#!/usr/bin/env python3
"""Small helper for the structured goal task board.

The parser intentionally supports only the narrow YAML subset used by
docs/goal/task-board.yaml so the workflow has no PyYAML dependency
(same choice as the pcc project this board is modelled on).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TASK_BOARD = ROOT / "docs" / "goal" / "task-board.yaml"
STATE_FILE = ROOT / "docs" / "current-goal-state.md"
CANONICAL_GOAL_PROTOCOL = "docs/goal/goal-prompt.md"

VALID_PRIORITIES = {"P0": 0, "P1": 1, "P2": 2, "P3": 3}
VALID_STATUSES = {
    "DISCOVERED",
    "TODO_READY",
    "TODO_NEEDS_DESIGN",
    "IN_PROGRESS",
    "TESTING",
    "DONE_WEAK",
    "DONE_STRONG",
    "BLOCKED",
    "CLAIM_RISK",
}

REQUIRED_TASK_FIELDS = {
    "milestone",
    "depends_on",
    "rank",
    "exit_criteria",
}

# Every `DONE_STRONG` row must name a file containing an adversarial revalidation note
# headed `## Adversarial revalidation: <task id>` (rule M0-ADVERSARIAL-AUDIT).
REVALIDATION_HEADING = "## Adversarial revalidation: {tid}"


def _parse_scalar(raw: str) -> Any:
    raw = raw.strip()
    if raw == "":
        return ""
    if raw in {"[]", "{}"}:
        return [] if raw == "[]" else {}
    if raw in {"true", "false"}:
        return raw == "true"
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return raw


def load_task_board(path: Path = TASK_BOARD) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(path)
    data: dict[str, Any] = {"tasks": []}
    current: dict[str, Any] | None = None
    current_list_key: str | None = None

    for line_no, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw_line.rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        indent = len(line) - len(line.lstrip(" "))

        if stripped.startswith("- id:"):
            current = {"id": _parse_scalar(stripped[len("- id:") :])}
            data["tasks"].append(current)
            current_list_key = None
            continue

        if current is not None and indent >= 4:
            if stripped.startswith("- "):
                if current_list_key is None:
                    raise ValueError(f"{path}:{line_no}: list item without list key")
                current[current_list_key].append(_parse_scalar(stripped[2:]))
                continue
            if ":" not in stripped:
                raise ValueError(f"{path}:{line_no}: expected key: value")
            key, value = stripped.split(":", 1)
            key = key.strip()
            value = value.strip()
            if value == "":
                current[key] = []
                current_list_key = key
            else:
                current[key] = _parse_scalar(value)
                current_list_key = None
            continue

        if ":" not in stripped:
            raise ValueError(f"{path}:{line_no}: expected top-level key: value")
        key, value = stripped.split(":", 1)
        key = key.strip()
        value = value.strip()
        if key == "tasks" and value == "":
            data["tasks"] = []
        else:
            data[key] = _parse_scalar(value)

    return data


def _walk_deps(task: dict[str, Any], board: dict[str, Any], errors: list[str]) -> None:
    """Detect dependency cycles via DFS on the id graph."""
    ids = {t["id"] for t in board["tasks"]}
    path: list[str] = []
    seen: set[str] = set()

    def dfs(tid: str) -> None:
        if tid in path:
            errors.append(f"dependency cycle: {' -> '.join(path + [tid])}")
            return
        if tid in seen:
            return
        path.append(tid)
        seen.add(tid)
        t = next((t for t in board["tasks"] if t["id"] == tid), None)
        if t is not None:
            for d in t.get("depends_on", []):
                dfs(d)
        path.pop()

    for tid in ids:
        dfs(tid)


def validate(board: dict[str, Any], root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    seen: set[str] = set()
    tasks = board.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        return ["task board has no tasks"]

    version = board.get("version", 1)
    milestone_order = board.get("milestone_order", [])
    active_milestone = board.get("active_milestone", "")
    milestone_indexes: dict[str, int] = {}
    if version >= 2:
        if board.get("source_protocol") != CANONICAL_GOAL_PROTOCOL:
            errors.append(
                f"version 2 board source_protocol must be {CANONICAL_GOAL_PROTOCOL}"
            )
        if not isinstance(milestone_order, list) or not milestone_order:
            errors.append("milestone_order must be a non-empty list")
        else:
            milestone_indexes = {m: i for i, m in enumerate(milestone_order)}
        if active_milestone not in milestone_indexes:
            errors.append(f"active_milestone {active_milestone!r} not in milestone_order")

    for task in tasks:
        tid = task.get("id")
        if not tid:
            errors.append("task without id")
            continue
        if tid in seen:
            errors.append(f"duplicate task id: {tid}")
        seen.add(tid)

        missing = REQUIRED_TASK_FIELDS - set(task)
        if missing:
            errors.append(f"{tid}: missing fields {sorted(missing)}")

        status = task.get("status", "")
        if status not in VALID_STATUSES:
            errors.append(f"{tid}: unknown status {status!r}")

        priority = task.get("priority", "")
        if priority not in VALID_PRIORITIES:
            errors.append(f"{tid}: unknown priority {priority!r}")

        milestone = task.get("milestone", "")
        if version >= 2 and milestone not in milestone_indexes:
            errors.append(f"{tid}: unknown milestone {milestone!r}")

        for dep in task.get("depends_on", []):
            if dep not in seen:
                # dependency may appear later in the file; check the full id set after
                continue
            dep_milestone = next(
                (t.get("milestone") for t in tasks if t.get("id") == dep), None
            )
            if (
                version >= 2
                and dep_milestone in milestone_indexes
                and milestone in milestone_indexes
                and milestone_indexes[dep_milestone] > milestone_indexes[milestone]
            ):
                errors.append(f"{tid}: depends on later-milestone task {dep}")

        if not isinstance(task.get("exit_criteria", []), list):
            errors.append(f"{tid}: exit_criteria must be a list")
        if not isinstance(task.get("required_gates", []), list):
            errors.append(f"{tid}: required_gates must be a list")

        reduction = task.get("open_conjecture_reduction", False)
        if reduction not in (True, False):
            errors.append(
                f"{tid}: open_conjecture_reduction must be true or false, got {reduction!r}"
            )
        if status == "DONE_STRONG":
            # M0-OPEN-REDUCTION-RULE: a reduction to an open conjecture never closes a row.
            if reduction is True:
                errors.append(
                    f"{tid}: DONE_STRONG is not allowed for a row whose content is a "
                    "reduction to an open conjecture (open_conjecture_reduction: true); "
                    "DONE_WEAK is the strongest available status"
                )
            if task.get("open_boundary", ""):
                errors.append(f"{tid}: DONE_STRONG requires an empty open_boundary")
            if not task.get("latest_evidence", ""):
                errors.append(f"{tid}: DONE_STRONG requires latest_evidence")
            # M0-ADVERSARIAL-AUDIT: a second, adversarial pass must be on record.
            note = task.get("revalidation", "")
            if not note:
                errors.append(
                    f"{tid}: DONE_STRONG requires a revalidation note "
                    "(field `revalidation:` naming the file with the adversarial pass)"
                )
            else:
                note_path = root / str(note)
                if not note_path.exists():
                    errors.append(f"{tid}: revalidation note {note} does not exist")
                elif REVALIDATION_HEADING.format(tid=tid) not in note_path.read_text(
                    encoding="utf-8"
                ):
                    errors.append(
                        f"{tid}: {note} has no section "
                        f"'{REVALIDATION_HEADING.format(tid=tid)}'"
                    )

    # unknown dependencies (checked after all ids are known)
    for task in tasks:
        for dep in task.get("depends_on", []):
            if dep not in seen:
                errors.append(f"{task.get('id')}: unknown dependency {dep!r}")

    _walk_deps(board, board, errors)

    return errors


def dependency_ready(task: dict[str, Any], board: dict[str, Any]) -> bool:
    by_id = {t["id"]: t for t in board["tasks"]}
    return all(
        dep in by_id and by_id[dep].get("status") == "DONE_STRONG"
        for dep in task.get("depends_on", [])
    )


def next_task(board: dict[str, Any]) -> dict[str, Any] | None:
    active = board.get("active_milestone", "")
    candidates = [
        t
        for t in board["tasks"]
        if t.get("milestone") == active
        and t.get("status") != "DONE_STRONG"
        and dependency_ready(t, board)
    ]
    if not candidates:
        return None
    candidates.sort(
        key=lambda t: (VALID_PRIORITIES.get(t.get("priority", "P3"), 99), t.get("rank", 0))
    )
    return candidates[0]


def render(board: dict[str, Any], root: Path = ROOT) -> str:
    tasks = board["tasks"]
    active = board.get("active_milestone", "")
    counts: dict[str, int] = {}
    for t in tasks:
        counts[t.get("status", "?")] = counts.get(t.get("status", "?"), 0) + 1
    next_t = next_task(board)
    by_id = {t["id"]: t for t in tasks}

    lines: list[str] = [
        "# Current goal state",
        "",
        "> Generated by `scripts/goal_state.py render`. Do not append work logs here;",
        "> update `docs/goal/task-board.yaml` or evidence files, then regenerate.",
        "",
        "## Authority and routing",
        "",
        "1. `AGENTS.md` owns repository safety and startup rules.",
        "2. `docs/goal/goal-prompt.md` owns the single execution and claim protocol.",
        "3. `docs/goal/task-board.yaml` is the only executable task queue.",
        "",
        "## Active milestone",
        "",
        f"- Milestone: `{active}`",
        f"- Tasks in milestone: `{len([t for t in tasks if t.get('milestone') == active])}`",
        f"- Tasks total: `{len(tasks)}`",
    ]
    for status in sorted(counts, key=lambda s: -counts[s]):
        lines.append(f"- `{status}`: `{counts[status]}`")

    if next_t:
        deps = ", ".join(
            f"`{d}` ({by_id[d].get('status')})" for d in next_t.get("depends_on", [])
        )
        lines += [
            f"- Next dependency-ready task: `{next_t['id']}`",
            f"- Next title: {next_t.get('title', '')}",
            f"- Next depends on: {deps or 'none'}",
            f"- Next open boundary: {next_t.get('open_boundary', '')}",
        ]
    else:
        lines.append("- Next dependency-ready task: none in the active milestone")

    lines += ["", "## Active task table", ""]
    lines.append("| Rank | ID | Priority | Status | Depends on |")
    lines.append("|---:|---|---|---|---|")
    for t in sorted(tasks, key=lambda t: (t.get("milestone", ""), t.get("rank", 0))):
        if t.get("status") == "DONE_STRONG":
            continue
        deps = ", ".join(f"`{d}`" for d in t.get("depends_on", []))
        lines.append(
            f"| {t.get('rank', '')} | `{t['id']}` | {t.get('priority', '')} | "
            f"`{t.get('status', '')}` | {deps} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="goal task board helper")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("validate", help="validate the task board")
    sub.add_parser("next", help="show the next dependency-ready task")
    sub.add_parser("render", help="write docs/current-goal-state.md")

    args = ap.parse_args()

    try:
        board = load_task_board()
    except Exception as exc:  # noqa: BLE001
        print(f"error loading task board: {exc}")
        return 1

    if args.cmd == "validate":
        errors = validate(board)
        if errors:
            print("validation failed:")
            for e in errors:
                print(f"  - {e}")
            return 1
        print(f"OK: {len(board['tasks'])} tasks validate")
        return 0

    if args.cmd == "next":
        nxt = next_task(board)
        if nxt is None:
            print("no dependency-ready task in the active milestone")
            return 0
        print(f"{nxt['id']} | {nxt.get('priority')} | {nxt.get('status')} | {nxt.get('title')}")
        if nxt.get("open_boundary"):
            print(f"  boundary: {nxt['open_boundary']}")
        return 0

    if args.cmd == "render":
        errors = validate(board)
        if errors:
            print("validation failed; not rendering:")
            for e in errors:
                print(f"  - {e}")
            return 1
        STATE_FILE.write_text(render(board), encoding="utf-8")
        print(f"wrote {STATE_FILE}")
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
