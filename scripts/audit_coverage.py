#!/usr/bin/env python3
"""Axiom-audit coverage report.

Compares

  * the set of theorems the `RiemannHypothesis` library exports
    (produced by `lake env lean scripts/list_theorems.lean`), with
  * the set of names checked by a `#print axioms` line in `scripts/audit.sh`,

and prints the difference in both directions:

  * MISSING  — exported theorems with no axiom check (the blind spot);
  * STALE    — names checked by `audit.sh` that the library no longer exports
               (typo, renamed or deleted theorem: the check silently passes on
               nothing, since `#print axioms` of an unknown name is an error —
               so these are hard failures of the audit and are reported as such).

Usage:

    lake env lean scripts/list_theorems.lean > /tmp/theorems.txt
    python3 scripts/audit_coverage.py /tmp/theorems.txt [--summary] [--by-module]

Exit status is 1 if there are STALE names, else 0; MISSING names are reported but
do not fail the run, since full coverage is a goal rather than an invariant.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def audited_names() -> set[str]:
    text = (ROOT / "scripts" / "audit.sh").read_text()
    return set(re.findall(r"^#print axioms (\S+)\s*$", text, re.M))


def exported_names(path: Path) -> set[str]:
    return {line.strip() for line in path.read_text().splitlines() if line.strip()}


def module_of(name: str, index: dict[str, str]) -> str:
    return index.get(name, "?")


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    if not args:
        print(__doc__)
        return 2
    exported = exported_names(Path(args[0]))
    audited = audited_names()

    missing = sorted(exported - audited)
    stale = sorted(audited - exported)

    print(f"exported theorems : {len(exported)}")
    print(f"audited names     : {len(audited)}")
    print(f"covered           : {len(exported & audited)}"
          f" ({100.0 * len(exported & audited) / max(len(exported), 1):.1f}%)")
    print(f"missing coverage  : {len(missing)}")
    print(f"stale audit lines : {len(stale)}")

    if stale:
        print("\n== STALE (audited but not exported) ==")
        for n in stale:
            print(n)

    if "--summary" not in flags:
        print("\n== MISSING (exported but not audited) ==")
        for n in missing:
            print(n)

    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
