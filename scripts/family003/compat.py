#!/usr/bin/env python3
"""Record host-compatibility edits in absorbed family-003 modules.

    python3 scripts/family003/compat.py mark FILE "reason"
    python3 scripts/family003/compat.py add-import FILE MODULE "reason"
    python3 scripts/family003/compat.py add-import-where REGEX MODULE "reason"

`mark` turns the header line `Host compatibility edits: none.` into
`Host compatibility edits: yes.` followed by an indented bullet with the reason (further
reasons are appended as further bullets).  The exact diff against the upstream file is
always recoverable with `git log -p` from the mechanical-port commit, or by re-running
`scripts/family003/port.py` into a scratch tree.
"""
import os
import re
import sys

MARK_NONE = "  Host compatibility edits: none.\n"
MARK_YES = "  Host compatibility edits: yes.\n"


def mark(path, reason):
    text = open(path, encoding="utf-8").read()
    bullet = f"    - {reason}\n"
    if MARK_NONE in text:
        text = text.replace(MARK_NONE, MARK_YES + bullet, 1)
    elif MARK_YES in text:
        i = text.index(MARK_YES) + len(MARK_YES)
        # skip existing bullets
        while text.startswith("    - ", i):
            i = text.index("\n", i) + 1
        if bullet not in text:
            text = text[:i] + bullet + text[i:]
    else:
        raise SystemExit(f"{path}: no provenance header")
    open(path, "w", encoding="utf-8").write(text)


def add_import(path, module, reason):
    lines = open(path, encoding="utf-8").read().splitlines(keepends=True)
    if any(l.strip() == f"import {module}" for l in lines):
        return False
    last = max(i for i, l in enumerate(lines) if re.match(r"\s*import\s", l))
    lines.insert(last + 1, f"import {module}\n")
    open(path, "w", encoding="utf-8").write("".join(lines))
    mark(path, reason)
    return True


def main():
    cmd = sys.argv[1]
    if cmd == "mark":
        mark(sys.argv[2], sys.argv[3])
    elif cmd == "add-import":
        add_import(sys.argv[2], sys.argv[3], sys.argv[4])
    elif cmd == "add-import-where":
        rx = re.compile(sys.argv[2])
        n = 0
        for root, _, files in os.walk("RiemannHypothesis/Family003"):
            for f in files:
                p = os.path.join(root, f)
                if not f.endswith(".lean") or "/Compat/" in p:
                    continue
                if rx.search(open(p, encoding="utf-8").read()):
                    n += add_import(p, sys.argv[3], sys.argv[4])
        print(f"added import to {n} files")
    else:
        raise SystemExit(cmd)


if __name__ == "__main__":
    main()
