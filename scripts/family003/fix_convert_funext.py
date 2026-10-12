#!/usr/bin/env python3
"""Host-compatibility tweak for absorbed family-003 modules (see compat.py).

At the host Mathlib pin some instance paths (e.g. the `AddCommMonoid ℂ` instance used by
`HasSum`) are not reducibly defeq to the ones `convert` meets, so `convert h using k` leaves an
extra instance-equality goal that upstream `convert` closed itself.  For every line
`convert ... using k` immediately followed (same indentation) by `funext`/`ext`, insert
`all_goals try with_reducible_and_instances rfl`.  Only files given on the command line are
touched; each touched file is recorded in its provenance header.
"""
import re
import sys
sys.path.insert(0, "scripts/family003")
from compat import mark

REASON = ("proof tweak: after convert, close residual instance-equality goals with "
          "'with_reducible_and_instances rfl' (host instances are not reducibly defeq)")

for p in sys.argv[1:]:
    L = open(p, encoding="utf-8").read().split("\n")
    out = []
    changed = False
    for i, line in enumerate(L):
        out.append(line)
        m = re.match(r"^(\s*)convert .* using \d+\s*$", line)
        if m and i + 1 < len(L) and re.match("^" + m.group(1) + r"(funext|ext)\b", L[i + 1]):
            out.append(m.group(1) + "all_goals try with_reducible_and_instances rfl")
            changed = True
    if changed:
        open(p, "w", encoding="utf-8").write("\n".join(out))
        mark(p, REASON)
        print("fixed", p)
