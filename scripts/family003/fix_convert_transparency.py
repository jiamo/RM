#!/usr/bin/env python3
"""Host-compatibility tweak for absorbed family-003 modules (see compat.py).

Lean v4.34 (the upstream toolchain) makes instances reducible (`instance_reducible`), so the
reducible-transparency `rfl` that `convert` uses to close side goals also closes
instance-equality goals such as `Real.instLE = instPreorder.toLE`.  On the host toolchain
(Lean v4.33.0) those goals survive and break the following tactic.  The faithful emulation is
to run `convert` with `preTransparency := .instances`.  This script rewrites every `convert`
(and `convert!`) that has no explicit configuration into
`convert (preTransparency := .instances)`, in the files given on the command line, and records
the edit in each touched file's provenance header.
"""
import re
import sys
sys.path.insert(0, "scripts/family003")
from compat import mark

REASON = ("tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the "
          "upstream Lean v4.34 reducibility of instances")
PAT = re.compile(r"(?<![\w.'])(convert|convert_to)(!?)(\s+)(?!\(\s*\w+\s*:=)")

for p in sys.argv[1:]:
    text = open(p, encoding="utf-8").read()
    head, sep, body = text.partition("\n-/\n")  # keep the provenance header untouched
    new_body, n = PAT.subn(lambda m: f"{m.group(1)}{m.group(2)} (preTransparency := .instances){m.group(3)}", body)
    if n:
        open(p, "w", encoding="utf-8").write(head + sep + new_body)
        mark(p, REASON)
        print(n, p)
