#!/usr/bin/env python3
"""Print, one per line and in dependency order, the modules of this repository's
RiemannHypothesis library that a Lean file imports, directly or transitively.

Reads import headers only and compiles nothing.  Imports from outside this repository (Mathlib,
the alpo.ge tree) are skipped, since analytic.sh takes them from the tree's LEAN_PATH.  An
import of this repository's other libraries (Zeta23, Challenge, Solution) is an error, because
analytic.sh does not compile them.

Usage: repo_closure.py REPO FILE.lean
"""
import os
import sys

LOCAL = "RiemannHypothesis"
UNSUPPORTED = ("Zeta23", "Challenge", "Solution")
MODIFIERS = ("public", "meta")


def strip_comments(text):
    """Remove Lean comments: nested block comments and line comments."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def header_imports(path):
    """The module names imported by the header of a Lean file."""
    with open(path, encoding="utf-8") as f:
        toks = strip_comments(f.read()).split()
    i, out = 0, []
    for kw in ("module", "prelude"):
        if i < len(toks) and toks[i] == kw:
            i += 1
    while i < len(toks):
        j = i
        while j < len(toks) and toks[j] in MODIFIERS:
            j += 1
        if j >= len(toks) or toks[j] != "import":
            break
        j += 1
        if j < len(toks) and toks[j] == "all":
            j += 1
        if j >= len(toks):
            sys.exit(f"{path}: import without a module name")
        out.append(toks[j])
        i = j + 1
    return out


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    repo, file = sys.argv[1], sys.argv[2]
    order, seen, stack = [], set(), []

    def visit(m):
        if m in seen:
            return
        top = m.split(".")[0]
        if top in UNSUPPORTED:
            sys.exit(f"{m}: library {top} is not compiled by analytic.sh")
        if top != LOCAL:
            return
        if m in stack:
            sys.exit(f"import cycle through {m}")
        path = os.path.join(repo, *m.split(".")) + ".lean"
        if not os.path.isfile(path):
            sys.exit(f"{m}: no file {path}")
        stack.append(m)
        for d in header_imports(path):
            visit(d)
        stack.pop()
        seen.add(m)
        order.append(m)

    sys.setrecursionlimit(10000)
    for m in header_imports(file):
        visit(m)
    print("\n".join(order))


if __name__ == "__main__":
    main()
