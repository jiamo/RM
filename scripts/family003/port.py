#!/usr/bin/env python3
"""Mechanical stage of the native absorption of openai/math family 003.

Usage:
    python3 scripts/family003/port.py INTAKE_DIR ENTRY_MODULE [ENTRY_MODULE ...]
            [--dry-run] [--map docs/family003/source-to-native-map.tsv]

INTAKE_DIR is the directory restored by `restore_openai_rh_bundle.py` (it contains
`openai-math/` and `reference-dependencies/`).  For every module in the static import
closure of the ENTRY_MODULEs (upstream names, e.g. `OAI.NumberTheory.DirichletL.Nonvanishing`)
this script writes a native module under `RiemannHypothesis/Family003/`:

* module prefix  `OAI.`                    -> `RiemannHypothesis.Family003.`
* module prefix  `PrimeNumberTheoremAnd.`  -> `RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd.`
* module prefix  `RellichKondrachov.`      -> `RiemannHypothesis.Family003.External.RellichKondrachov.`
* namespace      `OAI`                     -> `RiemannHypothesis.Family003`
  (upstream uses the token `OAI` only in `namespace OAI` / `end OAI` and in imports;
  the script checks this and refuses to run otherwise).
* five Mathlib modules that exist only at the upstream Mathlib pin are re-pointed at
  their host-pin equivalents (table `MATHLIB_RENAMES`).

A provenance header is prepended to each file.  Existing upstream header comments
(copyright / authors / licence) are preserved verbatim below it.

Files that already exist in the destination are NOT overwritten if they carry
host-compatibility edits (header line `Host compatibility edits: yes`), so the script is
safe to re-run after manual adaptation.
"""
import os
import re
import sys

REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
PNT_REV = "c39a751132c88b6e8080b74c74023fd95b3d8be0"
RK_REV = "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
DEST_ROOT = "RiemannHypothesis/Family003"

PAPER_QRH = ("The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 "
             "(preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)")
PAPER_SIEGEL = ("Uniform exclusion of Landau-Siegel zeros "
                "(preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)")

MATHLIB_RENAMES = {
    "Mathlib.Basic.Real.Basic": "Mathlib.Data.Real.Basic",
    "Mathlib.Basic.NNReal.Basic": "Mathlib.Data.NNReal.Basic",
    "Mathlib.Basic.Complex.Basic": "Mathlib.Data.Complex.Basic",
    "Mathlib.Analysis.Asymptotics.Arith": "Mathlib.Analysis.Asymptotics.Lemmas",
    "Mathlib.Analysis.Asymptotics.Ring": "Mathlib.Analysis.Asymptotics.Lemmas",
    # Added to Mathlib after the host pin; its content (the Borel structure on `Circle`)
    # is supplied natively by `RiemannHypothesis.Family003.Compat.CircleMeasurable`.
    "Mathlib.MeasureTheory.Group.Circle": "RiemannHypothesis.Family003.Compat.CircleMeasurable",
}

# Third-party modules that this repository already vendors in mathematically identical form
# (vendor/zeta23 ports of the same PrimeNumberTheoremAnd files, with the same declarations);
# they are reused instead of being duplicated, which would also clash in the root import.
REUSED = {
    "PrimeNumberTheoremAnd.Fourier": "Zeta23.FromPNTPlus.Fourier",
    "PrimeNumberTheoremAnd.SmoothExistence": "Zeta23.FromPNTPlus.SmoothExistence",
    "PrimeNumberTheoremAnd.Sobolev": "Zeta23.FromPNTPlus.Sobolev",
}

IMPORT_RE = re.compile(r"^(\s*import\s+)(\S+)(.*)$")


def native_module(m):
    if m in REUSED:
        return REUSED[m]
    if m.startswith("OAI."):
        return "RiemannHypothesis.Family003." + m[len("OAI."):]
    if m.startswith("PrimeNumberTheoremAnd."):
        return "RiemannHypothesis.Family003.External." + m
    if m.startswith("RellichKondrachov."):
        return "RiemannHypothesis.Family003.External." + m
    return MATHLIB_RENAMES.get(m, m)


class Intake:
    def __init__(self, root):
        self.root = root
        self.oai = os.path.join(root, "openai-math", "lean")
        self.refs = os.path.join(root, "reference-dependencies")

    def source(self, m):
        """(absolute path, repository-relative original path, origin) or None."""
        rel = m.replace(".", "/") + ".lean"
        p = os.path.join(self.oai, rel)
        if m.startswith("OAI.") and os.path.exists(p):
            return p, "lean/" + rel, "oai"
        if m.startswith("PrimeNumberTheoremAnd."):
            p = os.path.join(self.refs, "PrimeNumberTheoremAnd", rel)
            if os.path.exists(p):
                return p, rel, "pnt"
        if m.startswith("RellichKondrachov."):
            p = os.path.join(self.refs, "rellich-kondrachov", rel)
            if os.path.exists(p):
                return p, rel, "rk"
        return None

    def closure(self, entries):
        seen = {}
        stack = list(entries)
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            src = self.source(m)
            if src is None:
                continue
            seen[m] = src
            for line in open(src[0], encoding="utf-8"):
                mm = IMPORT_RE.match(line)
                if mm:
                    stack.append(mm.group(2))
        return seen


def header(m, orig, origin, papers):
    paper_lines = "\n".join(f"  Paper: {p}" for p in papers)
    if origin == "oai":
        return f"""/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: {orig}
  Original module: {m}
  Source revision: {REV}
{paper_lines}
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
"""
    if origin == "pnt":
        return f"""/-
Native absorption (via openai/math family 003) of third-party material.
  Original repository: github.com/AlexKontorovich/PrimeNumberTheoremAnd
  Original author(s): Alex Kontorovich and contributors
  Original path: {orig}  (module {m})
  Fixed revision: {PNT_REV}, with the openai/math compatibility patch
    lean/patches/PrimeNumberTheoremAnd-lean4341.patch already applied (applied once, upstream).
  Required by: github.com/openai/math, family 003, source revision {REV}
{paper_lines}
  Licence: Apache License 2.0 (see LICENSES/PrimeNumberTheoremAnd-LICENSE and NOTICE).
  Proof status: ADAPTED (upstream Lean proof; module prefix PrimeNumberTheoremAnd ->
  RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd; declaration names unchanged).
  Host compatibility edits: none.
-/
"""
    if origin == "rk":
        return f"""/-
Native absorption (via openai/math family 003) of third-party material.
  Original repository: github.com/abenenson/rellich-kondrachov
  Original author(s): Adam Benenson
  Original path: {orig}  (module {m})
  Fixed revision: {RK_REV}, with the openai/math compatibility patch
    lean/patches/rellich-kondrachov-lean4341.patch already applied (applied once, upstream).
  Required by: github.com/openai/math, family 003, source revision {REV}
{paper_lines}
  Licence: Apache License 2.0 (see LICENSES/rellich-kondrachov-LICENSE and NOTICE).
  Proof status: ADAPTED (upstream Lean proof; module prefix RellichKondrachov ->
  RiemannHypothesis.Family003.External.RellichKondrachov; declaration names unchanged).
  Host compatibility edits: none.
-/
"""
    raise ValueError(origin)


def transform(text, origin):
    out = []
    for line in text.splitlines(keepends=True):
        mm = IMPORT_RE.match(line)
        if mm:
            out.append(mm.group(1) + native_module(mm.group(2)) + mm.group(3) + "\n")
            continue
        out.append(line)
    text = "".join(out)
    if origin == "oai":
        text = re.sub(r"^namespace OAI\b", "namespace RiemannHypothesis.Family003", text, flags=re.M)
        text = re.sub(r"^end OAI\b", "end RiemannHypothesis.Family003", text, flags=re.M)
        # fully qualified root references (`_root_.OAI.SiegelZeros.…`, Siegel-zero closure)
        text = re.sub(r"\b_root_\.OAI\.", "_root_.RiemannHypothesis.Family003.", text)
        # safety check: no other occurrence of the token
        rest = [l for l in text.splitlines() if re.search(r"\bOAI\b", l)]
        if rest:
            raise SystemExit(f"unexpected OAI token: {rest[:3]}")
    return text


def main():
    argv = sys.argv[1:]
    mp = None
    if "--map" in argv:
        i = argv.index("--map")
        mp = argv[i + 1]
        del argv[i:i + 2]
    args = [a for a in argv if not a.startswith("--")]
    dry = "--dry-run" in argv
    intake = Intake(args[0])
    entries = args[1:]
    clo = intake.closure(entries)
    # paper attribution: Siegel-only files get the Siegel paper, the rest the QRH paper;
    # files in both closures get both.
    siegel = intake.closure(["OAI.NumberTheory.SiegelZeros.Main"])
    qrh = intake.closure(["OAI.NumberTheory.DirichletL.Hecke.Nonvanishing",
                          "OAI.NumberTheory.DirichletL.Nonvanishing"])
    rows = []
    written = skipped = 0
    for m, (path, orig, origin) in sorted(clo.items()):
        papers = []
        if m in qrh:
            papers.append(PAPER_QRH)
        if m in siegel:
            papers.append(PAPER_SIEGEL)
        nm = native_module(m)
        if m in REUSED:
            rows.append((m, orig, nm, "vendor/zeta23/" + nm.replace(".", "/") + ".lean (reused)"))
            continue
        dest = nm.replace(".", "/") + ".lean"
        rows.append((m, orig, nm, dest))
        if dry:
            continue
        if os.path.exists(dest) and "Host compatibility edits: yes" in open(dest, encoding="utf-8").read(4000):
            skipped += 1
            continue
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        text = open(path, encoding="utf-8").read()
        with open(dest, "w", encoding="utf-8") as f:
            f.write(header(m, orig, origin, papers) + transform(text, origin))
        written += 1
    print(f"{len(clo)} modules in closure; written {written}, kept (host-edited) {skipped}")
    if mp:
        os.makedirs(os.path.dirname(mp), exist_ok=True)
        with open(mp, "w", encoding="utf-8") as f:
            f.write("upstream_module\tupstream_path\tnative_module\tnative_path\n")
            for r in rows:
                f.write("\t".join(r) + "\n")


if __name__ == "__main__":
    main()
