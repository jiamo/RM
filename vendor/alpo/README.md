# `vendor/alpo` — the alpo.ge Lean tree (a claimed proof of RH and GRH)

**Status: unverified.** Nothing in this repository depends on this directory. The tree has
been checked for provenance and statically scanned; it has **not** been compiled in full, so
its claim has not been checked by Lean. Task-board row: `M3-ALPO-VERIFICATION`.

## Where the code comes from

* **The announcement.** [`remark.pdf`](remark.pdf) (4 pages, SHA-256
  `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`). Its author writes
  that they found a proof of the Riemann hypothesis "working with Claude", that the method
  also gives the Generalized Riemann Hypothesis, and that the argument is fully formalized.
  It is published only as Lean, at the address in its footnote 1. The PDF does not name its
  author, so none is given here.
* **The code.** `https://alpo.ge/lean.tar.gz.part01` … `part14`, downloaded on 2026-11-20:
  14 parts, 239 MB, whose SHA-256 hashes are in [`SHA256SUMS`](SHA256SUMS). Joined, the parts
  are a gzip tar archive with one top-level directory, `lean/`. [`lean/`](lean) here is that
  directory, **byte-identical**: [`tools/provenance.sh`](tools/provenance.sh) downloads the
  parts again, checks them against `SHA256SUMS` and checks the tree with `diff -r`. Nothing
  in `lean/` was edited.
* **Licence.** The archive has no licence file. It is kept in this *private* repository for
  verification only and must not be redistributed.
* **Size.** 175,187 `.lean` files, 1.03 GB of source (about 9× Mathlib by bytes, 21× by
  file count). Lake package `tree`, sources in `lean/src`.
* **Pins.** Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, the
  official master commit "chore: bump toolchain to v4.33.1", one commit after the Mathlib this
  repository used before. On 2026-11-21 this repository moved to the same pins, so that the
  tree and our statements can be compiled together (see [`Bridge.lean`](Bridge.lean)). All
  other dependencies (batteries, aesop, Qq, …) are pinned to the same commits in both
  manifests. This repository has **not yet been rebuilt** under the new pins (owner's
  decision, 2026-11-21); the change is a Lean patch release, but until `lake build` and
  `./scripts/audit.sh` pass again it is unverified.

## What it claims

[`lean/src/Main.lean`](lean/src/Main.lean):

```lean
theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

* `RiemannHypothesis` is Mathlib's definition (`Mathlib.NumberTheory.LSeries.RiemannZeta`):
  every zero of `riemannZeta` other than the trivial zeroes `-2(n+1)` and `s = 1` has real
  part `1/2`. It is **exactly this repository's `ZetaForm`**
  (`abbrev ZetaForm : Prop := RiemannHypothesis`, in `RiemannHypothesis/Defs.lean`).
* The other four statements are defined in [`lean/src/Statements.lean`](lean/src/Statements.lean),
  which imports only Mathlib: RH again, and GRH for Dirichlet `L`-functions (no zero with
  `re s > 1/2`; every zero in the critical strip on the critical line, for all characters and
  for primitive ones). The Extended Riemann Hypothesis (Dedekind zeta functions) is **not**
  claimed.

## What has been checked (2026-11-20/21)

| check | result |
|---|---|
| provenance: 14 parts against `SHA256SUMS`, archive is plain files with no links and no `..` or absolute paths, `lean/` byte-identical (`tools/provenance.sh`) | passed |
| static scan of `lean/src` (`tools/scan.sh`): `axiom`, `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern`, `unsafe`, `opaque`, `skipKernelTC`, `ofReduceBool`, `trustCompiler`, `#eval`, `debug.` options | none found |
| metaprogramming present | 5 `run_cmd` lines that only add names to a library-suggestions deny list (`BuildAid/D1–D5.lean`); tactics `kexactB`/`kcopy` and command `cpt_copy_thms`, which build terms or declarations that the kernel then checks (`addDecl`); no `IO` actions |
| `Main` depends on every module | yes: the import closure of `Main` is all 175,187 modules, so nothing smaller can be checked |
| Mathlib `0df444a3` and Lean `v4.33.1` are official | yes (GitHub API) |
| sample compilation with `tools/build.py` | 6 random modules and an 8-module closure compiled; about 5 s per small module at one thread |
| `Verify.lean` logic, against Mathlib with a planted `sorry` | rejects it (non-zero exit) |
| `Bridge.lean`'s two cross-checks, against copies of the definitions | compile |
| full build, `Verify.lean`, `Bridge.lean`, kernel replay | **not done** |

## Cost, and a warning

* Estimated **290–460 core-hours** and about **57 GB** of `.olean` output (Mathlib's own
  ratio of build output to source). At 6 parallel jobs (half of a 12-core machine) that is
  **2–3 days**, possibly 4–5, because modules deep in the tree load more imports. A 64-core
  machine: roughly 5–8 hours.
* **Never run `lake build` in `lean/`.** Lake v4.33 has no `-j` option. On 2026-11-20 an
  unthrottled `lake build Main` filled the system-wide file table
  (`Too many open files in system`, `kern.maxfiles` = 491,520) within a minute, `launchd` died,
  and the macOS kernel panicked. Use [`tools/build.py`](tools/build.py): it compiles the
  modules itself in dependency order, with at most `--jobs` single-threaded `lean` processes
  (default: half the CPUs), under `nice`, and with a watchdog that kills everything if the
  file table passes 30% or free memory drops below 15%. It is resumable.
* `leanchecker` without `--fresh` replays every requested module in parallel inside one
  process; on this tree that could exhaust memory. Use `leanchecker --fresh Main` (one process
  that replays every declaration, Mathlib's included, into a fresh environment), and only on
  a machine with plenty of RAM.

## How to verify

```bash
bash vendor/alpo/tools/provenance.sh            # where the code comes from
bash vendor/alpo/tools/scan.sh                  # static scan
cd vendor/alpo/lean && lake exe cache get && cd -   # Mathlib's prebuilt oleans only
python3 -I vendor/alpo/tools/build.py --root vendor/alpo/lean --jobs 6   # days; resumable
(cd vendor/alpo/lean && lake env lean ../Verify.lean)   # statements and axioms
lake build RiemannHypothesis.Main && bash vendor/alpo/tools/bridge.sh   # against our statements
(cd vendor/alpo/lean && lake env leanchecker --fresh Main)   # kernel replay, large RAM
```

The [`alpo-verify`](../../.github/workflows/alpo-verify.yml) workflow runs the same steps,
by hand only: provenance and scan on a standard runner; the build and the checks only when the
repository variable `ALPO_RUNNER` names a runner large enough (self-hosted recommended).

What a pass would establish: Lean's kernel accepts proofs of the five statements using only
`propext`, `Classical.choice` and `Quot.sound`, and, by `Bridge.lean`, this repository
confirms them from its own side:

* `ZetaForm` (our statement of record) is the tree's `riemannHypothesis`, and `ZetaStripForm`
  and `EtaForm` follow through the equivalences proved here, independently of the tree.
* The tree's own `RiemannZetaZerosOnLine` is the same proposition as `ZetaForm` (`Iff.rfl`).
* A second route that does not use `riemannHypothesis`: the tree's GRH theorem, applied to
  the character mod 1 (whose `L`-function is `riemannZeta`), gives `ZetaStripForm` and
  `EtaForm` again. Two separately stated claims must agree on our statement.
* `EtaForm` is stated with an elementary alternating series, without analytic continuation,
  so the conclusion cannot rest on a degenerate definition of `riemannZeta` outside
  `re s > 1`.

What it would still rest on: the Lean kernel, and Mathlib's `DirichletCharacter.LFunction` for
the GRH part. An independent kernel (lean4lean, nanoda) would remove the first. The bridge
confirms *what* is proved; only the build and the kernel decide *whether* it is proved.

## Files

| path | what |
|---|---|
| `lean/` | the published tree, unmodified |
| `remark.pdf` | the announcement |
| `SHA256SUMS` | hashes of the 14 published parts |
| `Verify.lean` | checks the five theorems' types as raw kernel terms (no notation or macro in the tree can change them), fails on any axiom beyond the standard three, lists every axiom in the environment and where `RiemannHypothesis` is defined |
| `Bridge.lean` | the tree's theorems against `ZetaForm`, `ZetaStripForm`, `EtaForm`, by two independent routes (needs only 5 modules of this repository: `RiemannHypothesis.{Defs,Connected,Eta,Zeros,Main}`) |
| `tools/provenance.sh`, `tools/scan.sh`, `tools/build.py`, `tools/bridge.sh` | the checks above |
| `.gitignore` | ignores `lean/.lake` (Mathlib checkout, cache and build output) |
