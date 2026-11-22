# `vendor/alpo` — the alpo.ge Lean tree (a claimed proof of RH and GRH)

**Status (2026-11-22).** Nothing in this repository depends on this directory.

* **Verified independently by others.** As reported below, the whole tree has been compiled
  and checked by several independent kernels. The archive vendored here is byte-for-byte the
  one they checked.
* **Checked here in part.** Provenance and a static scan passed. The *analytic half* of the
  proof is compiled in full, here and in CI, and connected to this repository's statements
  ([`AnalyticBridge.lean`](AnalyticBridge.lean)). Combined with a zero of `ζ` proved in this
  repository, the same analytic theorem also gives an unconditional oscillation theorem.
* **Not run here.** The full build of all 175,187 modules, [`Verify.lean`](Verify.lean) and
  [`Bridge.lean`](Bridge.lean).

Task-board row: `M3-ALPO-VERIFICATION`.

## Where the code comes from

* **The announcement.** [`remark.pdf`](remark.pdf) (4 pages, SHA-256
  `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`). Its author writes
  that they found a proof of the Riemann hypothesis "working with Claude", that the method
  also gives the Generalized Riemann Hypothesis, and that the argument is fully formalized in
  Lean, at the address in its footnote 1.
* **The exposition.** [`riemann_hypothesis.pdf`](riemann_hypothesis.pdf) (55 pages, *Dirichlet
  L-functions and the critical line*, SHA-256
  `419e24a4ba07eb9ce98524ad11f568f2bd87d8d70abe288e4ef37632bdd8bb85`). Its reference [1]
  names the development "L. Alpöge, with Claude".
  * It proves the analytic, linear-algebraic and numerical steps in full (Sections 2, 5, 10
    and 11).
  * It states the deep geometric and cohomological inputs with links to their Lean files
    (Sections 3, 4 and 6–9).
  * It ends with a concordance between the mathematics and the Lean source.
* **The code.** `https://alpo.ge/lean.tar.gz.part01` … `part14`, downloaded on 2026-11-20 and
  again on 2026-11-22.
  * 14 parts, whose SHA-256 hashes are in [`SHA256SUMS`](SHA256SUMS). Joined, they are
    239,275,554 bytes with SHA-256
    `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. This is exactly the
    archive in the independent verification below.
  * The joined parts are a gzip tar archive with one top-level directory, `lean/`. [`lean/`](lean)
    here is that directory, **byte-identical**: [`tools/provenance.sh`](tools/provenance.sh)
    downloads the parts again, checks them, and compares the tree with `diff -r`. Nothing in
    `lean/` was edited.
  * Public mirrors exist (`CocoSgt/riemann-hypothesis-lean`, `Deicyde/riemann-hypothesis`).
* **Licence.** The archive has no licence file. It is kept in this *private* repository for
  verification only and must not be redistributed.
* **Size.** 175,187 `.lean` files, 1.03 GB of source (about 9× Mathlib by bytes, 21× by
  file count). Lake package `tree`, sources in `lean/src`.
* **Pins.** Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, the
  official commit "chore: bump toolchain to v4.33.1". It is one commit after the Mathlib this
  repository used before.
  * On 2026-11-21 this repository moved to the same pins, so that the tree and our statements
    can be compiled together. Every other dependency is pinned to the same commit in both
    manifests.
  * Under the new pins, `tools/analytic.sh` compiles the 23 of our modules that
    `AnalyticBridge.lean` imports (`tools/repo_closure.py` lists them; they import only
    Mathlib). The rest of the repository has
    **not yet been rebuilt**; until `lake build` and `./scripts/audit.sh` pass again, it is
    unverified under these pins.

## What it claims

[`lean/src/Main.lean`](lean/src/Main.lean):

```lean
theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

* `RiemannHypothesis` is Mathlib's definition, in `Mathlib.NumberTheory.LSeries.RiemannZeta`:
  every zero of `riemannZeta` other than the trivial zeroes `-2(n+1)` and `s = 1` has real
  part `1/2`. It is **exactly this repository's `ZetaForm`**
  (`abbrev ZetaForm : Prop := RiemannHypothesis`, in `RiemannHypothesis/Defs.lean`).
* The other four statements are defined in
  [`lean/src/Statements.lean`](lean/src/Statements.lean), which imports only Mathlib.
  * One is RH again.
  * Three are GRH for Dirichlet `L`-functions: no zero with `re s > 1/2`, and every zero in the
    critical strip on the critical line, for all characters and for primitive ones.
  * The Extended Riemann Hypothesis (Dedekind zeta functions) is **not** claimed.

## How the proof is organized

The exposition and the source agree on two halves.

1. **Analytic half.** It is classical in spirit (Landau 1905) but formulated for windows.
   * Take a finite family of Dirichlet characters with positive weights.
   * Suppose the weighted smoothed prime sum `G(y) = Σ a_χ Re G_χ(y)` is at most `C·y^θ` on
     windows `[Y, Y^{1+δ}]` that go arbitrarily far out. Only an upper bound is needed.
   * Then no member has a zero with `re s > θ`.

   For `ζ`, `G₁(y) = Σ_{n≤y} Λ(n)(y/n − 1)₊ − y log y + (1+γ)y`. In Lean this is
   `Deduction.zeroFree_of_rpow_window`: 31 modules that import only Mathlib.
2. **Arithmetic half.** It proves the bound `H_ψ(y) ≤ y^{1/2+9ε}` on windows `[Y, Y^{3/2}]`.
   Here `H_ψ = G₁ + (3o+1)⁻¹ Σ_j Re G_{ψ^j}` (paper, (1.3)), built from:
   * finite-place divisibility along a theta tower of length about `√x`, a Stepanov-type
     multiplicity;
   * archimedean norms and periods;
   * a slope transfer through approximate tight frames;
   * Galois representations, with Selmer-group bounds on a common window.

   This is the other ~175,000 modules.

## What has been checked

### Here (2026-11-20 to 22)

| check | result |
|---|---|
| provenance: 14 parts against `SHA256SUMS`, archive is plain files with no links and no `..` or absolute paths, `lean/` byte-identical (`tools/provenance.sh`) | passed (locally and in CI) |
| joined archive equals the one independently verified (SHA-256 `9631b4f0…`, 239,275,554 bytes) | passed |
| static scan of `lean/src` (`tools/scan.sh`): `axiom`, `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern`, `unsafe`, `opaque`, `skipKernelTC`, `ofReduceBool`, `trustCompiler`, `#eval`, `debug.` options | none found |
| metaprogramming present | 5 `run_cmd` lines that only add names to a library-suggestions deny list (`BuildAid/D1–D5.lean`). Tactics `kexactB` and `kcopy` and command `cpt_copy_thms` build terms or declarations that the kernel then checks (`addDecl`). No `IO` actions |
| `Main` depends on every module | yes: the import closure of `Main` is all 175,187 modules |
| Mathlib `0df444a3` and Lean `v4.33.1` are official | yes (GitHub API) |
| **analytic half compiled in full** (`tools/analytic.sh`, also the CI job `analytic`): the 31 tree modules, the 23 of our modules it imports, and `AnalyticBridge.lean` | passed; every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` |
| `Verify.lean` logic, against Mathlib with a planted `sorry` | rejects it (non-zero exit) |
| full build, `Verify.lean`, `Bridge.lean`, kernel replay | not run here (see below) |

### Independently, as reported

Andrew Sutherland (MIT), "Verification files for the Lean proof of the Riemann Hypothesis",
<https://math.mit.edu/~drew/grh/>, page as of 2026-11-22 04:35 UTC, read on 2026-11-22. It
reports:

* All 175,187 modules compile.
* `#print axioms` of the five theorems shows only the three standard axioms, and no axiom is
  declared outside Lean core.
* `leanchecker` replays every module, and `lean4lean` accepts every module (five after raising
  its step limit).
* The independent kernels **nanoda** and **con-leche**, and its Rust port con-ron, accept the
  full 61.6 GB export.
* con-leche's and con-ron's `--compare` modes confirm the five statements against a challenge
  file that imports only Mathlib.
* A sandboxed `lake build Main` on a separate machine reproduces the export byte for byte.

At that time, the Lean default and paranoid kernels on the export and the full
`lake comparator` run were still in progress. These are other people's checks; this
repository has not reproduced them.

## What a pass establishes, and what it rests on

**Via `AnalyticBridge.lean` (compiled here and in CI).** Let `WindowBound` be the one-sided
window bound for `G₁`, stated with Mathlib notions only.

* It implies `ZetaForm`, `ZetaStripForm` and `EtaForm`. The first step uses the tree's
  analytic theorems; the other two use this repository's own equivalences.
* So for `ζ`, all a reader must trust about the 175,000-module arithmetic half is the single
  statement `WindowBound`.
* `WindowBound` is equivalent to RH (the four hygiene answers are in the file's docstring). It
  is an interface, not progress towards RH.
* Run backwards, the same analytic theorem is unconditional. `ζ` has a zero with `re ρ ≥ 1/2`
  (`RiemannHypothesis.exists_riemannZeta_eq_zero_of_mem_strip`, reflected by `s ↦ 1 − s`).
  Therefore, for `0 < θ < 1/2`, every window `[Y, Y^{1+δ}]` far enough out contains a point
  with `G₁(y) > C y^θ` (`exists_gt_rpow_mem_window`). In particular `G₁(y) = Ω₊(y^θ)`
  (`frequently_gt_rpow`), and the window bound of `WindowBound` is false for every `θ < 1/2`
  (`not_windowBound_of_lt_half`): the exponent `1/2` is sharp. Nothing from the arithmetic
  half is used. The classical theorem (E. Schmidt, 1903: `ψ(x) − x = Ω±(x^{1/2})`) is
  stronger; this version is one-sided, for the smoothed sum, and localized to windows.

**Via `Bridge.lean` (needs the full build).**

* `ZetaForm` is the tree's `riemannHypothesis`. `ZetaStripForm` and `EtaForm` follow through
  equivalences proved here, independently of the tree.
* The tree's own `RiemannZetaZerosOnLine` is the same proposition as `ZetaForm` (`Iff.rfl`).
* There is a second route that does not use `riemannHypothesis`: the tree's GRH theorem,
  applied to the character mod 1 (whose `L`-function is `riemannZeta`), gives `ZetaStripForm`
  and `EtaForm` again.
* `EtaForm` uses an elementary alternating series, so the conclusion cannot rest on a
  degenerate definition of `riemannZeta` outside `re s > 1`.

**What it still rests on.** The kernels, and Mathlib's definitions of `riemannZeta` and
`DirichletCharacter.LFunction` (the latter for the GRH part). The independent kernels reported
above address the first.

## Cost, and a warning

* **Full build.** Measured from sample compilations: about **240–360 core-hours** and
  **60–80 GB** of build output (78.6× the source size). Given the independent verification,
  there is no need to repeat it on a workstation.
* **Never run `lake build` in `lean/`.** Lake v4.33 has no `-j` option. On 2026-11-20 an
  unthrottled `lake build Main` filled the system-wide file table
  (`Too many open files in system`, `kern.maxfiles` = 491,520) within a minute; `launchd` died
  and the macOS kernel panicked.
* **Use [`tools/build.py`](tools/build.py) instead.** It compiles modules itself, in dependency
  order.
  * It runs at most `--jobs` single-threaded `lean` processes, under `nice`.
  * A watchdog kills everything if the file table passes 30% or free memory drops below 15%.
  * It is resumable.
  * Since 2026-11-22 it passes `-R src`, so that module names match Lake's. Before that, a
    module was compiled as `src.<Module>`, which breaks private names and `open private`.
* `leanchecker` without `--fresh` replays every requested module in parallel inside one
  process, which could exhaust memory on this tree. Use `leanchecker --fresh Main`, and only
  on a machine with plenty of RAM.

## How to verify

```bash
bash vendor/alpo/tools/provenance.sh            # where the code comes from
bash vendor/alpo/tools/scan.sh                  # static scan
cd vendor/alpo/lean && lake exe cache get && cd -   # Mathlib's prebuilt oleans only
bash vendor/alpo/tools/analytic.sh              # analytic half + AnalyticBridge (minutes)
# full build and the checks that need it (days; see "Cost"):
python3 -I vendor/alpo/tools/build.py --root vendor/alpo/lean --jobs 6
(cd vendor/alpo/lean && lake env lean ../Verify.lean)   # statements and axioms
lake build RiemannHypothesis.Main && bash vendor/alpo/tools/bridge.sh   # against our statements
(cd vendor/alpo/lean && lake env leanchecker --fresh Main)   # kernel replay, large RAM
```

There is also a fastest independent check that needs no build. Download the export from the
MIT page (7.7 GB compressed, 61.6 GB unpacked) and run `con-leche --compare`; this needs about
50 GB of RAM.

The [`alpo-verify`](../../.github/workflows/alpo-verify.yml) workflow is started by hand only.

* On standard runners it runs provenance, the scan, and the analytic half.
* It runs the full build and the checks that need it only when the repository variable
  `ALPO_RUNNER` names a large enough runner.

## Files

| path | what |
|---|---|
| `lean/` | the published tree, unmodified |
| `remark.pdf` | the announcement |
| `riemann_hypothesis.pdf` | the 55-page exposition, with the Lean concordance |
| `SHA256SUMS` | hashes of the 14 published parts |
| `AnalyticBridge.lean` | `WindowBound → ZetaForm, ZetaStripForm, EtaForm` through the tree's analytic half, and the unconditional oscillation theorems (the exponent `1/2` is sharp); compiled by `tools/analytic.sh` |
| `Verify.lean` | checks the five theorems' types as raw kernel terms, so no notation or macro in the tree can change them. Fails on any axiom beyond the standard three. Lists every axiom in the environment and where `RiemannHypothesis` is defined |
| `Bridge.lean` | the tree's theorems against `ZetaForm`, `ZetaStripForm` and `EtaForm`, by two independent routes. Needs the full build |
| `tools/provenance.sh`, `tools/scan.sh`, `tools/build.py`, `tools/analytic.sh`, `tools/repo_closure.py`, `tools/bridge.sh` | the checks above |
| `.gitignore` | ignores `lean/.lake` (Mathlib checkout, cache and build output) |
