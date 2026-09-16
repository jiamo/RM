# Proposed mathlib contribution — Kusmin–Landau and van der Corput exponential-sum estimates

## What this is

A **submission-ready extraction** of the exponential-sum machinery from the
`riemann_hypothesis_formalization` repository (Lean 4 / mathlib4, snapshot 2026-09-16,
pinned to mathlib4 `v4.28.0`) into the directory layout that mathlib expects:
`Mathlib/NumberTheory/ExponentialSums/`.

The five requested items are all here:

| requested item | file | content |
|---|---|---|
| `KusminLandau` | `KusminLandau.lean` | Discrete first-derivative test: if the successive differences `u(i+1)-u(i)` are monotone and stay in `[λ, 1−λ]`, then `‖∑_{j≤K} e(u(c+j))‖ ≤ 1 + 2/λ` — **no dependence on the length of the range**. |
| `KusminLandauGeneral` | `KusminLandauGeneral.lean` | The general monotone case: `‖∑_{j≤K} e(f(c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1)(1 + 2/λ)`, and the classical variation form `≤ (V + 2)(1 + 2/λ)` where `V = |f'(c+K) − f'(c)|`. |
| `VanDerCorput` | `VanDerCorput.lean` | Integral versions of the first-derivative test (`‖∫_a^b e^{iF}‖ ≤ 4/m`) and the **second-derivative test** (`VDCSecondDerivative`: `‖∫_a^b e^{iF}‖ ≤ 12/√r` when `|F''| ≥ r`), plus the logarithmic-phase corollaries. |
| `VDCThirdDerivative` | `VanDerCorputThird.lean` (+ companions) | Third-derivative test for *sums*: if `|F'''| ≥ H` then `‖∑_{N<n≤N'} e(F(n))‖ ≪ N^θ H^{−1/…}` — the exponent-pair `(1/6, 2/3)` step, proven via the A-process/Weyl differencing below. |

Three further files are included because `VDCThirdDerivative` literally depends on them (they would not
typecheck otherwise); they are equally extractable mathlib content in their own right:

| companion | role |
|---|---|
| `WeylDifferencing.lean` | The A-process: Cauchy–Schwarz differencing reduces an exponential sum to one whose phase has lower degree. |
| `WeylQuadratic.lean` | The quadratic case of the differenced sum, using the nearest-integer distance bound `|θ − round θ| ≤ 1/2` and the Kusmin–Landau test. |
| `VanDerCorputSums.lean` | The second-derivative test for *sums* (sampling into blocks on which `⌊F'⌋` is constant). |
| `SqrtHarmonic.lean` | The elementary estimate `∑_{1≤k≤n} 1/√k ≤ 2√n`. |

## How to build / validate

These files are laid out exactly as they should land in mathlib. In a mathlib4 checkout:

```bash
# from the root of a mathlib4 checkout:
cp -r /path/to/this/tree/* Mathlib/NumberTheory/ExponentialSums/
lake build Mathlib.NumberTheory.ExponentialSums.KusminLandau
lake build Mathlib.NumberTheory.ExponentialSums.KusminLandauGeneral
lake build Mathlib.NumberTheory.ExponentialSums.VanDerCorput
lake build Mathlib.NumberTheory.ExponentialSums.VanDerCorputThird
```

## What changed relative to the source (per file)

Only packaging — **every theorem statement and every proof term is transcribed unchanged** from the
source modules. The changes are:

* **Imports narrowed.** The originals used a monolithic `import Mathlib`; each extracted file now
  carries the narrow import set it actually needs (verified symbol-by-symbol against the mathlib4
  API surface and against the exact lemma names used by the pinned repository).
* **Private definitions localized.** Helpers that lived in the upstream project's private namespaces
  (`e2pi`, `cotPi`, `expI`) are now defined locally inside the destination file or its namespace,
  so nothing depends on the upstream project any more.
* **Two fragile API usages replaced by self-contained local arguments** (so the files do not hinge on
  lemmas whose names have churned between mathlib4 revisions):
  - `KusminLandauGeneral.lean`: `Nat.findGreatest` → a small local `lastIndexWith` with a three-part
    soundness lemma (in-range, satisfies `P`, greatest).
  - `VanDerCorput.lean`: `monotoneOn_of_hasDerivWithinAt_nonneg` → an explicit argument via
    `exists_hasDerivAt_eq_slope` (the mean value theorem); this also removes the now-unused
    `convex_Icc` / `interior_Icc` dependencies.
* A short "Extraction note" banner was added atop each file; the original module docstrings and
  copyright headers are preserved.

## Provenance

Extracted from `RiemannHypothesis/KusminLandau.lean`, `RiemannHypothesis/KusminLandauGeneral.lean`,
`RiemannHypothesis/VanDerCorput.lean`, `RiemannHypothesis/SqrtHarmonic.lean`,
`RiemannHypothesis/WeylDifferencing.lean`, `RiemannHypothesis/WeylQuadratic.lean`,
`RiemannHypothesis/VanDerCorputSums.lean`, `RiemannHypothesis/VanDerCorputThird.lean` in the
`riemann_hypothesis_formalization` repository.

## Status and caveats

* **No new mathematics.** This is pure re-packaging of already-formalized content; nothing was
  re-proved or altered.
* **Local compilation check required before PR.** This environment cannot install the Lean 4
toolchain or the multi-gigabyte mathlib olean cache (network download-size limits block both), so
  these files could not be run through `lake build` here. The narrowed imports were assembled by
  matching every external identifier against the mathlib4 documentation and the pinned repository's
  own verified usage, so breakage should be limited to occasional import-path adjustments of the
  kind a reviewer routinely fixes; the proof terms themselves are byte-for-byte identical to the
  source. Run the commands above before opening a PR.
* These files are the only part of this repository that currently has a realistic path to external
  validation (mathlib review); everything downstream of the Montgomery–Vaughan generalized Hilbert
  inequality remains blocked — see the repository report `docs/goal/evidence/2026-09-16-round-GHI-blocked.md`.
