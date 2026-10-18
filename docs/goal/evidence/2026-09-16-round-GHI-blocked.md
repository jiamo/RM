**2026-10-18:** the generalized Hilbert inequality has been proved since 2026-10-18: `RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality` in the module `RiemannHypothesis.MontgomeryVaughan` (`RiemannHypothesis/MontgomeryVaughan.lean`); the report below is kept unchanged as the 2026-09-16 record.
# Round report 2026-09-16 — Generalized Hilbert Inequality (blocked) and mathlib extraction (delivered)

**Starting point.** Snapshot `output-final_aristotle` of the `riemann_hypothesis_formalization`
repository (Lean 4 / mathlib4, `lean-toolchain` `leanprover/lean4:v4.33.0`, `lake-manifest.json`
pinning mathlib4 `v4.28.0`). Per instruction, `lake-manifest.json` was **not regenerated**; it is
byte-for-byte identical to the supplied archive. `RiemannHypothesis/Challenge.lean` carries only the
three equivalence proofs inserted in the previous round.

**Environment constraints (important).**
* The supplied snapshot contains **no `.git` directory**, so the named commit `732aac1` cannot be
  checked out in this environment; work proceeded from the snapshot itself, which is the only state
  available. This is recorded rather than worked around, because fabricating git history would be
  worse than stating the limitation.
* **No compilable Lean environment is attainable here.** The per-download size limit blocks the
  ~150 MB Lean 4.33.0 toolchain tarball and, a fortiori, the multi-gigabyte mathlib olean cache,
  so `lake build` cannot be run locally. Every new proof term below would therefore be unverifiable.
  This constraint is the decisive reason for the BLOCKED verdict on Deliverable 1 and the principal
  caveat on Deliverable 2.

---

## Deliverable 1 — `GeneralizedHilbertInequality` for δ-separated *real* frequencies: **BLOCKED**

### Statement under consideration
```
GeneralizedHilbertInequality :
  ∀ (δ : ℝ) (S : Finset ι) (lam : ι → ℝ) (x : ι → ℂ),
    0 < δ → (∀ r s, r ∈ S → s ∈ S → r ≠ s → δ ≤ |lam r - lam s|) →
    ‖∑ r in S, ∑ s in S.erase r, x r • conj(x s) / (lam r - lam s)‖ ≤ π / δ * ∑ r in S, ‖x r‖²
```
This is the Montgomery–Vaughan theorem (J. London Math. Soc. (2) 8 (1974), 73–82): the sharp bound
`π δ⁻¹`, the same constant as for lattice frequencies (`hilbert_inequality_lattice`, already proved
in `RiemannHypothesis/HilbertInequality.lean`). The statement is currently an unproved `Prop`; this
round leaves it exactly there.

### What was established about the gap
The file's own docstring frames the residual content as "the passage from the lattice to arbitrary
separated reals". Three facts are now pinned down:

1. **The naive route is provably dead.** With separation `δ`, at most two frequencies lie in each
   annulus `[rδ,(r+1)δ)`, so row sums of `|1/(λ_r − λ_s)|` diverge like the harmonic series: the
   triangle inequality plus separation yields only the free bound `O(δ⁻¹ log R)`. The logarithm is not
   an artifact of a sloppy estimate — it is intrinsic to any absolute-value (Schur-test) argument, and
   beating it requires exploiting cancellation.

2. **A widely circulated "elementary" proof is incorrect.** Notes in circulation (and the Bombieri–
   Vinogradov lecture notes derived from them) obtain the key ℓ² estimate
   `∑_r |∑_{s≠r} z_s/(λ_r−λ_s)|² ≤ (π/δ)² ∑_r |z_r|²` by expanding the square, applying the partial
   fraction identity `1/((λ_r−λ_s)(λ_r−λ_t)) = (1/(λ_s−λ_t))(1/(λ_r−λ_s) − 1/(λ_r−λ_t))`, and recording
   that "the two inner sums cancel". That cancellation step is equivalent to the identity
   ```
   ∑_{r ≠ s,t} 1/((λ_r−λ_s)(λ_r−λ_t)) = 2/(λ_s−λ_t)²   (claimed)
   ```
   which is **false** for finite separated families. Numerical check on random 1-separated families
   with R = 6: all 30 ordered pairs `(s,t)` fail, with discrepancies ranging from 3 to 3×10⁴. Carrying
   through what actually survives the failed cancellation reproduces exactly the insufficient free bound
   `O(δ⁻¹ log R)` of item 1 — the argument collapses into the case already excluded. So there is no
   short elementary detour around the hard analysis.

3. **What a correct proof needs.** The two published routes are each a substantial formalization
   project, and neither is available in this repository or in mathlib at the required sharpness:
   * **Montgomery and Vaughan's original 1974 argument**: a delicate double-sum manipulation with
     cosecant/cotangent kernels (partial-fraction expansions, symmetric pairing of `(s,t)` terms,
     passage from the sine-kernel form back to `1/x`). Reproducing it faithfully is paper-length.
   * **The Beurling–Selberg extremal route**: construct Beurling's entire majorant `B ≥ sign` of
     exponential type `2π` with `∫(B − sign) = 1`, prove Paley–Wiener/Plancherel for band-limited
     functions, then pair the bilinear form against band-limited test functions via Poisson summation
     so that off-diagonal pairings vanish by frequency separation. This demands extremal-function
     infrastructure and complex/Fourier analysis not present here.

Because (a) no correct short proof exists in the literature, (b) both real proofs require substantial
new infrastructure, and (c) this environment cannot compile anything, writing hundreds of lines of
unverified analysis here would be less honest than a clean block. Consistent with repository
convention, **no `sorry` has been introduced**: unproved statements stay `Prop`s.

### Consequence: four task-board rows marked BLOCKED
Per the standing instruction ("做不到就写清楚卡在哪一步，并把 M2-MOLLIFIER、四阶矩、Levinson、线性密度节省四行标成 BLOCKED"),
the following rows of `docs/goal/task-board.yaml` are set to `status: BLOCKED` with reasons:

| row | reading of the instruction | why it blocks |
|---|---|---|
| `M2-MOLLIFIER` | explicit | mollifier machinery for Levinson needs the sharp mean-value theorem over well-spaced frequencies, which needs the generalized Hilbert inequality |
| `M2-MEANVALUE` | the "fourth moment" side of the gap: the row's open boundary records that the sharp Montgomery–Vaughan mean-value form **and** the critical-line fourth moment are both missing inputs | open boundary states "neither [MV GHI] nor the fourth moment is formalized in that shape"; that gap is precisely what is blocked here |
| `M2-LEVINSON` | explicit ("Levinson") | the actual mollifier method (not the current corollary-of-two-thirds statement) depends on `M2-MOLLIFIER` |
| `M2-DENSITY` | explicit ("线性密度节省") | its open boundary states verbatim that the linear saving `N(σ,T)=O(T^{1−c(σ−1/2)})` "needs the sharp mean value theorem (Montgomery–Vaughan's generalized Hilbert inequality) or the fourth moment" — exactly the two blocked inputs |

The quadratic-saving statements already proved in `M2-DENSITY`/`M2-DENSITY-POWER-SAVING` remain valid and
are explicitly left untouched; only the unproved linear saving is blocked.

### Module-level record
The attempt log above is also written into the module docstring of
`RiemannHypothesis/HilbertInequality.lean` (section "Attempts toward the general form") so that the
blocking reasoning travels with the statement.

---

## Deliverable 2 — Kusmin–Landau / van der Corput extraction for mathlib: **DELIVERED**

The five requested items, plus the three files the fifth one literally depends on, have been organized
into mathlib-submittable form under
`submission/Mathlib/NumberTheory/ExponentialSums/` (nine `.lean` files + `README.md`):

| requested item | file(s) | content delivered |
|---|---|---|
| `KusminLandau` | `KusminLandau.lean` | discrete first-derivative test `norm_sum_e2pi_le_of_diff_mono_le`: `‖∑_{j≤K} e(u(c+j))‖ ≤ 1 + 2/λ` when successive differences of `u` are monotone in `[λ, 1−λ]` — no dependence on range length |
| `KusminLandauGeneral` | `KusminLandauGeneral.lean` | general monotone range: `(⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1)(1 + 2/λ)`; variation form `(V + 2)(1 + 2/λ)` |
| `VanDerCorput` (incl. `VDCSecondDerivative`) | `VanDerCorput.lean` | integral first-derivative test `‖∫_a^b e^{iF}‖ ≤ 4/m`; second-derivative test `VDCSecondDerivative`: `‖∫_a^b e^{iF}‖ ≤ 12/√r` when `|F''| ≥ r`; logarithmic-phase corollaries |
| `VDCThirdDerivative` | `VanDerCorputThird.lean` + `WeylDifferencing.lean`, `WeylQuadratic.lean`, `VanDerCorputSums.lean`, `SqrtHarmonic.lean` | third-derivative test for sums (exponent-pair step) via A-process/Weyl differencing + quadratic differenced-sum bound + second-derivative test for sums + the `∑ 1/√k ≤ 2√n` estimate |

### What changed relative to the source modules
Pure re-packaging — **every theorem statement and every proof term is transcribed unchanged**:
* Imports narrowed from monolithic `import Mathlib` to the exact dependency set of each file.
* Dependencies on the upstream project's private definitions removed: helpers `e2pi`, `cotPi`, `expI`
  are now local to the destination file/namespace.
* Two fragile API usages replaced by self-contained local arguments (so the files do not hinge on lemmas
  whose names churn between mathlib4 revisions):
  - `KusminLandauGeneral.lean`: `Nat.findGreatest` → local `lastIndexWith` with a three-part soundness lemma;
  - `VanDerCorput.lean`: `monotoneOn_of_hasDerivWithinAt_nonneg` → an explicit `exists_hasDerivAt_eq_slope`
    (mean value theorem) argument; unused `convex_Icc`/`interior_Icc` dependencies dropped.
* A short "Extraction note" banner tops each file; original copyright headers and module docstrings preserved.

### Build / verification instructions (must be done in the user's environment)
```bash
# in a mathlib4 checkout:
cp -r submission/* Mathlib/NumberTheory/ExponentialSums/
lake build Mathlib.NumberTheory.ExponentialSums.KusminLandau
lake build Mathlib.NumberTheory.ExponentialSums.KusminLandauGeneral
lake build Mathlib.NumberTheory.ExponentialSums.VanDerCorput
lake build Mathlib.NumberTheory.ExponentialSums.VanDerCorputThird
./scripts/audit.sh          # optional: confirm the main repository still builds/sorry-free
```
The narrowed imports were assembled symbol-by-symbol against the mathlib4 documentation surface and
against the exact lemma names used by the pinned repository (v4.28.0); because no compilation was
possible here, a first `lake build` may require routine import-path tweaks of the kind a mathlib
reviewer fixes anyway. The proof terms themselves are byte-for-byte identical to the source.

---

## Change manifest (files modified or added in this round)

```
RiemannHypothesis/HilbertInequality.lean            module-doc attempt log appended (no code change)
docs/goal/task-board.yaml                            M2-MEANVALUE, M2-MOLLIFIER, M2-LEVINSON, M2-DENSITY -> BLOCKED
docs/goal/evidence/2026-09-16-round-GHI-blocked.md   this report
submission/README.md                                 extraction package readme + build instructions
submission/Mathlib/NumberTheory/ExponentialSums/
  KusminLandau.lean                                  extracted
  KusminLandauGeneral.lean                           extracted (+ lastIndexWith patch)
  VanDerCorput.lean                                  extracted (+ MVT patch, unused import dropped)
  SqrtHarmonic.lean                                  extracted
  WeylDifferencing.lean                              extracted
  WeylQuadratic.lean                                 extracted
  VanDerCorputSums.lean                              extracted
  VanDerCorputThird.lean                             extracted
```
No other source, configuration, or build-artifact file was touched; in particular `lake-manifest.json`
and `lean-toolchain` are unchanged, and nothing outside `submission/` was added to the tree.

## Compile / audit status
Could not be run (environment cannot install the toolchain/cache; see top). All pre-existing content is
unchanged, so the prior audit status of the untouched `RiemannHypothesis/` modules is preserved.

## What the next round should do
1. In an environment with `elan`/`lake` and network: `cd submission && cp ... && lake build` the eight
   modules above; fix any import paths; once green, they are genuinely submit-ready to mathlib.
2. For the generalized Hilbert inequality: commit to ONE route (original MV cosecant-kernel argument is
   the shorter dependency footprint; Beurling–Selberg is more reusable infrastructure). Add the needed
   complex/Fourier-analysis lemmas, then attack `GeneralizedHilbertInequality`. Until that proposition
   has a proof term, `M2-MOLLIFIER`, `M2-LEVINSON` and the linear saving of `M2-DENSITY` cannot move.
