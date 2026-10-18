# The cosecant form of the Montgomery–Vaughan inequality, with the constant `δ⁻¹`

Date: 2026-10-18
Task: `M2-HILBERT-CSC` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/HilbertCosecant.lean` (new; imports `LargeSieve` and
`MontgomeryVaughan`)

## Claim

```lean
theorem hasSum_inv_sq_int {x : ℝ} (hx : ∀ m : ℤ, x ≠ m) :
    HasSum (fun m : ℤ => 1 / (x + m) ^ 2) (π ^ 2 / Real.sin (π * x) ^ 2)

theorem cosecantHilbertInequality {n : ℕ} (α : Fin n → ℝ) (u : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ intDist (α r - α s)) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖
      ≤ δ⁻¹ * ∑ r, ‖u r‖ ^ 2

theorem cosecantHilbertInequality_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → ℝ) (x : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j)) :
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)‖
      ≤ δ⁻¹ * ∑ i ∈ s, ‖x i‖ ^ 2
```

`intDist θ = |θ − round θ|` is the existing distance to the nearest integer of
`RiemannHypothesis/LargeSieve.lean`, so the result plugs into the large-sieve chain. In words:
for points `α_r` that are `δ`-separated modulo one and complex `u_r`,
`|∑_{r≠s} u_r conj(u_s) / sin π(α_r − α_s)| ≤ δ⁻¹ ∑ |u_r|²`. Mode: a **proof**, in this
repository, of a classical theorem (Montgomery–Vaughan, *The large sieve*, Mathematika 20
(1973), 119–134; Iwaniec–Kowalski, Lemma 7.8). Mathlib supplies the cotangent expansion
`cot_series_rep'`, term-by-term differentiation (`hasDerivAt_tsum_of_isPreconnected`), the
spectral theorem and Basel's sum. It does not supply the expansion of `csc²` or the inequality.

All three theorems have axioms exactly `[propext, Classical.choice, Quot.sound]`.

## The argument (route b of the request)

Route b, Montgomery and Vaughan's own eigenvector argument rerun with the kernel
`A r s = csc π(α_r − α_s)` (`cscKernel`; `1 / sin 0 = 0` on the diagonal), was chosen because it
reuses `MontgomeryVaughan.lean` step by step and needs only one analytic input, the expansion of
`csc²`. Route a (periodization of `generalizedHilbertInequality`) would have needed the
partial-fraction expansion of `csc` itself and a Fejér-mean limit.

* `real_cot_series`: Mathlib's `cot_series_rep'` restricted to real non-integers,
  `π cot πy − 1/y = ∑_{n≥1} (1/(y−n) + 1/(y+n))`.
* `hasSum_inv_sq_int`: differentiating term by term on `(x − c/2, x + c/2)`, `c = ‖x‖`, where
  every summand's derivative is bounded by `2(1 + 2R/c)²/(n+1)²`, gives
  `π² / sin² πx = 1/x² + ∑_{n≥1} (1/(x−n)² + 1/(x+n)²)`, which is the `ℤ`-indexed sum.
* `cscKernel_mul_cscKernel`, `sum_cscKernel_mul_cscKernel`: `csc a csc b = csc(b − a)(cot a − cot b)`
  with `a = π(α_r − α_s)`, `b = π(α_r − α_t)`, `b − a = π(α_s − α_t)`; with the corrections at
  `r = s` and `r = t`, `∑_r A r s A r t = A s t (c_s − c_t) + 2 A s t C s t + [s = t] b_s`, where
  `C = cotKernel`, `c_s = ∑_r C r s`, `b_s = ∑_r A r s²`.
* `csc_eigen_bound`: for `A v = iμ v` the two `c`-terms are both `−iμ ∑ c_s |v_s|²` and cancel,
  exactly as in `MontgomeryVaughan.eigen_bound`; then `|A s t C s t| ≤ A s t²`
  (`abs_csc_mul_cot_le`, since `|cos| ≤ 1`) gives `μ² ‖v‖² ≤ 3 ∑_s b_s |v_s|²`.
* `sum_inv_sin_sq_le`: `b_s ≤ 1/(3δ²)`. By `hasSum_inv_sq_int`,
  `b_s = π⁻² ∑_{r≠s} ∑_m (α_r − α_s + m)⁻²`. For each finite set `T ⊆ ℤ` the points
  `α_r − α_s + m` (`r ≠ s`, `m ∈ T`) together with the centre `0` are `δ`-separated on the line
  (for `r ≠ r'` by `intDist ≥ δ`, for `r = r'` because `|m − m'| ≥ 1 ≥ δ`), so the fibre count of
  `MontgomeryVaughan.colSq_le` (`sum_inv_sq_le_of_separated`) bounds the finite part by
  `2ζ(2)/δ² = π²/(3δ²)`. `Real.tsum_le_of_sum_le` passes to the full series.
* `csc_eigenvalue_sq_le`, `csc_norm_apply_le`: `μ² ≤ 3/(3δ²) = δ⁻²`; the spectral theorem for the
  Hermitian `H = iA` gives `‖Hx‖ ≤ δ⁻¹ ‖x‖`.
* `cosecantHilbertInequality`: the form is `i ⟨Hx, x⟩`; Cauchy–Schwarz.
* `cosecantHilbertInequality_finset`: reindexing a finite set by `Finset.equivFin`; the diagonal
  terms vanish (`/ sin 0 = / 0`), so `s.erase i` and `s` give the same inner sum.

## Hypothesis hygiene

No new `def … : Prop` is introduced, and no theorem takes an unproved `Prop` as a hypothesis, so
the four hygiene questions do not arise. `docs/goal/conditional-theorems.txt` is unchanged
(see § "Commands and gates" of `2026-10-18-m2-large-sieve-mv.md`).

## Adversarial revalidation: M2-HILBERT-CSC

* *Constants, by hand.* `ζ(2) = π²/6`, so `π⁻² · 2ζ(2)/δ² = 1/(3δ²)` (`sum_inv_sin_sq_le`), and
  `3 · 1/(3δ²) = δ⁻²` (`csc_eigenvalue_sq_le`), whose square root is `δ⁻¹`. The pinned statement
  has `δ⁻¹`, not a weaker constant. The expansion is checked at `x = 1/2`:
  `∑_m (1/2 + m)⁻² = 2 · 4 ∑_{k≥0} (2k+1)⁻² = 8 · π²/8 = π² = π²/sin²(π/2)`.
* *Non-triviality.* `n = 2`, `α = (0, 1/2)`, `δ = 1/2`, `u = (1, i)`: the form is
  `1·(−i)/sin(−π/2) + i·1/sin(π/2) = 2i`, of norm `2`, against the right side `2 · 2 = 4`.
* *Vacuity.* The hypotheses (`0 < δ ≤ 1/2`, separation modulo one) hold for `α_r = r/n`,
  `δ = 1/n`, every `n ≥ 2`.
* *Load-bearing.* Without separation, `α = (0, ε)` and `u = (1, i)` give a form of norm
  `2/sin(πε)`, unbounded as `ε → 0`. `0 < δ` is needed for `δ⁻¹` to make sense. `δ ≤ 1/2` is used
  in the periodization (`|m − m'| ≥ 1 ≥ δ`); it is not restrictive, since for `n ≥ 2` separation
  already forces `δ ≤ intDist ≤ 1/2`.
* *Claim mode.* A proof in this repository. The cotangent expansion, the spectral theorem and
  Basel's sum are Mathlib's; the `csc²` expansion is derived here.
* *Statement pinning.* `scripts/revalidation.lean` writes out `hasSum_inv_sq_int`,
  `cosecantHilbertInequality` and `cosecantHilbertInequality_finset` in full and supplies the
  repository's declarations as proof terms. Their axioms are pinned in step 3 of
  `scripts/audit.sh`.

## Not proved

* The optimality of the constant `δ⁻¹`.
* The weighted form with `δ_r⁻¹` in place of `δ⁻¹`.

## Commands and gates

See `docs/goal/evidence/2026-10-18-m2-large-sieve-mv.md`, § "Commands and gates".
