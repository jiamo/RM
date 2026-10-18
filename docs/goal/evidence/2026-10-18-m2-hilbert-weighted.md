# The weighted Montgomery–Vaughan inequality, with the constant `5√2`

Date: 2026-10-18
Task: `M2-HILBERT-WEIGHTED` (new, `DONE_STRONG`)
Modules: `RiemannHypothesis/LocalSpacingMaximal.lean` (new; imports `Mathlib`),
`RiemannHypothesis/MontgomeryVaughanWeighted.lean` (new; imports `MontgomeryVaughan` and
`LocalSpacingMaximal`)

## Claim

```lean
theorem weightedHilbertInequality {n : ℕ} (lam δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ |lam r - lam s|) (u : Fin n → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 5 * Real.sqrt 2 * ∑ r, ‖u r‖ ^ 2 / δ r

theorem hilbertInequality_of_uniform {n : ℕ} (lam : Fin n → ℝ) (u : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 5 * Real.sqrt 2 / δ * ∑ r, ‖u r‖ ^ 2
```

(both in namespace `RiemannHypothesis.MontgomeryVaughanWeighted`).

In words: for real `λ_r` and **any** family of weights `δ_r > 0` with `|λ_r − λ_s| ≥ δ_r` for
every `s ≠ r`, and complex `u_r`,
`|∑_{r≠s} u_r conj(u_s)/(λ_r − λ_s)| ≤ 5√2 ∑_r |u_r|²/δ_r`. This is the stronger of the two forms
in the request: it contains the case `δ_r = min_{s≠r} |λ_r − λ_s|`, and it is the form that
applications use (for `λ_n = −log n` the natural weight `1/(n+1)` is smaller than the exact local
spacing `log(1 + 1/n)`).

**The constant.** Montgomery and Vaughan (*Hilbert's inequality*, J. London Math. Soc. (2) 8
(1974), 73–82) prove `3π/2 ≈ 4.712`. The constant proved here is `5√2 ≈ 7.071 ≈ 2.251 π`, i.e.
about `1.50` times theirs (`5√2 / (3π/2) ≈ 1.5006`). `3π/2` is **not** proved. With all
`δ_r = δ` the theorem gives `(5√2)/δ`, weaker than the sharp `π/δ` of
`MontgomeryVaughan.generalizedHilbertInequality` (round 1), which is unchanged.

Mode: a **proof**, in this repository, of a classical theorem with a weaker constant. Mathlib
supplies the spectral theorem for symmetric operators, the layer-cake formula and basic
integration; it does not supply any Hilbert-type inequality or the maximal inequality.

Related vendored code: the third-party library `vendor/zeta23` (built as part of `lake build`)
contains `Zeta23.MV.mvDiag_thirteen : Zeta23.MVDiag 13`, the same inequality with the constant
`13` over an arbitrary `Fintype`. It is not used here; the proof below is independent and its
constant `5√2 ≈ 7.07` is smaller.

## The argument

Put `u_r = √δ_r x_r`. The form is `∑ x_r conj(x_s) B r s` with
`B r s = √δ_r √δ_s / (λ_r − λ_s)` (`wkernel`), so it suffices to bound the eigenvalues `iμ` of the
real skew-symmetric `B`.

* `sum_delta_kernel_mul_kernel` — the weighted partial-fraction identity: with
  `K r s = 1/(λ_r − λ_s)`, `a_s = ∑_r δ_r K r s`, `b_s = ∑_r δ_r K r s²`,
  `∑_r δ_r K r s K r t = K s t (a_s − a_t) + (δ_s + δ_t) K s t² + [s = t] b_s`.
* `weighted_eigen_identity` — Montgomery and Vaughan's eigenvector argument: expanding
  `‖Bv‖² = μ²‖v‖²` with that identity, the `a`-terms cancel because `v` is an eigenvector, and
  `μ²‖v‖² = ∑_{s,t} v_s conj(v_t) √δ_s √δ_t (δ_s + δ_t) K s t² + ∑_s δ_s b_s |v_s|²`.
  In the unweighted case the first sum is handled by `|v_s v_t| ≤ (|v_s|² + |v_t|²)/2`; with
  weights this fails, because the positive kernel `δ_s^{3/2} δ_t^{1/2} K s t²` is not bounded by
  Schur's test with any power weight `δ^β`. Montgomery and Vaughan handle the leftover terms by a
  finer estimate; here they are handled by a maximal inequality instead.
* `LocalSpacingMaximal.lean`:
  `sum_delta_ball_le` (the intervals of length `δ_t` about the `λ_t` are disjoint, so a ball of
  radius `R` about `λ_s` carries `∑ δ_t ≤ 3R`); `sum_div_sq_le_of_ballSum_le` (summation by parts:
  ball masses `≤ A R` give `∑_{t≠s} m_t/(λ_s − λ_t)² ≤ 2A/δ_s`); `delta_mul_sum_delta_div_sq_le`
  (`δ_s b_s ≤ 6`); `sum_delta_le_of_ballSum_gt` (Vitali covering: weak type `5/τ`);
  `sum_delta_mul_maxAvg_sq_le` (layer cake: `∑_s δ_s M_s² ≤ 120 ∑ a_t²` for the maximal ball
  averages `M_s` of the masses `a_t √δ_t`); `sum_sum_mul_div_sq_le`
  (`∑_{s≠t} a_s a_t δ_s^{3/2} δ_t^{1/2}/(λ_s − λ_t)² ≤ 2√120 ∑ a_t²` for `a ≥ 0`, by the summation
  by parts with `A = M_s` and Cauchy–Schwarz).
* `weighted_eigenvalue_sq_le` — taking real parts, `Re(v_s conj v_t) ≤ |v_s||v_t|`, symmetrizing
  the factor `δ_s + δ_t`, and the two bounds above:
  `μ² ≤ 2 · 2√120 + 6 = 6 + 4√120 < 50` (`sqrt_120_lt : √120 < 11`).
* `wMatrix_isHermitian`, `norm_wMatrix_apply_le` — the spectral theorem for `iB`, exactly as
  `MontgomeryVaughan.norm_apply_le`: `‖(iB)x‖ ≤ √50 ‖x‖ = 5√2 ‖x‖`.
* `weightedHilbertInequality` — the form is `i ⟨(iB)x, x⟩` with `x_r = u_r/√δ_r`; Cauchy–Schwarz,
  and `‖x‖² = ∑ |u_r|²/δ_r`.

## Hypothesis hygiene

No new `def … : Prop` is introduced, and no theorem takes an unproved `Prop` as a hypothesis, so
the four hygiene questions of `AGENTS.md` do not arise. `docs/goal/conditional-theorems.txt` is
unchanged.

## Adversarial revalidation: M2-HILBERT-WEIGHTED

* *Constants, by hand.* `√120 ≈ 10.954 < 11` (`11² = 121`); `6 + 4√120 ≈ 49.82 < 50`;
  `√50 = 5√2 ≈ 7.0711`; `3π/2 ≈ 4.7124`; `5√2/π ≈ 2.2508`. Inside the maximal argument:
  disjoint intervals in a ball of radius `R` (each of radius `≤` its distance to the centre) have
  total length `≤ 3R`; summation by parts against `2/r³` gives `2A/δ_s`, so `δ_s b_s ≤ 2·3 = 6`;
  Vitali with the `5×` enlargement gives weak type `5/τ`, and the layer-cake integral gives the
  `L²` constant `120`.
* *Non-triviality.* `n = 2`, `λ = (0, 1)`, `δ = (1, 1)`, `u = (1, i)`: the form is
  `1·(−i)/(−1) + i·1/1 = 2i`, of norm `2`, against the right side `5√2 · 2 ≈ 14.1`. Lower bound
  for any admissible constant: the uniform case must dominate the sharp unweighted constant, so
  `C ≥ π`; `5√2 ≈ 7.07 ≥ π`, consistent.
* *Vacuity.* The hypotheses hold for `λ_r = r`, `δ_r = 1`, and for `λ_k = −log(k+1)`,
  `δ_k = 1/(k+2)` (`log_local_spacing`, M2-MEANVALUE-WEIGHTED).
* *Load-bearing.* Without the spacing hypothesis, `λ = (0, ε)`, `δ = (1, 1)`, `u = (1, i)` give a
  form of norm `2/ε`, unbounded. `0 < δ_r` is needed for `/δ_r`. The hypothesis is only used with
  `δ_r` on the side of `r` (`δ_r ≤ |λ_r − λ_s|`), as in the request's stronger form.
* *Claim mode.* A proof in this repository, with the constant `5√2`, not Montgomery and
  Vaughan's `3π/2`.
* *Statement pinning.* `scripts/revalidation.lean` writes out `weightedHilbertInequality`,
  `hilbertInequality_of_uniform`, `weighted_eigenvalue_sq_le` (with `wkernel` unfolded) and
  `LocalSpacing.sum_sum_mul_div_sq_le` in full and supplies the repository's declarations as
  proof terms. Their axioms are pinned in step 3 of `scripts/audit.sh`.

## Not proved

* Montgomery and Vaughan's constant `3π/2`.
* The weighted cosecant inequality and the weighted large sieve are proved separately, with the
  constant `5√2/π` in place of `3/2` (M2-LARGE-SIEVE-WEIGHTED).

## Commands and gates

See `docs/goal/evidence/2026-10-18-m2-meanvalue-weighted.md`, § "Commands and gates".
