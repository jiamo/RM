/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.GallagherDiscrete
import RiemannHypothesis.GaussianMeanValue

/-!
# The discrete mean value theorem with the error term inside the sum

`RiemannHypothesis/GallagherDiscrete.lean` combines Gallagher's Sobolev lemma with the
*elementary* mean value theorem, and so carries the error term `8 N (1 + log N)` outside the
sum.  `RiemannHypothesis/GaussianMeanValue.lean` proves the Montgomery–Vaughan shape of the
continuous mean value theorem, with the error term inside the sum.  Feeding the latter into
Gallagher's lemma gives the discrete bound in the same shape:

`∑_i ‖D(σ + i t_i)‖² ≤ 58 (2/δ + δ (log N)²) ∑_{n ≤ N} ‖a n‖² n^(-2σ) (T + n)`

for `δ`-separated points `t_i ∈ [δ/2, T - δ/2]` and `T ≥ 6`.

## Main results

* `sum_normSq_dirichletPoly_at_separated_le_mv` — the discrete mean value theorem.
* `card_le_of_dirichletPoly_large_separated_mv` — the large values count that follows.

## Scope

The constant `58` is the one of `integral_normSq_dirichletPoly_le_mv` and is not sharp, and the
Sobolev step keeps the factor `2/δ + δ (log N)²` of the elementary Gallagher inequality.  Only
the shape of the error term is improved.  Everything here is about Dirichlet polynomials, not
about `ζ`: no zero-density estimate follows and no zero is located.
-/

noncomputable section

open Complex MeasureTheory Finset

namespace RiemannHypothesis

/-- The `(T + n)`-weighted mean-square weight of the coefficients `a n log n` is at most
`(log N)²` times that of the coefficients `a n`. -/
theorem sum_normSq_logCoeff_weighted_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∑ n ∈ Icc 1 N, ‖logCoeff a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)
      ≤ Real.log N ^ 2 * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogle : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hnorm : ‖logCoeff a n‖ ^ 2 = Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    simp only [logCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by linarith) _
  have hw : (0 : ℝ) ≤ T + n := by linarith
  have hsq : Real.log n ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hna : (0 : ℝ) ≤ ‖a n‖ ^ 2 := by positivity
  rw [hnorm]
  have hfac : (0 : ℝ) ≤ ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hna hpow) hw]

/-- **The discrete mean value theorem, in Montgomery–Vaughan shape.**  For `δ`-separated points
`t i` in `[δ/2, T - δ/2]` and `T ≥ 6`,

`∑_i ‖D(σ + i t_i)‖² ≤ 58 (2/δ + δ (log N)²) ∑_{n ≤ N} ‖a n‖² n^(-2σ) (T + n)`. -/
theorem sum_normSq_dirichletPoly_at_separated_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 6 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set W := ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    refine Finset.sum_nonneg fun n hn => ?_
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h2 : (0 : ℝ) ≤ T + n := by positivity
    positivity
  set f : ℝ → ℂ := fun x => dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I) with hf
  set f' : ℝ → ℂ := fun x => -I * dirichletPoly (logCoeff a) N ((σ : ℂ) + (x : ℂ) * I) with hf'
  have hderiv : ∀ x, HasDerivAt f (f' x) x := fun x => hasDerivAt_dirichletPoly_line a N σ x
  have hf'cont : Continuous f' :=
    continuous_const.mul (continuous_dirichletPoly_line_coeff (logCoeff a) N σ)
  have hmem' : ∀ i ∈ s, t i ∈ Set.Icc (0 + δ / 2) (T - δ / 2) := by
    intro i hi
    simpa using hmem i hi
  have hgal := Gallagher.sum_normSq_le_of_separated hderiv hf'cont hδ hT0 hsep hmem'
  have hfsq : (∫ x in (0 : ℝ)..T, ‖f x‖ ^ 2) ≤ 58 * W :=
    integral_Icc_normSq_dirichletPoly_le_mv a N σ hT
  have hf'sq : (∫ x in (0 : ℝ)..T, ‖f' x‖ ^ 2) ≤ 58 * (Real.log N ^ 2 * W) := by
    have hcongr : (∫ x in (0 : ℝ)..T, ‖f' x‖ ^ 2)
        = ∫ x in (0 : ℝ)..T, ‖dirichletPoly (logCoeff a) N ((σ : ℂ) + (x : ℂ) * I)‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp [hf']
    rw [hcongr]
    refine le_trans (integral_Icc_normSq_dirichletPoly_le_mv (logCoeff a) N σ hT) ?_
    exact mul_le_mul_of_nonneg_left (sum_normSq_logCoeff_weighted_le a N σ hT0) (by norm_num)
  have hkey : δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ 2 * (58 * W) + δ ^ 2 * (58 * (Real.log N ^ 2 * W)) := by
    refine hgal.trans ?_
    have hδ2 : (0 : ℝ) ≤ δ ^ 2 := by positivity
    nlinarith [hfsq, hf'sq]
  have hdiv : ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ (2 * (58 * W) + δ ^ 2 * (58 * (Real.log N ^ 2 * W))) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [hkey]
  have hsimp : (2 * (58 * W) + δ ^ 2 * (58 * (Real.log N ^ 2 * W))) / δ
      = 58 * (2 / δ + δ * Real.log N ^ 2) * W := by
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

/-- **The large values count at separated points, in Montgomery–Vaughan shape.** -/
theorem card_le_of_dirichletPoly_large_separated_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ} (hδ : 0 < δ) (hT : 6 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * (∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)) / V ^ 2 := by
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _i ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2 :=
          Finset.sum_le_sum fun i hi => by
            have h := hbig i hi
            nlinarith [hV.le, norm_nonneg (dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I))]
  have hup := sum_normSq_dirichletPoly_at_separated_le_mv a N σ hδ hT hsep hmem
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < V ^ 2)]
  linarith

end RiemannHypothesis
