/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MollifiedZetaMeanSquare
import RiemannHypothesis.ZetaCircleAverage

/-!
# Circle averages of the mollified zeta function

`RiemannHypothesis/ZetaCircleAverage.lean` transports the mean square of `ζ` from vertical
lines to circles, which is what Jensen's counting inequality consumes; the resulting bound is
`O(T)` and gives the Bohr–Landau density theorem.  This file does the same for the *mollified*
function `F_y = ζ M_y`, whose mean square is not `O(T)` but `o(T)`:
`RiemannHypothesis/MollifiedZetaMeanSquare.lean` makes `∫ ‖F_y − 1‖²` as small as one likes,
and that is the extra saving Carlson's density theorem needs.

Two elementary facts replace the majorant `log x ≤ x²/2` of the unmollified route, whose
constant term is exactly what pins the Bohr–Landau bound at `O(T)`:

* `log ‖z‖ ≤ (λ/2) ‖z − 1‖² + 1/(2λ)` for every `λ > 0` — from `log ‖z‖ ≤ ‖z‖ − 1 ≤ ‖z − 1‖`
  and the arithmetic–geometric mean inequality.  Choosing `λ` large makes the constant term
  `1/(2λ)` arbitrarily small, at the cost of a large multiple of the mean square, which is
  affordable precisely because the mollified mean square is small.
* `‖F_y(s) − 1‖ ≤ 1/y` for `re s ≥ 3` — the mollifier identity in the half-plane of absolute
  convergence, together with `|c_y(m)| ≤ d(m) ≤ m`.  This keeps `− log ‖F_y‖` at the centre of
  the circle small, whereas for `ζ` alone it is only bounded by `log 2`.

## Main results

* `mollifiedZeta` : `F_y(z) = ζ(z) M_y(z)`.
* `norm_mollifiedZeta_sub_one_le` : `‖F_y − 1‖ ≤ 1/y` on `re s ≥ 3`.
* `circleAverage_log_norm_mollifiedZeta_le` : the circle average of `log ‖F_y‖` is at most
  `(λ/2)` times the circle average of `‖F_y − 1‖²`, plus `1/(2λ)`.
* `exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le` : the vertical integral of
  those circle averages is `≤ ε b`, for a mollifier length depending on `ε`.
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set

namespace RiemannHypothesis

/-- The mollified zeta function `F_y = ζ M_y`. -/
def mollifiedZeta (y : ℕ) (z : ℂ) : ℂ := riemannZeta z * Mollifier.mollifier y z

/-! ## Analyticity -/

/-- The mollifier is entire. -/
theorem analyticAt_mollifier (y : ℕ) (z : ℂ) : AnalyticAt ℂ (Mollifier.mollifier y) z := by
  have hdiff : Differentiable ℂ (Mollifier.mollifier y) := by
    unfold Mollifier.mollifier
    refine Differentiable.fun_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    exact (Differentiable.const_cpow differentiable_id.neg (Or.inl hn0)).const_mul _
  exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- `F_y` is analytic on a neighbourhood of the closed ball of radius `R < 5/2` about `3 + i u`,
for `u ≥ 4`. -/
theorem analyticOnNhd_mollifiedZeta_closedBall (y : ℕ) {u R : ℝ} (hu : 4 ≤ u) (hR : R < 5 / 2) :
    AnalyticOnNhd ℂ (mollifiedZeta y) (closedBall ((3 : ℂ) + (u : ℂ) * I) R) := by
  intro z hz
  have hz1 : z ≠ 1 := fun h => one_notMem_closedBall_of_le hu hR (h ▸ hz)
  exact (analyticAt_riemannZeta' hz1).mul (analyticAt_mollifier y z)

/-! ## The value at the centre -/

/-- The majorant used for the tail of the mollified series: `1/n²` beyond `y`, `0` below. -/
def invSqTail (y n : ℕ) : ℝ := if n ≤ y then 0 else 1 / (n : ℝ) ^ 2

theorem invSqTail_nonneg (y n : ℕ) : 0 ≤ invSqTail y n := by
  rw [invSqTail]
  split
  · exact le_refl _
  · positivity

theorem summable_invSqTail (y : ℕ) : Summable (invSqTail y) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hle : ∀ n : ℕ, invSqTail y n ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rw [invSqTail]
    split
    · positivity
    · exact le_refl _
  exact Summable.of_nonneg_of_le (invSqTail_nonneg y) hle hp

/-- `∑_{n > y} 1/n² ≤ 1/y`. -/
theorem tsum_invSqTail_le {y : ℕ} (hy : 1 ≤ y) : ∑' n : ℕ, invSqTail y n ≤ 1 / y := by
  refine tsum_le_of_sum_range_le (invSqTail_nonneg y) fun M => ?_
  have hsub : Finset.Ioc y (M - 1) ⊆ Finset.range M := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  have hzero : ∀ n ∈ Finset.range M, n ∉ Finset.Ioc y (M - 1) → invSqTail y n = 0 := by
    intro n hn hn'
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn'
    have hny : n ≤ y := by
      by_contra hc
      exact absurd (hn' (by omega)) (by omega)
    rw [invSqTail, if_pos hny]
  rw [← Finset.sum_subset hsub hzero]
  have hcongr : ∑ n ∈ Finset.Ioc y (M - 1), invSqTail y n
      = ∑ n ∈ Finset.Ioc y (M - 1), 1 / (n : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Ioc] at hn
    rw [invSqTail, if_neg (by omega)]
  rw [hcongr]
  exact sum_Ioc_inv_sq_le hy (M - 1)

/-- **`‖ζ M_y − 1‖ ≤ 1/y` on the half-plane `re s ≥ 3`.**  The tail coefficients of `ζ M_y`
are bounded by the divisor function, which is at most the argument. -/
theorem norm_mollifiedZeta_sub_one_le {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖mollifiedZeta y s - 1‖ ≤ 1 / y := by
  classical
  have hs1 : 1 < s.re := by linarith
  have heq : mollifiedZeta y s - 1 = LSeries (Mollifier.tailCoeff y) s := by
    rw [mollifiedZeta, Mollifier.zeta_mul_mollifier_eq_one_add_tail hy hs1]
    ring
  have hterm : ∀ n : ℕ, ‖LSeries.term (Mollifier.tailCoeff y) s n‖ ≤ invSqTail y n := by
    intro n
    rcases le_or_gt n y with hn | hn
    · have h0 : Mollifier.tailCoeff y n = 0 := by
        rw [Mollifier.tailCoeff, if_neg (by omega)]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [LSeries.term_zero, norm_zero]
        exact invSqTail_nonneg y 0
      · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), h0, zero_div, norm_zero]
        exact invSqTail_nonneg y n
    · have hn1 : 1 ≤ n := by omega
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hcoeff : ‖Mollifier.tailCoeff y n‖ ≤ (n : ℝ) := by
        rw [Mollifier.tailCoeff, if_pos hn]
        refine (norm_detectCoeff_le_divisorCount y n).trans ?_
        exact_mod_cast Nat.card_divisors_le_self n
      rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hn1, invSqTail, if_neg (by omega)]
      have hpow3 : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hnR hs
      have hpow3' : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hposre : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by linarith) _
      rw [div_le_div_iff₀ hposre (by positivity)]
      have hmul : ‖Mollifier.tailCoeff y n‖ * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      have h3 : (n : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ s.re := by
        calc (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (3 : ℝ) := by rw [hpow3']; ring
          _ ≤ (n : ℝ) ^ s.re := hpow3
      rw [one_mul]
      exact hmul.trans h3
  have hns : Summable (fun n => ‖LSeries.term (Mollifier.tailCoeff y) s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (summable_invSqTail y)
  rw [heq, LSeries]
  calc ‖∑' n : ℕ, LSeries.term (Mollifier.tailCoeff y) s n‖
      ≤ ∑' n : ℕ, ‖LSeries.term (Mollifier.tailCoeff y) s n‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n : ℕ, invSqTail y n := hns.tsum_le_tsum hterm (summable_invSqTail y)
    _ ≤ 1 / y := tsum_invSqTail_le hy

/-- The mollified zeta function does not vanish on `re s ≥ 3` once `y ≥ 2`. -/
theorem mollifiedZeta_ne_zero {y : ℕ} (hy : 2 ≤ y) {s : ℂ} (hs : 3 ≤ s.re) :
    mollifiedZeta y s ≠ 0 := by
  intro h
  have hbd := norm_mollifiedZeta_sub_one_le (by omega : 1 ≤ y) hs
  rw [h, zero_sub, norm_neg, norm_one] at hbd
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  rw [le_div_iff₀ (by linarith)] at hbd
  linarith

/-- The logarithm at the centre is small: `− log ‖F_y(c)‖ ≤ 2/y` for `y ≥ 4`. -/
theorem neg_log_norm_mollifiedZeta_le {y : ℕ} (hy : 4 ≤ y) {s : ℂ} (hs : 3 ≤ s.re) :
    -Real.log ‖mollifiedZeta y s‖ ≤ 2 / y := by
  have hy4 : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hbd := norm_mollifiedZeta_sub_one_le (by omega : 1 ≤ y) hs
  have hrev : 1 - ‖mollifiedZeta y s‖ ≤ ‖mollifiedZeta y s - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (mollifiedZeta y s)
    rw [norm_one, norm_sub_rev] at this
    linarith [this]
  have hlow : 1 - 1 / (y : ℝ) ≤ ‖mollifiedZeta y s‖ := by linarith
  have hylow : 1 / (y : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hpos : (0 : ℝ) < ‖mollifiedZeta y s‖ := by linarith
  -- `-log u ≤ 1/u - 1` for `u > 0`
  have hkey : -Real.log ‖mollifiedZeta y s‖ ≤ 1 / ‖mollifiedZeta y s‖ - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 1 / ‖mollifiedZeta y s‖) (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub] at h
    linarith
  have hinv : 1 / ‖mollifiedZeta y s‖ - 1 ≤ 2 / (y : ℝ) := by
    have hd : (0 : ℝ) < 1 - 1 / (y : ℝ) := by linarith
    have h1 : 1 / ‖mollifiedZeta y s‖ ≤ 1 / (1 - 1 / (y : ℝ)) :=
      one_div_le_one_div_of_le hd hlow
    have h2 : 1 / (1 - 1 / (y : ℝ)) - 1 ≤ 2 / (y : ℝ) := by
      rw [div_sub_one (ne_of_gt hd), div_le_div_iff₀ hd (by linarith)]
      have hyinv : 1 / (y : ℝ) * (y : ℝ) = 1 := by field_simp
      nlinarith [hyinv, hylow]
    linarith
  linarith

/-! ## The majorant with an adjustable constant -/

/-- `log ‖z‖ ≤ (λ/2) ‖z − 1‖² + 1/(2λ)` for every `λ > 0`.  With Lean's convention
`log 0 = 0` this also holds at `z = 0`. -/
theorem log_norm_le_lam_normSq_sub_one (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    Real.log ‖z‖ ≤ lam / 2 * ‖z - 1‖ ^ 2 + 1 / (2 * lam) := by
  have hamgm : ∀ a : ℝ, a ≤ lam / 2 * a ^ 2 + 1 / (2 * lam) := by
    intro a
    have h : 0 ≤ (lam * a - 1) ^ 2 / (2 * lam) := by positivity
    have hexp : (lam * a - 1) ^ 2 / (2 * lam)
        = lam / 2 * a ^ 2 + 1 / (2 * lam) - a := by
      field_simp
      ring
    linarith [hexp ▸ h]
  have hstep : Real.log ‖z‖ ≤ ‖z - 1‖ := by
    rcases eq_or_lt_of_le (norm_nonneg z) with h | h
    · rw [← h, Real.log_zero]
      exact norm_nonneg _
    · have h1 := Real.log_le_sub_one_of_pos h
      have h2 : ‖z‖ - 1 ≤ ‖z - 1‖ := by
        have := norm_sub_norm_le z (1 : ℂ)
        rwa [norm_one] at this
      linarith
  exact hstep.trans (hamgm _)

/-- The circle average form of the previous majorant. -/
theorem circleAverage_log_norm_mollifiedZeta_le {y : ℕ} {u R lam : ℝ} (hu : 4 ≤ u)
    (hR0 : 0 < R) (hR : R < 5 / 2) (hlam : 0 < lam) :
    circleAverage (fun z => Real.log ‖mollifiedZeta y z‖) ((3 : ℂ) + (u : ℂ) * I) R
      ≤ lam / 2 * circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2)
          ((3 : ℂ) + (u : ℂ) * I) R + 1 / (2 * lam) := by
  set c : ℂ := (3 : ℂ) + (u : ℂ) * I with hc
  have habs : |R| = R := abs_of_pos hR0
  have hone : (1 : ℂ) ∉ sphere c R := fun h =>
    one_notMem_closedBall_of_le hu hR (sphere_subset_closedBall h)
  have hana : ∀ z ∈ sphere c |R|, AnalyticAt ℂ (mollifiedZeta y) z := by
    intro z hz
    rw [habs] at hz
    have hz1 : z ≠ 1 := fun h => hone (h ▸ hz)
    exact (analyticAt_riemannZeta' hz1).mul (analyticAt_mollifier y z)
  have hlogint : CircleIntegrable (fun z => Real.log ‖mollifiedZeta y z‖) c R :=
    MeromorphicOn.circleIntegrable_log_norm (fun z hz => (hana z hz).meromorphicAt)
  have hsqint : CircleIntegrable (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) c R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    intro z hz
    have hz' : z ∈ sphere c |R| := by rwa [habs]
    exact (((hana z hz').continuousAt.sub continuousAt_const).norm.pow 2).continuousWithinAt
  have hmulint : CircleIntegrable (fun z => lam / 2 * ‖mollifiedZeta y z - 1‖ ^ 2) c R := by
    rw [circleIntegrable_def] at hsqint ⊢
    exact hsqint.const_mul _
  have hCA : circleAverage
      (fun z => lam / 2 * ‖mollifiedZeta y z - 1‖ ^ 2 + 1 / (2 * lam)) c R
      = lam / 2 * circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) c R
        + 1 / (2 * lam) := by
    rw [circleAverage_fun_add hmulint (circleIntegrable_const _ _ _), circleAverage_const]
    congr 1
    have h := circleAverage_fun_smul (a := lam / 2)
      (f := fun z => ‖mollifiedZeta y z - 1‖ ^ 2) (c := c) (R := R)
    simpa only [smul_eq_mul] using h
  rw [← hCA]
  refine circleAverage_mono hlogint ?_ (fun z _ => log_norm_le_lam_normSq_sub_one lam hlam _)
  rw [circleIntegrable_def] at hmulint ⊢
  exact hmulint.add intervalIntegrable_const

/-! ## Integrating the circle averages in the ordinate of the centre -/

/-- The integrand of the circle average of `‖F_y − 1‖²`, as a function of the angle `θ` and of
the ordinate `u` of the centre. -/
def mollifiedCircleIntegrandSq (y : ℕ) (R θ u : ℝ) : ℝ :=
  ‖mollifiedZeta y (circleMap ((3 : ℂ) + (u : ℂ) * I) R θ) - 1‖ ^ 2

/-- Joint continuity of the integrand on a box of ordinates bounded below by `4`. -/
theorem continuousOn_uncurry_mollifiedCircleIntegrandSq (y : ℕ) {R : ℝ} (hR : |R| < 5 / 2)
    {a b : ℝ} (ha : 4 ≤ a) :
    ContinuousOn (Function.uncurry fun θ u => mollifiedCircleIntegrandSq y R θ u)
      (Set.Icc 0 (2 * π) ×ˢ Set.Icc a b) := by
  have hg : Continuous fun p : ℝ × ℝ => circleMap ((3 : ℂ) + (p.2 : ℂ) * I) R p.1 := by
    unfold circleMap
    fun_prop
  rintro ⟨θ, u⟩ ⟨-, hu⟩
  have hu4 : 4 ≤ u := le_trans ha hu.1
  have hne : circleMap ((3 : ℂ) + (u : ℂ) * I) R θ ≠ 1 := circleMap_ne_one hu4 hR
  have hF : AnalyticAt ℂ (mollifiedZeta y) (circleMap ((3 : ℂ) + (u : ℂ) * I) R θ) :=
    (analyticAt_riemannZeta' hne).mul (analyticAt_mollifier y _)
  have h1 : ContinuousAt
      (fun p : ℝ × ℝ => mollifiedZeta y (circleMap ((3 : ℂ) + (p.2 : ℂ) * I) R p.1)) (θ, u) :=
    ContinuousAt.comp (g := mollifiedZeta y) hF.continuousAt hg.continuousAt
  exact (((h1.sub continuousAt_const).norm.pow 2)).continuousWithinAt

/-- Integrability of the integrand on the box `[0, 2π] × [a, b]`. -/
theorem integrable_uncurry_mollifiedCircleIntegrandSq (y : ℕ) {R : ℝ} (hR : |R| < 5 / 2)
    {a b : ℝ} (ha : 4 ≤ a) :
    Integrable (Function.uncurry fun θ u => mollifiedCircleIntegrandSq y R θ u)
      ((volume.restrict (Set.Ioc 0 (2 * π))).prod (volume.restrict (Set.Ioc a b))) := by
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact (continuousOn_uncurry_mollifiedCircleIntegrandSq y hR ha).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- The circle average written out as an interval integral in the angle. -/
theorem circleAverage_normSq_mollifiedZeta_sub_one_eq {y : ℕ} {R u : ℝ} :
    circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), mollifiedCircleIntegrandSq y R θ u := by
  rw [circleAverage_def]
  simp [mollifiedCircleIntegrandSq, smul_eq_mul]

/-- The circle averages of `‖F_y − 1‖²` are integrable in the ordinate of the centre. -/
theorem intervalIntegrable_circleAverage_normSq_mollifiedZeta_sub_one (y : ℕ) {R : ℝ}
    (hR0 : 0 < R) (hR : R < 5 / 2) {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2)
      ((3 : ℂ) + (u : ℂ) * I) R) volume a b := by
  have hRabs : |R| < 5 / 2 := by rwa [abs_of_pos hR0]
  have hint :=
    (integrable_uncurry_mollifiedCircleIntegrandSq y hRabs (a := a) (b := b) ha).integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  have h2 : (fun u : ℝ =>
      circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
      = fun u : ℝ => (2 * π)⁻¹ * ∫ θ in Set.Ioc 0 (2 * π), mollifiedCircleIntegrandSq y R θ u := by
    funext u
    rw [circleAverage_normSq_mollifiedZeta_sub_one_eq, intervalIntegral.integral_of_le hpi]
  rw [h2]
  exact hint.const_mul _

/-- **The vertical integral of the circle averages of `‖F_y − 1‖²` is `≤ ε b`.**  This is the
mollified mean square of `RiemannHypothesis/MollifiedZetaMeanSquare.lean`, transported from
vertical lines to circles by Fubini. -/
theorem exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le {R ε : ℝ} (hR0 : 0 < R)
    (hR : R < 5 / 2) (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y : ℕ, y₀ ≤ y → ∃ b₀ : ℝ, 4 ≤ b₀ ∧
      ∀ a b : ℝ, 4 ≤ a → a ≤ b → b₀ ≤ b →
        (∫ u in a..b, circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2)
            ((3 : ℂ) + (u : ℂ) * I) R) ≤ ε * b := by
  have hRabs : |R| < 5 / 2 := by rwa [abs_of_pos hR0]
  set σ₀ : ℝ := min (3 - R) (3 / 4) with hσ₀
  have hσ₀0 : 1 / 2 < σ₀ := lt_min (by linarith) (by norm_num)
  have hσ₀1 : σ₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨y₀, hy₀4, hall⟩ :=
    exists_integral_normSq_zeta_mul_mollifier_sub_one_le hσ₀0 hσ₀1 (half_pos hε)
  refine ⟨y₀, hy₀4, fun y hy => ?_⟩
  obtain ⟨b₁, hb₁, hbd⟩ := hall y hy
  refine ⟨max (b₁ + 5 / 2) 4, le_max_right _ _, fun a b ha hab hb => ?_⟩
  have hb1 : b₁ + 5 / 2 ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : (4 : ℝ) ≤ b := le_trans ha hab
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  -- the inner estimate, for a fixed angle
  have hinner : ∀ θ : ℝ, (∫ u in a..b, mollifiedCircleIntegrandSq y R θ u)
      ≤ ε / 2 * (b + 5 / 2) := by
    intro θ
    have hs : ∀ u : ℝ, circleMap ((3 : ℂ) + (u : ℂ) * I) R θ
        = ((3 + R * Real.cos θ : ℝ) : ℂ) + ((u + R * Real.sin θ : ℝ) : ℂ) * I := by
      intro u
      simp only [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hEq : (∫ u in a..b, mollifiedCircleIntegrandSq y R θ u)
        = ∫ u in a..b, ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ)
              + ((u + R * Real.sin θ : ℝ) : ℂ) * I) *
            Mollifier.mollifier y (((3 + R * Real.cos θ : ℝ) : ℂ)
              + ((u + R * Real.sin θ : ℝ) : ℂ) * I) - 1‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [mollifiedCircleIntegrandSq, hs u, mollifiedZeta]
    have hshift : (∫ u in a..b, ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ)
            + ((u + R * Real.sin θ : ℝ) : ℂ) * I) *
          Mollifier.mollifier y (((3 + R * Real.cos θ : ℝ) : ℂ)
            + ((u + R * Real.sin θ : ℝ) : ℂ) * I) - 1‖ ^ 2)
        = ∫ v in (a + R * Real.sin θ)..(b + R * Real.sin θ),
            ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) *
              Mollifier.mollifier y (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2 := by
      rw [← intervalIntegral.integral_comp_add_right
        (fun v : ℝ => ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) *
          Mollifier.mollifier y (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2)
        (R * Real.sin θ)]
    have hsin : |R * Real.sin θ| ≤ |R| := by
      rw [abs_mul]
      calc |R| * |Real.sin θ| ≤ |R| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg R)
        _ = |R| := mul_one _
    have hsin' := neg_abs_le (R * Real.sin θ)
    have hsin'' := le_abs_self (R * Real.sin θ)
    have hlow : (1 : ℝ) ≤ a + R * Real.sin θ := by linarith
    have hcos : |R * Real.cos θ| ≤ |R| := by
      rw [abs_mul]
      calc |R| * |Real.cos θ| ≤ |R| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg R)
        _ = |R| := mul_one _
    have hR' : |R| = R := abs_of_pos hR0
    have hcos' := neg_abs_le (R * Real.cos θ)
    have hcos'' := le_abs_self (R * Real.cos θ)
    have hleσ : σ₀ ≤ 3 + R * Real.cos θ := by
      have h1 : σ₀ ≤ 3 - R := min_le_left _ _
      rw [hR'] at hcos
      linarith
    have hupσ : 3 + R * Real.cos θ ≤ 6 := by
      rw [hR'] at hcos
      linarith
    have hb₁le : b₁ ≤ b + R * Real.sin θ := by
      rw [hR'] at hsin
      linarith
    have hle := hbd (3 + R * Real.cos θ) hleσ hupσ (a + R * Real.sin θ) (b + R * Real.sin θ)
      hlow (by linarith) hb₁le
    have hub : b + R * Real.sin θ ≤ b + 5 / 2 := by
      rw [hR'] at hsin
      linarith
    rw [hEq, hshift]
    calc (∫ v in (a + R * Real.sin θ)..(b + R * Real.sin θ),
          ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) *
            Mollifier.mollifier y (((3 + R * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2)
        ≤ ε / 2 * (b + R * Real.sin θ) := hle
      _ ≤ ε / 2 * (b + 5 / 2) := by
          exact mul_le_mul_of_nonneg_left hub (by linarith)
  -- Fubini and the outer estimate
  have hswap : (∫ u in a..b, ∫ θ in (0 : ℝ)..(2 * π), mollifiedCircleIntegrandSq y R θ u)
      = ∫ θ in (0 : ℝ)..(2 * π), ∫ u in a..b, mollifiedCircleIntegrandSq y R θ u := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hpi]
    have h1 : ∀ u : ℝ, (∫ θ in (0 : ℝ)..(2 * π), mollifiedCircleIntegrandSq y R θ u)
        = ∫ θ in Set.Ioc 0 (2 * π), mollifiedCircleIntegrandSq y R θ u := fun _ =>
      intervalIntegral.integral_of_le hpi
    simp only [h1]
    have h2 : ∀ θ : ℝ, (∫ u in a..b, mollifiedCircleIntegrandSq y R θ u)
        = ∫ u in Set.Ioc a b, mollifiedCircleIntegrandSq y R θ u := fun _ =>
      intervalIntegral.integral_of_le hab
    simp only [h2]
    exact (integral_integral_swap
      (integrable_uncurry_mollifiedCircleIntegrandSq y hRabs ha)).symm
  have hrewrite : (∫ u in a..b,
        circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
      = (2 * π)⁻¹ * ∫ u in a..b, ∫ θ in (0 : ℝ)..(2 * π),
          mollifiedCircleIntegrandSq y R θ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => circleAverage_normSq_mollifiedZeta_sub_one_eq
  have houter : (∫ θ in (0 : ℝ)..(2 * π), ∫ u in a..b, mollifiedCircleIntegrandSq y R θ u)
      ≤ 2 * π * (ε / 2 * (b + 5 / 2)) := by
    have hintθ : IntervalIntegrable
        (fun θ : ℝ => ∫ u in a..b, mollifiedCircleIntegrandSq y R θ u) volume 0 (2 * π) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
      have hprod := (integrable_uncurry_mollifiedCircleIntegrandSq y hRabs (a := a) (b := b)
        ha).integral_prod_left
      have h2 : (fun θ : ℝ => ∫ u in a..b, mollifiedCircleIntegrandSq y R θ u)
          = fun θ : ℝ => ∫ u in Set.Ioc a b, mollifiedCircleIntegrandSq y R θ u := by
        funext θ
        exact intervalIntegral.integral_of_le hab
      rw [h2]
      exact hprod
    have h := intervalIntegral.integral_mono_on hpi hintθ
      (intervalIntegrable_const (c := ε / 2 * (b + 5 / 2))) (fun θ _ => hinner θ)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    exact h
  rw [hrewrite, hswap]
  have hpipos : (0 : ℝ) < 2 * π := by positivity
  have hstep : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), ∫ u in a..b,
        mollifiedCircleIntegrandSq y R θ u)
      ≤ (2 * π)⁻¹ * (2 * π * (ε / 2 * (b + 5 / 2))) :=
    mul_le_mul_of_nonneg_left houter (by positivity)
  have hsimp : (2 * π)⁻¹ * (2 * π * (ε / 2 * (b + 5 / 2))) = ε / 2 * (b + 5 / 2) := by
    field_simp
  rw [hsimp] at hstep
  refine hstep.trans ?_
  nlinarith [hε.le, hb4]

end RiemannHypothesis
