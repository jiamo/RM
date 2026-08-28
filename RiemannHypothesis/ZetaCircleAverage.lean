/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareUniform
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Averages of `log ‖ζ‖` over circles, integrated in the vertical direction

The Bohr–Landau zero-density argument counts the zeroes of `ζ` in a disc by Jensen's formula
(`RiemannHypothesis.card_mul_log_le_circleAverage_sub_log`), which bounds the count by the average
of `log ‖ζ‖` over the boundary circle.  This file bounds those averages *after integration over
the centre's ordinate*, which is the only form in which they are `O(T)`.

The key inequality is the elementary `Real.log x ≤ x² / 2` for `x ≥ 0`: it replaces `log ‖ζ‖` by
the nonnegative continuous function `‖ζ‖² / 2`, for which the interchange of the `θ`- and
`y`-integrations is Tonelli for a continuous nonnegative function on a compact box.  Each inner
integral is then a mean square of `ζ` on a vertical line of abscissa `3 + R cos θ`, and
`RiemannHypothesis.exists_integral_normSq_riemannZeta_le_uniform` bounds all of them by `C · b`
with one constant.

The centre is taken on the line `Re s = 3`, where `‖ζ‖ ≥ 1/2`
(`RiemannHypothesis.half_le_norm_riemannZeta_of_three_le_re`).

## Main results

* `log_norm_le_half_normSq` : `log ‖z‖ ≤ ‖z‖² / 2`.
* `circleAverage_log_norm_riemannZeta_le_circleAverage_normSq` : the pointwise comparison of the
  two circle averages.
* `exists_integral_circleAverage_log_norm_riemannZeta_le` : **the integral over `y ∈ [a, b]` of
  the circle average of `log ‖ζ‖` about `3 + i y` is `O(b)`**, uniformly for radii `R < 5/2`.
-/

noncomputable section

open Complex Real MeasureTheory Metric

namespace RiemannHypothesis

/-- `log x ≤ x² / 2` for every real `x ≥ 0` (and, with Lean's convention `log 0 = 0`, also at
`x = 0`).  Applied to `x = ‖z‖` this is the majorant used below. -/
theorem log_norm_le_half_normSq (z : ℂ) : Real.log ‖z‖ ≤ ‖z‖ ^ 2 / 2 := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]; simp
  · have := Real.log_le_sub_one_of_pos h
    nlinarith [sq_nonneg (‖z‖ - 1)]

/-- `ζ` is analytic away from its pole. -/
theorem analyticAt_riemannZeta' {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  (DifferentiableOn.analyticOnNhd
    (fun _z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    isOpen_compl_singleton) s hs

/-- `ζ` is meromorphic — indeed analytic — on every set avoiding the pole. -/
theorem meromorphicOn_riemannZeta {s : Set ℂ} (hs : (1 : ℂ) ∉ s) : MeromorphicOn riemannZeta s :=
  fun _z hz => (analyticAt_riemannZeta' (fun h => hs (h ▸ hz))).meromorphicAt

/-- For a centre `3 + i y` high enough up, the pole of `ζ` lies outside the closed ball of
radius `R < 5/2`. -/
theorem one_notMem_closedBall_of_le {y R : ℝ} (hy : 4 ≤ y) (hR : R < 5 / 2) :
    (1 : ℂ) ∉ closedBall ((3 : ℂ) + (y : ℂ) * I) R := by
  simp only [mem_closedBall, Complex.dist_eq, not_le]
  have h : ((1 : ℂ) - ((3 : ℂ) + (y : ℂ) * I)).im = -y := by simp
  have hb := Complex.abs_im_le_norm ((1 : ℂ) - ((3 : ℂ) + (y : ℂ) * I))
  rw [h, abs_neg, abs_of_nonneg (by linarith)] at hb
  linarith

/-- `ζ` is analytic on a neighbourhood of the closed ball of radius `R < 5/2` about `3 + i y`,
for `y ≥ 4`. -/
theorem analyticOnNhd_riemannZeta_closedBall {y R : ℝ} (hy : 4 ≤ y) (hR : R < 5 / 2) :
    AnalyticOnNhd ℂ riemannZeta (closedBall ((3 : ℂ) + (y : ℂ) * I) R) := fun _z hz =>
  analyticAt_riemannZeta' (fun h => one_notMem_closedBall_of_le hy hR (h ▸ hz))

/-- The circle average of `log ‖ζ‖` is at most the circle average of `‖ζ‖² / 2`. -/
theorem circleAverage_log_norm_riemannZeta_le_circleAverage_normSq {y R : ℝ} (hy : 4 ≤ y)
    (hR0 : 0 < R) (hR : R < 5 / 2) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) ((3 : ℂ) + (y : ℂ) * I) R
      ≤ circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R := by
  have habs : |R| = R := abs_of_pos hR0
  have hone : (1 : ℂ) ∉ sphere ((3 : ℂ) + (y : ℂ) * I) R := fun h =>
    one_notMem_closedBall_of_le hy hR (sphere_subset_closedBall h)
  have h1 : CircleIntegrable (fun z => Real.log ‖riemannZeta z‖) ((3 : ℂ) + (y : ℂ) * I) R :=
    circleIntegrable_log_norm_meromorphicOn
      (meromorphicOn_riemannZeta (s := sphere ((3 : ℂ) + (y : ℂ) * I) |R|) (by rwa [habs]))
  have h2 : CircleIntegrable (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    intro z hz
    have hz1 : z ≠ 1 := fun h => hone (h ▸ hz)
    exact ((analyticAt_riemannZeta' hz1).continuousAt.norm.pow 2).div_const 2 |>.continuousWithinAt
  exact circleAverage_mono h1 h2 fun x _ => log_norm_le_half_normSq _

/-! ### The integrand as a function of the two variables `(θ, y)` -/

/-- The integrand of the circle average, as a function of the angle `θ` and of the ordinate `y`
of the centre. -/
def circleIntegrandSq (R θ y : ℝ) : ℝ :=
  ‖riemannZeta (circleMap ((3 : ℂ) + (y : ℂ) * I) R θ)‖ ^ 2 / 2

/-- The point on the circle has ordinate at least `y - |R|`, hence is never the pole `1`
when `y ≥ 4` and `|R| < 5/2`. -/
theorem circleMap_ne_one {R θ y : ℝ} (hy : 4 ≤ y) (hR : |R| < 5 / 2) :
    circleMap ((3 : ℂ) + (y : ℂ) * I) R θ ≠ 1 := by
  intro h
  have him : (circleMap ((3 : ℂ) + (y : ℂ) * I) R θ).im = y + R * Real.sin θ := by
    simp [circleMap]
  have hb : |R * Real.sin θ| ≤ |R| := by
    rw [abs_mul]
    calc |R| * |Real.sin θ| ≤ |R| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg R)
      _ = |R| := mul_one _
  have := neg_abs_le (R * Real.sin θ)
  rw [h] at him
  simp only [Complex.one_im] at him
  linarith [hb, this]

/-- Joint continuity of the integrand on a box of ordinates bounded below by `4`. -/
theorem continuousOn_uncurry_circleIntegrandSq {R : ℝ} (hR : |R| < 5 / 2) {a b : ℝ} (ha : 4 ≤ a) :
    ContinuousOn (Function.uncurry fun θ y => circleIntegrandSq R θ y)
      (Set.Icc 0 (2 * π) ×ˢ Set.Icc a b) := by
  have hg : Continuous fun p : ℝ × ℝ => circleMap ((3 : ℂ) + (p.2 : ℂ) * I) R p.1 := by
    unfold circleMap
    fun_prop
  rintro ⟨θ, y⟩ ⟨-, hy⟩
  have hy4 : 4 ≤ y := le_trans ha hy.1
  have hne : circleMap ((3 : ℂ) + (y : ℂ) * I) R θ ≠ 1 := circleMap_ne_one hy4 hR
  have : ContinuousAt (Function.uncurry fun θ y => circleIntegrandSq R θ y) (θ, y) := by
    have h1 : ContinuousAt
        (fun p : ℝ × ℝ => riemannZeta (circleMap ((3 : ℂ) + (p.2 : ℂ) * I) R p.1)) (θ, y) :=
      ContinuousAt.comp (g := riemannZeta)
        (f := fun p : ℝ × ℝ => circleMap ((3 : ℂ) + (p.2 : ℂ) * I) R p.1)
        (analyticAt_riemannZeta' hne).continuousAt hg.continuousAt
    exact (h1.norm.pow 2).div_const 2
  exact this.continuousWithinAt

/-- Integrability of the integrand on the box `[0, 2π] × [a, b]`, as a function of the pair. -/
theorem integrable_uncurry_circleIntegrandSq {R : ℝ} (hR : |R| < 5 / 2) {a b : ℝ} (ha : 4 ≤ a) :
    Integrable (Function.uncurry fun θ y => circleIntegrandSq R θ y)
      ((volume.restrict (Set.Ioc 0 (2 * π))).prod (volume.restrict (Set.Ioc a b))) := by
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact (continuousOn_uncurry_circleIntegrandSq hR ha).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- The circle average written out as an interval integral in the angle. -/
theorem circleAverage_normSq_eq {R y : ℝ} :
    circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), circleIntegrandSq R θ y := by
  rw [circleAverage_def]
  simp [circleIntegrandSq, smul_eq_mul]

/-- The circle averages of `‖ζ‖² / 2` are integrable in the ordinate of the centre. -/
theorem intervalIntegrable_circleAverage_normSq_riemannZeta {R : ℝ} (hR0 : 0 < R)
    (hR : R < 5 / 2) {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun y : ℝ => circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
      volume a b := by
  have hRabs : |R| < 5 / 2 := by rwa [abs_of_pos hR0]
  have hint := (integrable_uncurry_circleIntegrandSq hRabs (a := a) (b := b) ha).integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  have : IntegrableOn
      (fun y : ℝ => ∫ θ in Set.Ioc 0 (2 * π), circleIntegrandSq R θ y) (Set.Ioc a b) volume := hint
  have h2 : (fun y : ℝ =>
      circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
      = fun y : ℝ => (2 * π)⁻¹ * ∫ θ in Set.Ioc 0 (2 * π), circleIntegrandSq R θ y := by
    funext y
    rw [circleAverage_normSq_eq, intervalIntegral.integral_of_le hpi]
  rw [h2]
  exact this.const_mul _

/-- **The vertical integral of the circle averages of `‖ζ‖² / 2` is `O(b)`.**  This is the
Bohr–Landau mean square, transported from vertical lines to circles. -/
theorem exists_integral_circleAverage_normSq_riemannZeta_le {R : ℝ} (hR0 : 0 < R)
    (hR : R < 5 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 4 ≤ a → a ≤ b →
      (∫ y in a..b,
          circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
        ≤ C * b := by
  have hRabs : |R| < 5 / 2 := by rwa [abs_of_pos hR0]
  set σ₀ : ℝ := min (3 - R) (3 / 4) with hσ₀
  have hσ₀0 : 1 / 2 < σ₀ := lt_min (by linarith) (by norm_num)
  have hσ₀1 : σ₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C₀, hC₀, hbd⟩ := integral_normSq_riemannZeta_le_uniform_Icc hσ₀0 hσ₀1
  refine ⟨C₀ + 1, by linarith, fun a b ha hab => ?_⟩
  have hb4 : (4 : ℝ) ≤ b := le_trans ha hab
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  -- the inner estimate, for a fixed angle
  have hinner : ∀ θ : ℝ, (∫ y in a..b, circleIntegrandSq R θ y) ≤ C₀ / 2 * (b + 5 / 2) := by
    intro θ
    have hs : ∀ y : ℝ, circleMap ((3 : ℂ) + (y : ℂ) * I) R θ
        = ((3 + R * Real.cos θ : ℝ) : ℂ) + ((y + R * Real.sin θ : ℝ) : ℂ) * I := by
      intro y
      simp only [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hEq : (∫ y in a..b, circleIntegrandSq R θ y)
        = 1 / 2 * ∫ y in a..b,
            ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ)
              + ((y + R * Real.sin θ : ℝ) : ℂ) * I)‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [circleIntegrandSq, hs y]
      ring
    have hshift : (∫ y in a..b,
          ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ)
            + ((y + R * Real.sin θ : ℝ) : ℂ) * I)‖ ^ 2)
        = ∫ u in (a + R * Real.sin θ)..(b + R * Real.sin θ),
            ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 := by
      rw [← intervalIntegral.integral_comp_add_right
        (fun u : ℝ => ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2)
        (R * Real.sin θ)]
    have hsin : |R * Real.sin θ| ≤ |R| := by
      rw [abs_mul]
      calc |R| * |Real.sin θ| ≤ |R| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg R)
        _ = |R| := mul_one _
    have hlow : (1 : ℝ) ≤ a + R * Real.sin θ := by
      have := neg_abs_le (R * Real.sin θ)
      have h2 : |R| < 5 / 2 := hRabs
      linarith
    have hcos : σ₀ ≤ 3 + R * Real.cos θ := by
      have hc : |R * Real.cos θ| ≤ |R| := by
        rw [abs_mul]
        calc |R| * |Real.cos θ| ≤ |R| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg R)
          _ = |R| := mul_one _
      have hR' : |R| = R := abs_of_pos hR0
      have := neg_abs_le (R * Real.cos θ)
      have : σ₀ ≤ 3 - R := min_le_left _ _
      have h3 : -R ≤ R * Real.cos θ := by
        have := neg_abs_le (R * Real.cos θ)
        rw [hR'] at hc
        linarith
      linarith
    have hle := hbd (3 + R * Real.cos θ) hcos (a + R * Real.sin θ) (b + R * Real.sin θ) hlow
      (by linarith)
    have hR' : |R| = R := abs_of_pos hR0
    have hub : b + R * Real.sin θ ≤ b + 5 / 2 := by
      have := le_abs_self (R * Real.sin θ)
      rw [hR'] at hsin
      linarith
    have hC₀nn : (0 : ℝ) ≤ C₀ := hC₀.le
    rw [hEq, hshift]
    calc 1 / 2 * ∫ u in (a + R * Real.sin θ)..(b + R * Real.sin θ),
          ‖riemannZeta (((3 + R * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2
        ≤ 1 / 2 * (C₀ * (b + R * Real.sin θ)) := by linarith
      _ ≤ C₀ / 2 * (b + 5 / 2) := by nlinarith
  -- Fubini and the outer estimate
  have hswap : (∫ y in a..b, ∫ θ in (0 : ℝ)..(2 * π), circleIntegrandSq R θ y)
      = ∫ θ in (0 : ℝ)..(2 * π), ∫ y in a..b, circleIntegrandSq R θ y := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hpi]
    have : ∀ y : ℝ, (∫ θ in (0 : ℝ)..(2 * π), circleIntegrandSq R θ y)
        = ∫ θ in Set.Ioc 0 (2 * π), circleIntegrandSq R θ y := fun y =>
      intervalIntegral.integral_of_le hpi
    simp only [this]
    have : ∀ θ : ℝ, (∫ y in a..b, circleIntegrandSq R θ y)
        = ∫ y in Set.Ioc a b, circleIntegrandSq R θ y := fun θ =>
      intervalIntegral.integral_of_le hab
    simp only [this]
    exact (integral_integral_swap (integrable_uncurry_circleIntegrandSq hRabs ha)).symm
  have hrewrite : (∫ y in a..b,
        circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
      = (2 * π)⁻¹ * ∫ y in a..b, ∫ θ in (0 : ℝ)..(2 * π), circleIntegrandSq R θ y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y _ => circleAverage_normSq_eq
  have houter : (∫ θ in (0 : ℝ)..(2 * π), ∫ y in a..b, circleIntegrandSq R θ y)
      ≤ 2 * π * (C₀ / 2 * (b + 5 / 2)) := by
    have hintθ : IntervalIntegrable
        (fun θ : ℝ => ∫ y in a..b, circleIntegrandSq R θ y) volume 0 (2 * π) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
      have := (integrable_uncurry_circleIntegrandSq hRabs (a := a) (b := b) ha).integral_prod_left
      have h2 : (fun θ : ℝ => ∫ y in a..b, circleIntegrandSq R θ y)
          = fun θ : ℝ => ∫ y in Set.Ioc a b, circleIntegrandSq R θ y := by
        funext θ
        exact intervalIntegral.integral_of_le hab
      rw [h2]
      exact this
    have := intervalIntegral.integral_mono_on hpi hintθ
      (intervalIntegrable_const (c := C₀ / 2 * (b + 5 / 2))) (fun θ _ => hinner θ)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact this
  rw [hrewrite]
  have hpipos : (0 : ℝ) < 2 * π := by positivity
  have hstep : (2 * π)⁻¹ * (∫ y in a..b, ∫ θ in (0 : ℝ)..(2 * π), circleIntegrandSq R θ y)
      ≤ (2 * π)⁻¹ * (2 * π * (C₀ / 2 * (b + 5 / 2))) := by
    rw [hswap]
    exact mul_le_mul_of_nonneg_left houter (by positivity)
  have hsimp : (2 * π)⁻¹ * (2 * π * (C₀ / 2 * (b + 5 / 2))) = C₀ / 2 * (b + 5 / 2) := by
    field_simp
  rw [hsimp] at hstep
  refine hstep.trans ?_
  nlinarith [hC₀.le, hb4]

end RiemannHypothesis
