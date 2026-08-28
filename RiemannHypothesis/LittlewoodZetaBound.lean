/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZetaLittlewood
import RiemannHypothesis.StripMeanSquareUniform
import RiemannHypothesis.ZeroCountLocal
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Bounding the terms of Littlewood's lemma for `ζ`

`RiemannHypothesis.ZetaLittlewood` proves Littlewood's lemma for `ζ` as an *identity*: for a
rectangle on whose border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − σ) = ∫ (log ‖ζ‖ left − log ‖ζ‖ right) + (bottom arg) − (top arg)
  + (width) · (right arg)`.

To turn the identity into a zero-density estimate one has to bound each term on the right.  This
file bounds all of them except the two horizontal (argument) terms, so that the obstruction to a
density theorem is isolated in a single, explicitly written quantity.

## Main results

* `analyticOnNhd_riemannZeta_rectangle_of_im_pos`, `zeta_littlewood_lemma_above` — Littlewood's
  lemma for `ζ` on a rectangle lying strictly above the real axis.  The rectangle no longer has
  to lie inside the critical strip, so its right side may be taken at the abscissa `3`, where
  `ζ` is close to `1`.
* `abs_sub_lt_pi_of_forall_cos_ne_zero` — a continuous real function on an interval whose cosine
  never vanishes moves by less than `π`: an interval of length `≥ π` meets `π/2 + πℤ`.
* `abs_im_VIntegral_logDeriv_riemannZeta_lt_pi` — hence the variation of the argument of `ζ`
  along *any* vertical segment of the line `re s = 3` is less than `π`: on that line
  `‖ζ − 1‖ ≤ 1/2`, so `re ζ > 0` and no full turn is possible.
* `abs_integral_log_norm_riemannZeta_three_le` — on the line `re s = 3`, `1/2 ≤ ‖ζ‖ ≤ 2`, so the
  right-hand log-modulus term is at most `log 2` per unit of height.
* `integral_posLog_norm_riemannZeta_le` — the positive part of `log ‖ζ‖` on a vertical line with
  `σ ≥ σ₀ > 1/2` has mean `O(1)`, by `log⁺ x ≤ x²/2` and the uniform mean square of `ζ`.
* `zeta_littlewood_bound` — the resulting inequality, and `exists_zeta_littlewood_bound` — its
  uniform form, in which the only terms not bounded by `O(T₂)` are the two horizontal argument
  terms.

Nothing here is conditional, and nothing here yields a density theorem on its own: bounding the
two horizontal terms is exactly the classical estimate `S(t) = O(log t)` for the argument of `ζ`,
which is not formalized in this repository.
-/

noncomputable section

open Complex Real MeasureTheory Set Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

/-! ## A continuous function whose cosine does not vanish moves by less than `π` -/

/-- Every closed interval of length at least `π` contains a zero of the cosine. -/
theorem exists_cos_eq_zero_of_pi_le {a b : ℝ} (hab : a + π ≤ b) :
    ∃ x ∈ Icc a b, Real.cos x = 0 := by
  have hpi : 0 < π := Real.pi_pos
  set k : ℤ := ⌈a / π - 1 / 2⌉ with hk
  have h1 : a / π - 1 / 2 ≤ (k : ℝ) := Int.le_ceil _
  have h2 : (k : ℝ) < a / π - 1 / 2 + 1 := Int.ceil_lt_add_one _
  have hd : a / π * π = a := div_mul_cancel₀ _ (ne_of_gt hpi)
  have e1 : a ≤ ((k : ℝ) + 1 / 2) * π := by nlinarith
  have e2 : ((k : ℝ) + 1 / 2) * π < a + π := by nlinarith
  exact ⟨(2 * (k : ℝ) + 1) * π / 2, ⟨by nlinarith, by nlinarith⟩,
    Real.cos_eq_zero_iff.2 ⟨k, rfl⟩⟩

/-- **A continuous real function whose cosine never vanishes moves by less than `π`.**  If it
moved by `π` or more, the intermediate value theorem would produce a point of its interval of
values at which the cosine vanishes. -/
theorem abs_sub_lt_pi_of_forall_cos_ne_zero {theta : ℝ → ℝ} {c d : ℝ}
    (hc : ContinuousOn theta [[c, d]]) (h : ∀ t ∈ [[c, d]], Real.cos (theta t) ≠ 0) :
    |theta d - theta c| < π := by
  by_contra hcon
  rw [not_lt] at hcon
  have hle : min (theta c) (theta d) + π ≤ max (theta c) (theta d) := by
    rcases abs_cases (theta d - theta c) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      simp only [min_def, max_def] <;> split_ifs <;> linarith [hcon, he]
  obtain ⟨x, hx, hcosx⟩ := exists_cos_eq_zero_of_pi_le hle
  have hxmem : x ∈ [[theta c, theta d]] := by simpa [Set.uIcc] using hx
  obtain ⟨t, ht, hxt⟩ := intermediate_value_uIcc hc hxmem
  exact h t ht (hxt ▸ hcosx)

/-! ## `ζ` on the line `re s = 3` -/

/-- For `re s ≥ 3` the real part of `ζ` is at least `1/2`; in particular `ζ` stays in the right
half-plane, so its argument cannot make a full turn. -/
theorem half_le_re_riemannZeta_of_three_le_re {s : ℂ} (hs : 3 ≤ s.re) :
    1 / 2 ≤ (riemannZeta s).re := by
  have h := norm_riemannZeta_sub_one_le_half_of_three_le_re hs
  have h2 : |(riemannZeta s - 1).re| ≤ ‖riemannZeta s - 1‖ := Complex.abs_re_le_norm _
  have h3 : (riemannZeta s - 1).re = (riemannZeta s).re - 1 := by simp
  rw [h3] at h2
  have h4 := abs_le.mp h2
  linarith [h4.1]

/-- **The argument of `ζ` moves by less than `π` along the line `re s = 3`.**  On that line
`re ζ ≥ 1/2`, so a continuous branch of the argument stays inside a single interval on which the
cosine is positive. -/
theorem abs_im_VIntegral_logDeriv_riemannZeta_lt_pi (c d : ℝ) :
    |(VIntegral (logDeriv riemannZeta) (3 : ℝ) c d).im| < π := by
  have hre : ∀ t : ℝ, (3 : ℝ) ≤ (((3 : ℝ) : ℂ) + t * I).re := by intro t; simp
  have hanal : ∀ t ∈ [[c, d]], AnalyticAt ℂ riemannZeta (((3 : ℝ) : ℂ) + t * I) := by
    intro t _
    have hne : (((3 : ℝ) : ℂ) + t * I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
    exact DifferentiableOn.analyticAt (s := {u : ℂ | u ≠ 1})
      (fun u hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
      (isOpen_ne.mem_nhds hne)
  have h0 : ∀ t ∈ [[c, d]], riemannZeta (((3 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t _ hz
    have h := half_le_norm_riemannZeta_of_three_le_re (hre t)
    rw [hz] at h
    simp at h
    linarith
  obtain ⟨theta, hthetac, hthetap, hthetai⟩ := exists_continuousOn_arg_vertical hanal h0
  have hcos : ∀ t ∈ [[c, d]], Real.cos (theta t) ≠ 0 := by
    intro t ht hzero
    have hp := hthetap t ht
    have hree : (riemannZeta (((3 : ℝ) : ℂ) + t * I)).re
        = ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖ * Real.cos (theta t) := by
      conv_lhs => rw [hp]
      simp [Complex.exp_mul_I, Complex.cos_ofReal_re]
    have hhalf := half_le_re_riemannZeta_of_three_le_re (hre t)
    rw [hzero, mul_zero] at hree
    linarith
  have hlt := abs_sub_lt_pi_of_forall_cos_ne_zero hthetac hcos
  rw [hthetai c left_mem_uIcc d right_mem_uIcc] at hlt
  exact hlt

/-- On the line `re s = 3` the log-modulus of `ζ` is at most `log 2` in absolute value. -/
theorem abs_log_norm_riemannZeta_le_log_two_of_three_le_re {s : ℂ} (hs : 3 ≤ s.re) :
    |Real.log ‖riemannZeta s‖| ≤ Real.log 2 := by
  have hlow : 1 / 2 ≤ ‖riemannZeta s‖ := half_le_norm_riemannZeta_of_three_le_re hs
  have hup : ‖riemannZeta s‖ ≤ 2 := norm_riemannZeta_le_two_of_two_le_re (by linarith)
  rw [abs_le]
  refine ⟨?_, Real.log_le_log (by linarith) hup⟩
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlow
  rw [one_div, Real.log_inv] at h
  linarith

/-- The log-modulus term of the right side of the rectangle is at most `log 2` per unit of
height. -/
theorem abs_integral_log_norm_riemannZeta_three_le {c d : ℝ} (hcd : c ≤ d) :
    |∫ t in c..d, Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖| ≤ Real.log 2 * (d - c) := by
  have hb : ∀ t ∈ Set.uIoc c d,
      ‖Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖‖ ≤ Real.log 2 := by
    intro t _
    simpa using abs_log_norm_riemannZeta_le_log_two_of_three_le_re
      (s := ((3 : ℝ) : ℂ) + t * I) (by simp)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at h
  exact h

/-! ## The positive part of `log ‖ζ‖` on a vertical line in the strip -/

/-- `log⁺` is continuous: near `0` it vanishes identically. -/
theorem continuous_posLog : Continuous Real.posLog := by
  have h : Real.posLog = fun x : ℝ => Real.log (max 1 |x|) := by
    funext x
    rcases le_or_gt |x| 1 with hx | hx
    · rw [(Real.posLog_eq_zero_iff x).2 hx, max_eq_left hx, Real.log_one]
    · rw [Real.posLog_eq_log hx.le, max_eq_right hx.le, Real.log_abs]
  rw [h]
  exact (continuous_const.max continuous_abs).log fun x => by
    have hle := le_max_left 1 |x|
    intro hzero
    rw [hzero] at hle
    linarith

/-- `log⁺ x ≤ x²/2`: the elementary inequality behind the bound for the first moment of
`log ‖ζ‖`. -/
theorem posLog_le_half_sq (x : ℝ) : Real.posLog x ≤ x ^ 2 / 2 := by
  rcases le_or_gt |x| 1 with hx | hx
  · rw [(Real.posLog_eq_zero_iff x).2 hx]; positivity
  · rw [Real.posLog_eq_log hx.le, ← Real.log_abs]
    have h1 : Real.log |x| ≤ |x| - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1)]

/-- `t ↦ ζ(σ + i t)` is continuous on `[1, ∞)`, for every abscissa `σ`: such a line misses the
pole at `s = 1`. -/
theorem continuousOn_riemannZeta_line (σ : ℝ) :
    ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) (Set.Ici 1) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hline : ContinuousAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
  exact (ContinuousAt.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (g := riemannZeta)
    ((differentiableAt_riemannZeta hne).continuousAt) hline).continuousWithinAt

/-- **The mean of `log⁺ ‖ζ‖` on a vertical line with `σ ≥ σ₀ > 1/2` is `O(1)`**, by
`log⁺ x ≤ x² / 2` and the uniform mean square of `ζ`. -/
theorem integral_posLog_norm_riemannZeta_le {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ t in a..b, Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) ≤ C * b := by
  obtain ⟨C, hC, hbd⟩ := integral_normSq_riemannZeta_le_uniform_Icc h0 h1
  refine ⟨C / 2, by positivity, fun σ hσ a b ha hab => ?_⟩
  have hsub : Set.uIcc a b ⊆ Set.Ici 1 := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => le_trans ha ht.1
  have hcont : ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) (Set.uIcc a b) :=
    (continuousOn_riemannZeta_line σ).mono hsub
  have hi1 : IntervalIntegrable
      (fun t : ℝ => Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) volume a b :=
    (continuous_posLog.comp_continuousOn hcont.norm).intervalIntegrable
  have hi2 : IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / 2) volume a b :=
    ((hcont.norm.pow 2).div_const 2).intervalIntegrable
  have hle : ∀ t ∈ Set.Icc a b, Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / 2 := fun t _ => posLog_le_half_sq _
  refine (intervalIntegral.integral_mono_on hab hi1 hi2 hle).trans ?_
  rw [intervalIntegral.integral_div]
  have hb := hbd σ hσ a b ha hab
  linarith

/-! ## Littlewood's lemma above the real axis -/

variable {z w : ℂ}

/-- `ζ` is analytic on a neighbourhood of any rectangle lying strictly above the real axis: the
only singularity of `ζ` is the pole at `s = 1`, whose imaginary part is `0`. -/
theorem analyticOnNhd_riemannZeta_rectangle_of_im_pos (hz : 0 < z.im) (him : z.im ≤ w.im) :
    AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
  intro s hs
  have hmem : s.im ∈ [[z.im, w.im]] := by simpa using hs.2
  rw [Set.uIcc_of_le him] at hmem
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hmem
    simp at hmem
    linarith [hmem.1]
  exact DifferentiableOn.analyticAt (s := {u : ℂ | u ≠ 1})
    (fun u hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_ne.mem_nhds h1)

/-- **Littlewood's lemma for `ζ` on a rectangle above the real axis.**  Unlike
`zeta_littlewood_lemma`, the rectangle is not required to lie inside the critical strip; it is
required to lie strictly above the real axis, which is what keeps it away from the pole. -/
theorem zeta_littlewood_lemma_above (hz : 0 < z.im) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  littlewood_lemma hre him (analyticOnNhd_riemannZeta_rectangle_of_im_pos hz him) hborder

/-! ## The resulting bound -/

/-- **Littlewood's lemma for `ζ`, as an inequality.**  For `σ < 1` and `1 ≤ T₁ ≤ T₂`, on a
rectangle `[σ, 3] × [T₁, T₂]` on whose border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − σ) ≤ ∫ log⁺ ‖ζ(σ + i t)‖ dt + log 2 · (T₂ − T₁)
  + (bottom argument term) − (top argument term) + (3 − σ) π`.

The first two terms on the right are `O(T₂)` when `σ` stays above `1/2` (see
`exists_zeta_littlewood_bound`); the two argument terms are the ones this file does not
bound. -/
theorem zeta_littlewood_bound {σ T₁ T₂ : ℝ} (hσ1 : σ < 1) (hT1 : 1 ≤ T₁) (hT : T₁ ≤ T₂)
    (hborder : ∀ s ∈ RectangleBorder ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I),
      riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I),
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ)
      ≤ (∫ t in T₁..T₂, Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
        + Real.log 2 * (T₂ - T₁)
        + (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₁).im)
        - (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₂).im)
        + (3 - σ) * Real.pi := by
  set z : ℂ := (σ : ℂ) + T₁ * I with hzdef
  set w : ℂ := ((3 : ℝ) : ℂ) + T₂ * I with hwdef
  have hzre : z.re = σ := by simp [hzdef]
  have hzim : z.im = T₁ := by simp [hzdef]
  have hwre : w.re = 3 := by simp [hwdef]
  have hwim : w.im = T₂ := by simp [hwdef]
  have hid := zeta_littlewood_lemma_above (z := z) (w := w) (by rw [hzim]; linarith)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; exact hT) hborder
  rw [hzre, hzim, hwre, hwim] at hid
  rw [hid]
  -- the two vertical sides carry no zero of `ζ`
  have hsub : Set.uIcc T₁ T₂ ⊆ Set.Ici 1 := by
    rw [Set.uIcc_of_le hT]
    exact fun t ht => le_trans hT1 ht.1
  have hzeroL : ∀ t ∈ [[T₁, T₂]], riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
    intro t ht
    have h := hborder _ (mem_rectangleBorder_left (z := z) (w := w)
      (by rw [hzim, hwim]; exact ht))
    rwa [hzre] at h
  have hzeroR : ∀ t ∈ [[T₁, T₂]], riemannZeta (((3 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t _ hzero
    have h := half_le_norm_riemannZeta_of_three_le_re
      (s := ((3 : ℝ) : ℂ) + t * I) (by simp)
    rw [hzero] at h
    simp at h
    linarith
  -- both log-moduli are continuous, hence integrable, along the two vertical sides
  have hcontL : ContinuousOn (fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
      [[T₁, T₂]] :=
    (((continuousOn_riemannZeta_line σ).mono hsub).norm).log
      fun t ht => norm_ne_zero_iff.mpr (hzeroL t ht)
  have hcontR : ContinuousOn
      (fun t : ℝ => Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖) [[T₁, T₂]] :=
    (((continuousOn_riemannZeta_line 3).mono hsub).norm).log
      fun t ht => norm_ne_zero_iff.mpr (hzeroR t ht)
  have hiL : IntervalIntegrable
      (fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    hcontL.intervalIntegrable
  have hiR : IntervalIntegrable
      (fun t : ℝ => Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    hcontR.intervalIntegrable
  have hiP : IntervalIntegrable
      (fun t : ℝ => Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    (continuous_posLog.comp_continuousOn
      (((continuousOn_riemannZeta_line σ).mono hsub).norm)).intervalIntegrable
  have hsplit : (∫ t in T₁..T₂, (Real.log ‖riemannZeta ((σ : ℂ) + t * I)‖
        - Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖))
      = (∫ t in T₁..T₂, Real.log ‖riemannZeta ((σ : ℂ) + t * I)‖)
        - ∫ t in T₁..T₂, Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖ :=
    intervalIntegral.integral_sub hiL hiR
  have hlogle : (∫ t in T₁..T₂, Real.log ‖riemannZeta ((σ : ℂ) + t * I)‖)
      ≤ ∫ t in T₁..T₂, Real.posLog ‖riemannZeta ((σ : ℂ) + t * I)‖ := by
    refine intervalIntegral.integral_mono_on hT hiL hiP fun t _ => ?_
    rw [Real.posLog_def]
    exact le_max_right _ _
  have hright : -(∫ t in T₁..T₂, Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * I)‖)
      ≤ Real.log 2 * (T₂ - T₁) :=
    le_trans (neg_le_abs _) (abs_integral_log_norm_riemannZeta_three_le hT)
  -- the argument along the right side moves by less than `π`
  have hV : (VIntegral (logDeriv riemannZeta) 3 T₁ T₂).im ≤ Real.pi :=
    le_of_lt (lt_of_abs_lt (abs_im_VIntegral_logDeriv_riemannZeta_lt_pi T₁ T₂))
  have hD : (3 - σ) * (VIntegral (logDeriv riemannZeta) 3 T₁ T₂).im ≤ (3 - σ) * Real.pi := by
    have h3 : (0 : ℝ) < 3 - σ := by linarith
    nlinarith
  rw [hsplit]
  linarith

/-- **The uniform form of `zeta_littlewood_bound`.**  For every `σ₀ > 1/2` there is a constant
`C` such that, for every `σ ≥ σ₀` below `1` and every rectangle `[σ, 3] × [T₁, T₂]` above the
height `1` on whose border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − σ) ≤ C · T₂ + (bottom argument term) − (top argument term)`.

Only the two horizontal argument terms are left unbounded: bounding them by `O(log T₂)` is the
classical estimate for `S(t)`, and would turn this inequality into a zero-density bound. -/
theorem exists_zeta_littlewood_bound {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → ∀ T₁ T₂ : ℝ, 1 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I), riemannZeta s ≠ 0) →
      2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ)
        ≤ C * T₂
          + (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₁).im)
          - (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₂).im) := by
  obtain ⟨C, hC, hbd⟩ := integral_posLog_norm_riemannZeta_le h0 h1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C + Real.log 2 + 3 * Real.pi, by positivity,
    fun σ hσ hσ1 T₁ T₂ hT1 hT hborder => ?_⟩
  have hσ0 : 1 / 2 < σ := lt_of_lt_of_le h0 hσ
  have hT2 : (1 : ℝ) ≤ T₂ := le_trans hT1 hT
  have hb := zeta_littlewood_bound hσ1 hT1 hT hborder
  have hp := hbd σ hσ T₁ T₂ hT1 hT
  have h1' : Real.log 2 * (T₂ - T₁) ≤ Real.log 2 * T₂ := by nlinarith
  have h2' : (3 - σ) * Real.pi ≤ 3 * Real.pi * T₂ := by nlinarith
  linarith

end RiemannHypothesis
