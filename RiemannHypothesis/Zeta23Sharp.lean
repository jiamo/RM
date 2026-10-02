/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeta23Verification

/-!
# The two-thirds theorem in absolute form, with the sharp constant

`RiemannHypothesis.Zeta23Verification` turns the ratio statements of the vendored two-thirds
theorem into absolute counts, but deliberately loses a factor: it proves at least
`(T/8π)·log T` zeroes on the critical line in `(T, 2T]`, where the argument actually gives
`(2/3 − ε)·(T/2π)·log T`.  This file removes that loss.

* `windowCount_asymptotic` — `N(T, 2T) ~ (T/2π)·log T`: for every `ε > 0` and all large `T`,
  `(1 − ε)(T/2π) log T ≤ N(T, 2T) ≤ (1 + ε)(T/2π) log T`;
* `tendsto_windowCount_div` — the same as a limit, `N(T, 2T) / ((T/2π) log T) → 1`;
* `eventually_windowCountOnLine_ge_sharp` — Theorem A in absolute form with the sharp constant:
  for every `ε > 0`, eventually at least `(2/3 − ε)(T/2π) log T` **distinct** zeroes of `ζ` on
  the critical line have ordinate in `(T, 2T]`;
* `eventually_windowCountSimpleOnLine_ge_sharp` — the same for *simple* zeroes on the line
  (Theorem B);
* `eventually_windowCountDistinct_ge_sharp` — at least `(5/6 − ε)(T/2π) log T` distinct
  nontrivial zeroes in the window (Theorem C).

The inputs are exactly those of `Zeta23Verification`: the Riemann–von Mangoldt formula
`windowCount_sub_mainTerm_le` and the unconditional ratio theorems of
`RiemannHypothesis.Zeta23Bridge`.  Nothing is assumed.
-/

noncomputable section

open Filter Real
open scoped Topology

namespace RiemannHypothesis

/-- The leading term of `N(T, 2T)`: `(T/2π)·log T`. -/
def windowLeadingTerm (T : ℝ) : ℝ := T / (2 * π) * Real.log T

/-- `windowMainTerm T = (T/2π)(log T − c₀)` with `c₀ = log(2π) + 1 − 2 log 2`. -/
private lemma windowMainTerm_eq_sub (T : ℝ) (hT : 0 < T) :
    windowMainTerm T = windowLeadingTerm T
      - T / (2 * π) * (Real.log (2 * π) + 1 - 2 * Real.log 2) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [windowMainTerm, windowLeadingTerm, Real.log_div hT.ne' hpi.ne']
  ring

/-- The lower-order terms are eventually small against the leading term: for every `ε > 0`,
eventually `(T/2π)|c₀| + C log T ≤ ε·(T/2π) log T`. -/
private lemma eventually_error_le (C c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, T / (2 * π) * |c| + |C| * Real.log T ≤ ε * windowLeadingTerm T := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.exp (2 * |c| / ε)),
    eventually_ge_atTop (2 * π * (2 * |C| / ε))] with T hT1 hTexp hTC
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog : 2 * |c| / ε ≤ Real.log T := by
    have h1 : Real.log (Real.exp (2 * |c| / ε)) ≤ Real.log T :=
      Real.log_le_log (Real.exp_pos _) hTexp
    simpa using h1
  have hA : 2 * |C| / ε ≤ T / (2 * π) := by
    rw [le_div_iff₀ hpi]; linarith
  have hA0 : 0 ≤ T / (2 * π) := by positivity
  have h1 : 2 * |c| ≤ ε * Real.log T := by
    have := mul_le_mul_of_nonneg_left hlog hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have h2 : 2 * |C| ≤ ε * (T / (2 * π)) := by
    have := mul_le_mul_of_nonneg_left hA hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have e1 : T / (2 * π) * (2 * |c|) ≤ T / (2 * π) * (ε * Real.log T) :=
    mul_le_mul_of_nonneg_left h1 hA0
  have e2 : 2 * |C| * Real.log T ≤ ε * (T / (2 * π)) * Real.log T :=
    mul_le_mul_of_nonneg_right h2 hlog0
  rw [windowLeadingTerm]
  nlinarith [e1, e2]

/-- **Riemann–von Mangoldt, leading-order form.**  For every `ε > 0` and all large `T`,
`(1 − ε)(T/2π) log T ≤ N(T, 2T) ≤ (1 + ε)(T/2π) log T`. -/
theorem windowCount_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (1 - ε) * windowLeadingTerm T ≤ (windowCount T (2 * T) : ℝ) ∧
      (windowCount T (2 * T) : ℝ) ≤ (1 + ε) * windowLeadingTerm T := by
  obtain ⟨C, T₀, hC⟩ := windowCount_sub_mainTerm_le
  set c₀ : ℝ := Real.log (2 * π) + 1 - 2 * Real.log 2
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ),
    eventually_error_le C c₀ hε] with T hT hT1 herr
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hA0 : 0 ≤ T / (2 * π) := by positivity
  have hb := abs_le.mp (hC T hT)
  rw [windowMainTerm_eq_sub T hT0] at hb
  have hc1 : T / (2 * π) * c₀ ≤ T / (2 * π) * |c₀| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hA0
  have hc2 : -(T / (2 * π) * |c₀|) ≤ T / (2 * π) * c₀ := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le c₀) hA0
    linarith
  have hC1 : C * Real.log T ≤ |C| * Real.log T :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
  have hC2 : -(|C| * Real.log T) ≤ C * Real.log T := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le C) hlog0
    linarith
  constructor <;> nlinarith [hb.1, hb.2]

/-- **Riemann–von Mangoldt as a limit**: `N(T, 2T) / ((T/2π) log T) → 1`. -/
theorem tendsto_windowCount_div :
    Tendsto (fun T => (windowCount T (2 * T) : ℝ) / windowLeadingTerm T) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : ∀ᶠ T in atTop, 0 < windowLeadingTerm T := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact mul_pos (by positivity) (Real.log_pos hT)
  filter_upwards [windowCount_asymptotic (half_pos hε), hpos] with T hT hL
  have h1 : (windowCount T (2 * T) : ℝ) / windowLeadingTerm T ≤ 1 + ε / 2 := by
    rw [div_le_iff₀ hL]; exact hT.2
  have h2 : 1 - ε / 2 ≤ (windowCount T (2 * T) : ℝ) / windowLeadingTerm T := by
    rw [le_div_iff₀ hL]; exact hT.1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- From a ratio statement `(c − ε) N ≤ M` and the asymptotic of `N`, an absolute lower bound
`(c − ε)(T/2π) log T ≤ M` for every `ε > 0`, provided `0 < c ≤ 1`. -/
private lemma eventually_ge_of_ratio {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (M : ℝ → ℝ)
    (hratio : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (windowCount T (2 * T) : ℝ) ≤ M T)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (c - ε) * windowLeadingTerm T ≤ M T := by
  obtain ⟨T₁, hT₁⟩ := hratio (min (ε / 2) (c / 2)) (lt_min (half_pos hε) (half_pos hc))
  filter_upwards [windowCount_asymptotic (half_pos hε), eventually_ge_atTop T₁,
    eventually_ge_atTop (1 : ℝ)] with T hN hT hT1
  have hL : 0 ≤ windowLeadingTerm T :=
    mul_nonneg (by positivity) (Real.log_nonneg hT1)
  set δ := min (ε / 2) (c / 2) with hδ
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ c / 2 := min_le_right _ _
  have hcd : 0 ≤ c - δ := by linarith
  have h := hT₁ T hT
  have hNlow : (1 - ε / 2) * windowLeadingTerm T ≤ (windowCount T (2 * T) : ℝ) := hN.1
  have step : (c - δ) * ((1 - ε / 2) * windowLeadingTerm T) ≤
      (c - δ) * (windowCount T (2 * T) : ℝ) := mul_le_mul_of_nonneg_left hNlow hcd
  -- `(c − δ)(1 − ε/2) ≥ c − ε`, since `δ ≤ ε/2` and `c ≤ 1`
  have hδ0 : 0 ≤ δ := le_min (by linarith) (by linarith)
  have hcoef : c - ε ≤ (c - δ) * (1 - ε / 2) := by
    nlinarith [mul_nonneg hδ0 hε.le, mul_le_mul_of_nonneg_right hc1 hε.le]
  have := mul_le_mul_of_nonneg_right hcoef hL
  nlinarith

/-- **Theorem A in absolute form, sharp constant.**  For every `ε > 0` and all large `T` there
are at least `(2/3 − ε)·(T/2π)·log T` *distinct* zeroes of `ζ` on the critical line with ordinate
in `(T, 2T]`. -/
theorem eventually_windowCountOnLine_ge_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (2 / 3 - ε) * windowLeadingTerm T ≤ (windowCountOnLine T (2 * T) : ℝ) :=
  eventually_ge_of_ratio (by norm_num) (by norm_num) _ two_thirds_on_critical_line hε

/-- **Theorem B in absolute form, sharp constant.**  For every `ε > 0` and all large `T` there
are at least `(2/3 − ε)·(T/2π)·log T` *simple* zeroes of `ζ` on the critical line with ordinate
in `(T, 2T]`. -/
theorem eventually_windowCountSimpleOnLine_ge_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (2 / 3 - ε) * windowLeadingTerm T ≤ (windowCountSimpleOnLine T (2 * T) : ℝ) :=
  eventually_ge_of_ratio (by norm_num) (by norm_num) _ two_thirds_simple_on_critical_line hε

/-- **Theorem C in absolute form, sharp constant.**  For every `ε > 0` and all large `T` there
are at least `(5/6 − ε)·(T/2π)·log T` *distinct* nontrivial zeroes of `ζ` with ordinate in
`(T, 2T]`. -/
theorem eventually_windowCountDistinct_ge_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (5 / 6 - ε) * windowLeadingTerm T ≤ (windowCountDistinct T (2 * T) : ℝ) :=
  eventually_ge_of_ratio (by norm_num) (by norm_num) _ five_sixths_distinct hε

end RiemannHypothesis

end
