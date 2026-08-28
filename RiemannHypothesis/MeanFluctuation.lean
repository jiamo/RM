/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MeanSquare

/-!
# What a mean value says about the fluctuation of `|ζ|` on a line

A function whose average over `[0, T]` tends to `L` must come arbitrarily close to `L` from
above and from below along arbitrarily large arguments: it cannot stay below `L - ε`, nor
above `L + ε`, from some point on.  Combined with the mean value theorem of
`RiemannHypothesis.MeanSquare` this turns the second moment of `ζ` into a statement about the
size of `|ζ(σ + i t)|` itself: for `σ > 1`,

`|ζ(σ + i t)|² > ζ(2σ) - ε`  and  `|ζ(σ + i t)|² < ζ(2σ) + ε`

both happen for arbitrarily large `t`.

## Main results

* `frequently_gt_sub_of_avg_tendsto`, `frequently_lt_add_of_avg_tendsto` : the general
  statement for a locally integrable function with a mean value.
* `frequently_normSq_riemannZeta_gt`, `frequently_normSq_riemannZeta_lt` : the specialization
  to `|ζ(σ + i t)|²` for `σ > 1`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology intervalIntegral

namespace RiemannHypothesis

/-- The elementary limit `c/T + K → K` as `T → ∞`. -/
private lemma tendsto_affine_div (c K : ℝ) :
    Tendsto (fun T : ℝ => c / T + K) atTop (𝓝 K) := by
  have h : Tendsto (fun T : ℝ => c / T) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul c)
  simpa using h.add (tendsto_const_nhds (x := K) (f := atTop (α := ℝ)))

/-- A function whose average over `[0, T]` tends to `L` exceeds `L - ε` for arbitrarily large
arguments. -/
theorem frequently_gt_sub_of_avg_tendsto {f : ℝ → ℝ} {L ε : ℝ}
    (hf : ∀ T : ℝ, IntervalIntegrable f volume 0 T)
    (havg : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, f t) / T) atTop (𝓝 L)) (hε : 0 < ε) :
    ∃ᶠ t in atTop, L - ε < f t := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨t₁, ht₁⟩ := (eventually_atTop.mp hcon)
  set t₀ : ℝ := max t₁ 0 with ht₀
  have ht₀0 : 0 ≤ t₀ := le_max_right _ _
  have hbound : ∀ t, t₀ ≤ t → f t ≤ L - ε := by
    intro t ht
    have := ht₁ t (le_trans (le_max_left _ _) ht)
    exact not_lt.mp this
  set C : ℝ := ∫ t in (0 : ℝ)..t₀, f t with hC
  set K : ℝ := L - ε with hK
  have hle : ∀ T : ℝ, t₀ ≤ T → (∫ t in (0 : ℝ)..T, f t) ≤ C + (T - t₀) * K := by
    intro T hT
    have hsplit : (∫ t in (0 : ℝ)..T, f t) = C + ∫ t in t₀..T, f t := by
      rw [hC, integral_add_adjacent_intervals (hf t₀)]
      exact ((hf T).mono_set (by
        rw [Set.uIcc_of_le hT, Set.uIcc_of_le (le_trans ht₀0 hT)]
        exact Set.Icc_subset_Icc ht₀0 le_rfl))
    have hmono : (∫ t in t₀..T, f t) ≤ ∫ _t in t₀..T, K := by
      refine integral_mono_on hT ?_ _root_.intervalIntegrable_const fun x hx => hbound x hx.1
      exact ((hf T).mono_set (by
        rw [Set.uIcc_of_le hT, Set.uIcc_of_le (le_trans ht₀0 hT)]
        exact Set.Icc_subset_Icc ht₀0 le_rfl))
    rw [hsplit]
    simpa [intervalIntegral.integral_const, smul_eq_mul] using add_le_add_left hmono C
  have hfinal : ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, f t) / T ≤ (C - t₀ * K) / T + K := by
    filter_upwards [eventually_ge_atTop t₀, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    rw [div_le_iff₀ hT0]
    have h := hle T hT
    have hexp : ((C - t₀ * K) / T + K) * T = C - t₀ * K + K * T := by
      field_simp
    rw [hexp]
    nlinarith [h]
  have hlim := le_of_tendsto_of_tendsto havg (tendsto_affine_div (C - t₀ * K) K) hfinal
  rw [hK] at hlim
  linarith

/-- A function whose average over `[0, T]` tends to `L` drops below `L + ε` for arbitrarily
large arguments. -/
theorem frequently_lt_add_of_avg_tendsto {f : ℝ → ℝ} {L ε : ℝ}
    (hf : ∀ T : ℝ, IntervalIntegrable f volume 0 T)
    (havg : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, f t) / T) atTop (𝓝 L)) (hε : 0 < ε) :
    ∃ᶠ t in atTop, f t < L + ε := by
  have hneg : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, (-f) t) / T) atTop (𝓝 (-L)) := by
    have : ∀ T : ℝ, (∫ t in (0 : ℝ)..T, (-f) t) / T = -((∫ t in (0 : ℝ)..T, f t) / T) := by
      intro T
      rw [show (fun t => (-f) t) = fun t => -f t from rfl, intervalIntegral.integral_neg, neg_div]
    simpa only [this] using havg.neg
  have h := frequently_gt_sub_of_avg_tendsto (f := -f) (fun T => (hf T).neg) hneg hε
  refine h.mono fun t ht => ?_
  simp only [Pi.neg_apply] at ht
  linarith

/-- For `σ > 1` the function `t ↦ |ζ(σ + i t)|²` is continuous. -/
lemma continuous_normSq_riemannZeta_line {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun t : ℝ => ‖riemannZeta (linePoint σ t)‖ ^ 2 := by
  have hline : Continuous fun t : ℝ => linePoint σ t := by
    unfold linePoint
    fun_prop
  have hzeta : Continuous fun t : ℝ => riemannZeta (linePoint σ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : linePoint σ t ≠ 1 := by
      intro h
      have : (linePoint σ t).re = 1 := by rw [h]; simp
      rw [linePoint_re] at this
      linarith
    exact (differentiableAt_riemannZeta hne).continuousAt.comp hline.continuousAt
  exact (hzeta.norm.pow 2)

/-- For `σ > 1` and every `ε > 0`, `|ζ(σ + i t)|² > ζ(2σ) - ε` for arbitrarily large `t`. -/
theorem frequently_normSq_riemannZeta_gt {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t in atTop, (riemannZeta ((2 * σ : ℝ) : ℂ)).re - ε
      < ‖riemannZeta (linePoint σ t)‖ ^ 2 :=
  frequently_gt_sub_of_avg_tendsto
    (fun T => (continuous_normSq_riemannZeta_line hσ).intervalIntegrable 0 T)
    (meanSquareAvg_tendsto_riemannZeta hσ) hε

/-- For `σ > 1` and every `ε > 0`, `|ζ(σ + i t)|² < ζ(2σ) + ε` for arbitrarily large `t`. -/
theorem frequently_normSq_riemannZeta_lt {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t in atTop, ‖riemannZeta (linePoint σ t)‖ ^ 2
      < (riemannZeta ((2 * σ : ℝ) : ℂ)).re + ε :=
  frequently_lt_add_of_avg_tendsto
    (fun T => (continuous_normSq_riemannZeta_line hσ).intervalIntegrable 0 T)
    (meanSquareAvg_tendsto_riemannZeta hσ) hε

end RiemannHypothesis
