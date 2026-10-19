/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib

/-!
# The Laplace transform of `u^(a-1)` at a complex frequency

Mathlib has `∫_0^∞ u^(a-1) e^(-r u) du = r^(-a) Γ(a)` for **real** `r > 0`
(`Complex.integral_cpow_mul_exp_neg_mul_Ioi`).  This file extends it to every complex `r` with
`re r > 0` (`integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`), by analytic continuation: both sides
are holomorphic in `r` on the right half-plane (the left side by differentiation under the integral
sign, dominated by `u^(re a) e^(-δ u)`) and they agree on the positive reals.

This is the input that replaces the Fresnel integral in the evaluation of the stationary-phase
integrals of `ζ` (`RiemannHypothesis.ZetaMellinPhase`): letting `re r → 0⁺` there gives
`∫_0^∞ u^(-s) e^(iωu) du = Γ(1-s) (i/ω)^(1-s)`.  Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RiemannHypothesis

namespace LaplaceGamma

/-- The integrand `u^(a-1) e^(-r u)`. -/
def lapIntegrand (a r : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (a - 1) * cexp (-(r * u))

theorem norm_lapIntegrand {a r : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖lapIntegrand a r u‖ = u ^ (a.re - 1) * Real.exp (-(r.re * u)) := by
  rw [lapIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
  simp

theorem continuousOn_lapIntegrand (a r : ℂ) : ContinuousOn (lapIntegrand a r) (Ioi 0) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  unfold lapIntegrand
  apply ContinuousAt.mul
  · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (by left; simpa using hu)
  · fun_prop

theorem integrableOn_lapIntegrand {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    IntegrableOn (lapIntegrand a r) (Ioi 0) := by
  have hb : IntegrableOn (fun u : ℝ => u ^ (a.re - 1) * Real.exp (-r.re * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hr
  refine hb.mono' ((continuousOn_lapIntegrand a r).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_lapIntegrand hu, Real.rpow_one, neg_mul]

/-- The Laplace transform `F(r) = ∫_0^∞ u^(a-1) e^(-r u) du`. -/
def lapF (a r : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), lapIntegrand a r u

theorem hasDerivAt_lapF {a r₀ : ℂ} (ha : 0 < a.re) (hr₀ : 0 < r₀.re) :
    HasDerivAt (lapF a) (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * (-(u : ℂ)) * cexp (-(r₀ * u)))
      r₀ := by
  set δ : ℝ := r₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball r₀ δ ∈ 𝓝 r₀ := Metric.ball_mem_nhds r₀ hδ0
  have hre : ∀ r ∈ Metric.ball r₀ δ, δ < r.re := by
    intro r hr
    rw [Metric.mem_ball, dist_eq_norm] at hr
    have := Complex.abs_re_le_norm (r - r₀)
    rw [Complex.sub_re] at this
    have h2 := abs_lt.mp (this.trans_lt hr)
    linarith
  have hmeas : ∀ r : ℂ, AEStronglyMeasurable (lapIntegrand a r) (volume.restrict (Ioi 0)) :=
    fun r => (continuousOn_lapIntegrand a r).aestronglyMeasurable measurableSet_Ioi
  have hF'meas : AEStronglyMeasurable
      (fun u : ℝ => (u : ℂ) ^ (a - 1) * (-(u : ℂ)) * cexp (-(r₀ * u))) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (by left; simpa using hu)
      · fun_prop
    · fun_prop
  have hbound : IntegrableOn (fun u : ℝ => u ^ a.re * Real.exp (-δ * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hδ0
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r u => lapIntegrand a r u)
    (F' := fun r u => (u : ℂ) ^ (a - 1) * (-(u : ℂ)) * cexp (-(r * u)))
    (bound := fun u => u ^ a.re * Real.exp (-δ * u ^ (1 : ℝ)))
    hball (Eventually.of_forall hmeas) (integrableOn_lapIntegrand ha hr₀) hF'meas ?_ hbound ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu r hr
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_exp, Real.rpow_one]
    have hexp : Real.exp ((-(r * (u : ℂ))).re) ≤ Real.exp (-δ * u) := by
      apply Real.exp_le_exp.mpr
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have := hre r hr
      nlinarith
    have hpow : u ^ ((a - 1).re) * u = u ^ a.re := by
      rw [show (a - 1).re = a.re - 1 by simp, Real.rpow_sub hu0, Real.rpow_one]
      field_simp
    calc u ^ ((a - 1).re) * u * Real.exp ((-(r * (u : ℂ))).re)
        ≤ u ^ ((a - 1).re) * u * Real.exp (-δ * u) := by
          apply mul_le_mul_of_nonneg_left hexp; positivity
      _ = u ^ a.re * Real.exp (-δ * u) := by rw [hpow]
  · filter_upwards with u r' _
    unfold lapIntegrand
    have h1 : HasDerivAt (fun r : ℂ => cexp (-(r * u))) (cexp (-(r' * u)) * (-(u : ℂ))) r' := by
      have := ((hasDerivAt_id r').mul_const (u : ℂ)).neg.cexp
      simpa using this
    have := h1.const_mul ((u : ℂ) ^ (a - 1))
    refine this.congr_deriv ?_
    ring

theorem differentiableOn_lapF {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (lapF a) {r : ℂ | 0 < r.re} := fun _ hr =>
  (hasDerivAt_lapF ha hr).differentiableAt.differentiableWithinAt

theorem one_div_mem_slitPlane {r : ℂ} (hr : 0 < r.re) : 1 / r ∈ slitPlane := by
  left
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  rw [one_div, Complex.inv_re]
  exact div_pos hr (Complex.normSq_pos.mpr hr0)

theorem differentiableOn_rhs (a : ℂ) :
    DifferentiableOn ℂ (fun r : ℂ => (1 / r) ^ a * Gamma a) {r : ℂ | 0 < r.re} := by
  intro r hr
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.cpow_const
  · exact (differentiableAt_const _).div differentiableAt_id hr0
  · exact one_div_mem_slitPlane hr

/-- **The Laplace transform of `u^(a-1)` at a complex frequency**: for `re a > 0` and `re r > 0`,
`∫_0^∞ u^(a-1) e^(-r u) du = (1/r)^a Γ(a)`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-(r * u)) = (1 / r) ^ a * Gamma a := by
  set U : Set ℂ := {r : ℂ | 0 < r.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hF := (differentiableOn_lapF ha).analyticOnNhd hUo
  have hG := (differentiableOn_rhs a).analyticOnNhd hUo
  have h1 : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), lapF a z = (1 / z) ^ a * Gamma a := by
    set z : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hz
    have hlim : Tendsto z atTop (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at this
        have := (continuous_ofReal.tendsto 1).comp this
        simpa [hz, Function.comp_def] using this
      · filter_upwards with n
        simp only [hz, mem_compl_iff, mem_singleton_iff]
        intro h
        have h' : (1 + 1 / ((n : ℝ) + 1)) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    have hpos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    exact Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hpos
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hUc h1 hfreq hr

end LaplaceGamma

end RiemannHypothesis
