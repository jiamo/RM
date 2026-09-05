/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The logarithmic derivative is locally integrable

Littlewood's lemma, and with it every density estimate for the zeroes of `ζ`, needs to integrate
`f′/f` across a rectangle that *contains zeroes of `f`*.  At a zero of order `k` the logarithmic
derivative blows up like `k/(s − ρ)`, which is unbounded — but in two real dimensions `1/‖x‖` is
integrable, so `f′/f` is still locally integrable.  This file proves that, for an arbitrary
analytic function of a complex variable.

## Main results

* `exists_ball_eq_pow_mul` — the local factorization `f z = (z − ρ)^k · g z`.
* `logDeriv_eq_of_eq_pow_mul` — hence `logDeriv f z = k/(z − ρ) + logDeriv g z` away from `ρ`.
* `exists_punctured_ball_logDeriv_bound` — near an isolated zero `ρ` there are `C, r > 0` with
  `‖logDeriv f s‖ ≤ C / ‖s − ρ‖` on the punctured ball, on which `f` is moreover analytic and
  nonvanishing.
* `integrableOn_inv_norm_sub_ball` — the model estimate: `z ↦ C/‖z − ρ‖` is integrable on a ball.
* `integrableOn_logDeriv_ball` — hence `logDeriv f` is integrable on a small ball around `ρ`.
* `locallyIntegrableOn_logDeriv` — `logDeriv f` is locally integrable on any open set on which
  `f` is analytic and vanishes nowhere identically.
* `integrableOn_logDeriv_of_isCompact` — hence integrable on any compact subset of such a set.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology ENNReal

namespace RiemannHypothesis

/-! ## The local factorization -/

/-- Near a point at which `f` is analytic and does not vanish identically, `f` factors as
`(z − ρ)^k · g z` with `g` analytic and nonvanishing, on an open ball. -/
theorem exists_ball_eq_pow_mul {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hne : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) :
    ∃ (k : ℕ) (g : ℂ → ℂ) (r : ℝ), 0 < r ∧
      (∀ z ∈ ball ρ r, AnalyticAt ℂ g z) ∧ (∀ z ∈ ball ρ r, g z ≠ 0) ∧
      (∀ z ∈ ball ρ r, f z = (z - ρ) ^ k * g z) := by
  obtain ⟨k, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have h1 : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have h3 : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ k * g z := by
    filter_upwards [hfg] with z hz
    simpa [smul_eq_mul] using hz
  obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
  exact ⟨k, g, r, hr, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.1,
    fun z hz => (hsub z hz).2.2⟩

/-- On an open ball where `f z = (z − ρ)^k · g z` with `g` analytic and nonvanishing, the
logarithmic derivative of `f` is `k/(z − ρ) + logDeriv g z`, away from `ρ`. -/
theorem logDeriv_eq_of_eq_pow_mul {f g : ℂ → ℂ} {ρ : ℂ} {k : ℕ} {r : ℝ}
    (hg : ∀ z ∈ ball ρ r, AnalyticAt ℂ g z) (hg0 : ∀ z ∈ ball ρ r, g z ≠ 0)
    (hfg : ∀ z ∈ ball ρ r, f z = (z - ρ) ^ k * g z) {z : ℂ} (hz : z ∈ ball ρ r) (hzρ : z ≠ ρ) :
    logDeriv f z = (k : ℂ) / (z - ρ) + logDeriv g z := by
  have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  have hnhds : f =ᶠ[𝓝 z] fun w => (w - ρ) ^ k * g w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfg w hw
  have hcongr : logDeriv f z = logDeriv (fun w => (w - ρ) ^ k * g w) z := by
    simp only [logDeriv_apply, hnhds.deriv_eq, hnhds.self_of_nhds]
  rw [hcongr]
  have hdpow : DifferentiableAt ℂ (fun w : ℂ => w - ρ) z := by fun_prop
  have hdg : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
  have hpow0 : ((fun w : ℂ => (w - ρ) ^ k) z) ≠ 0 := pow_ne_zero _ hzsub
  rw [logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ k) (g := g) z hpow0 (hg0 z hz)
    (hdpow.pow k) hdg, logDeriv_fun_pow hdpow k]
  congr 1
  rw [logDeriv_apply, show deriv (fun w : ℂ => w - ρ) z = 1 by
    simp]
  field_simp

/-! ## The size of the logarithmic derivative near a zero -/

/-- **The local picture at an isolated zero.**  If `f` is analytic at `ρ` and does not vanish
identically near `ρ`, then on a small punctured ball `f` is analytic and nonvanishing, and
`‖logDeriv f s‖ ≤ C / ‖s − ρ‖`. -/
theorem exists_punctured_ball_logDeriv_bound {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hne : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      (∀ s ∈ ball ρ r, s ≠ ρ → AnalyticAt ℂ f s ∧ f s ≠ 0) ∧
      (∀ s ∈ ball ρ r, s ≠ ρ → ‖logDeriv f s‖ ≤ C / ‖s - ρ‖) := by
  obtain ⟨k, g, r, hr, hg, hg0, hfg⟩ := exists_ball_eq_pow_mul hf hne
  set r' := r / 2 with hr'def
  have hr' : 0 < r' := by positivity
  have hsub : closedBall ρ r' ⊆ ball ρ r := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  -- `logDeriv g` is continuous on the compact `closedBall ρ r'`, hence bounded there
  have hcont : ContinuousOn (fun z => logDeriv g z) (closedBall ρ r') := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    have hz' := hsub hz
    exact ((hg z hz').deriv.continuousAt).div (hg z hz').continuousAt (hg0 z hz')
  obtain ⟨M, hM⟩ := (isCompact_closedBall ρ r').exists_bound_of_continuousOn hcont.norm
  have hMcont : ∀ z ∈ closedBall ρ r', ‖logDeriv g z‖ ≤ M := by
    intro z hz
    simpa using hM z hz
  refine ⟨(k : ℝ) + |M| * r' + 1, r', by positivity, hr', ?_, ?_⟩
  · intro s hs hsρ
    have hsr : s ∈ ball ρ r := hsub (ball_subset_closedBall hs)
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - ρ) s := analyticAt_id.sub analyticAt_const
    have hprod : AnalyticAt ℂ (fun w : ℂ => (w - ρ) ^ k * g w) s := (hbase.pow k).mul (hg s hsr)
    refine ⟨hprod.congr ?_, ?_⟩
    · filter_upwards [isOpen_ball.mem_nhds hsr] with w hw using (hfg w hw).symm
    · rw [hfg s hsr]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hsρ)) (hg0 s hsr)
  · intro s hs hsρ
    have hsr : s ∈ ball ρ r := hsub (ball_subset_closedBall hs)
    have hscb : s ∈ closedBall ρ r' := ball_subset_closedBall hs
    have hnorm : ‖s - ρ‖ ≤ r' := by simpa [mem_closedBall, dist_eq_norm] using hscb
    have hpos : 0 < ‖s - ρ‖ := by
      simpa [norm_pos_iff, sub_eq_zero] using hsρ
    rw [logDeriv_eq_of_eq_pow_mul hg hg0 hfg hsr hsρ]
    calc ‖(k : ℂ) / (s - ρ) + logDeriv g s‖
        ≤ ‖(k : ℂ) / (s - ρ)‖ + ‖logDeriv g s‖ := norm_add_le _ _
      _ ≤ (k : ℝ) / ‖s - ρ‖ + |M| := by
          gcongr
          · simp
          · exact (hMcont s hscb).trans (le_abs_self M)
      _ ≤ (k : ℝ) / ‖s - ρ‖ + (|M| * r' + 1) / ‖s - ρ‖ := by
          have h1 : |M| ≤ (|M| * r') / ‖s - ρ‖ := by
            rw [le_div_iff₀ hpos]
            exact mul_le_mul_of_nonneg_left hnorm (abs_nonneg M)
          have h2 : (|M| * r') / ‖s - ρ‖ ≤ (|M| * r' + 1) / ‖s - ρ‖ := by
            gcongr; linarith
          linarith
      _ = ((k : ℝ) + |M| * r' + 1) / ‖s - ρ‖ := by ring

/-! ## Integrability -/

/-- The model estimate: `z ↦ C/‖z − ρ‖` is integrable on any ball.  In two real dimensions the
singularity `1/‖z‖` is integrable. -/
theorem integrableOn_inv_norm_sub_ball {C r : ℝ} (hC : 0 < C) (ρ : ℂ) :
    IntegrableOn (fun z : ℂ => C / ‖z - ρ‖) (ball ρ r) volume := by
  have h0 : IntegrableOn (fun z : ℂ => C / ‖z‖) (ball (0 : ℂ) r) volume := by
    refine ⟨((measurable_const.div measurable_norm).aestronglyMeasurable).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    set F : ℂ → ℝ≥0∞ := (ball (0 : ℂ) r).indicator (fun z => ‖C / ‖z‖‖ₑ) with hF
    have hmeasball : MeasurableSet (ball (0 : ℂ) r) := measurableSet_ball
    have h1 : ∫⁻ z in ball (0 : ℂ) r, ‖C / ‖z‖‖ₑ = ∫⁻ z, F z := by
      rw [hF, lintegral_indicator hmeasball]
    rw [h1, ← Complex.lintegral_comp_polarCoord_symm F]
    set box : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi with hbox
    have hboxmeas : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
    have hle : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p)
          ≤ box.indicator (fun _ => ENNReal.ofReal C) p := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : (0 : ℝ) < p.1 := hp1
      by_cases hmem : Complex.polarCoord.symm p ∈ ball (0 : ℂ) r
      · have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1']
        have hlt : p.1 < r := by
          have := mem_ball_zero_iff.mp hmem
          rwa [hnorm] at this
        have hbmem : p ∈ box := ⟨⟨hp1', hlt⟩, hp2⟩
        rw [Set.indicator_of_mem hbmem, hF, Set.indicator_of_mem hmem, hnorm, smul_eq_mul]
        have hnn : ‖C / p.1‖ₑ = ENNReal.ofReal (C / p.1) :=
          Real.enorm_eq_ofReal (by positivity)
        rw [hnn, ← ENNReal.ofReal_mul hp1'.le, mul_div_cancel₀ _ hp1'.ne']
      · rw [hF, Set.indicator_of_notMem hmem]
        simp
    calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p)
        ≤ ∫⁻ p in polarCoord.target, box.indicator (fun _ => ENNReal.ofReal C) p :=
          setLIntegral_mono' polarCoord.open_target.measurableSet hle
      _ ≤ ∫⁻ p, box.indicator (fun _ => ENNReal.ofReal C) p := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal C * volume box := by
          rw [lintegral_indicator hboxmeas, setLIntegral_const]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          rw [hbox, Measure.volume_eq_prod, Measure.prod_prod]
          exact ENNReal.mul_lt_top (by simp [Real.volume_Ioo]) (by simp [Real.volume_Ioo])
  have hmp : MeasurePreserving (fun z : ℂ => z + ρ) volume volume :=
    measurePreserving_add_right volume ρ
  have hme : MeasurableEmbedding (fun z : ℂ => z + ρ) :=
    (Homeomorph.addRight ρ).measurableEmbedding
  rw [← hmp.integrableOn_comp_preimage hme]
  have he1 : (fun z : ℂ => z + ρ) ⁻¹' (ball ρ r) = ball 0 r := by
    ext z; simp [Metric.mem_ball, dist_eq_norm]
  have he2 : ((fun z : ℂ => C / ‖z - ρ‖) ∘ fun z : ℂ => z + ρ) = fun z : ℂ => C / ‖z‖ := by
    funext z; simp
  rw [he1, he2]
  exact h0

/-- `logDeriv f` is integrable on a small ball around an isolated zero. -/
theorem integrableOn_logDeriv_ball {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hne : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) :
    ∃ r : ℝ, 0 < r ∧ IntegrableOn (logDeriv f) (ball ρ r) volume := by
  obtain ⟨C, r, hC, hr, hstruct, hbd⟩ := exists_punctured_ball_logDeriv_bound hf hne
  refine ⟨r, hr, ?_⟩
  -- the punctured ball
  set S : Set ℂ := ball ρ r \ {ρ} with hS
  have hSmeas : MeasurableSet S := measurableSet_ball.diff (measurableSet_singleton ρ)
  have hmemS : ∀ z ∈ S, z ∈ ball ρ r ∧ z ≠ ρ := by
    intro z hz
    exact ⟨hz.1, by simpa using hz.2⟩
  have hcontS : ContinuousOn (logDeriv f) S := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hmemS z hz
    obtain ⟨hana, hne0⟩ := hstruct z hz1 hz2
    exact (hana.deriv.continuousAt.div hana.continuousAt hne0).continuousWithinAt
  have hdom : IntegrableOn (fun z : ℂ => C / ‖z - ρ‖) S volume :=
    (integrableOn_inv_norm_sub_ball (C := C) (r := r) hC ρ).mono_set (Set.sdiff_subset)
  have hintS : IntegrableOn (logDeriv f) S volume := by
    refine Integrable.mono' hdom (hcontS.aestronglyMeasurable hSmeas) ?_
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    obtain ⟨hz1, hz2⟩ := hmemS z hz
    exact hbd z hz1 hz2
  -- adding back the single point `ρ` does not change integrability
  have hpt : IntegrableOn (logDeriv f) {ρ} volume := by
    simp [IntegrableOn, Measure.restrict_singleton, measure_singleton]
  rw [← Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr (mem_ball_self hr))]
  exact hintS.union hpt

/-- **`logDeriv f` is locally integrable on an open set of analyticity.**  No zero-freeness is
assumed: at a zero the logarithmic derivative has a `1/(z − ρ)` singularity, which is integrable
in two real dimensions. -/
theorem locallyIntegrableOn_logDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) :
    LocallyIntegrableOn (logDeriv f) U volume := by
  intro ρ hρ
  obtain ⟨r, hr, hint⟩ := integrableOn_logDeriv_ball (hf ρ hρ) (hne ρ hρ)
  exact ⟨ball ρ r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds ρ hr), hint⟩

/-- `logDeriv f` is integrable on any compact subset of an open set of analyticity. -/
theorem integrableOn_logDeriv_of_isCompact {f : ℂ → ℂ} {U K : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in 𝓝 ρ, f z = 0)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (logDeriv f) K volume :=
  (locallyIntegrableOn_iff hU.isLocallyClosed).mp
    (locallyIntegrableOn_logDeriv hf hne) K hKU hK

end RiemannHypothesis
