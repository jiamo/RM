/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import RiemannHypothesis.ExponentialType

/-!
# The easy half of Paley–Wiener: band-limited functions have exponential type

For an integrable `g` on `[-τ, τ]`, the band-limited function
`F(z) = ∫_{-τ}^{τ} g(t) e^{i z t} dt` satisfies `|F(z)| ≤ ‖g‖₁ e^{τ |z|}`; in particular it has
exponential type at most `τ` (`bandLimited_hasExponentialTypeAtMost`), it is bounded on the
real axis by `‖g‖₁` (`norm_bandLimited_ofReal_le`), and it is entire
(`bandLimited_differentiable`).

## Scope

This is the easy direction of the Paley–Wiener correspondence, for `g ∈ L¹[-τ, τ]`.  Not proved
here: that `F ∈ L²(ℝ)` when `g ∈ L²` (Plancherel), and the hard
converse (an entire function of exponential type `τ` that is square-integrable on `ℝ` is such a
Fourier integral).  The converse is what the Beurling–Selberg route needs.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral

namespace RiemannHypothesis

/-- The band-limited function `F(z) = ∫_{-τ}^{τ} g(t) e^{i z t} dt` with spectrum in `[-τ, τ]`. -/
def bandLimited (g : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-τ)..τ, g t * Complex.exp (Complex.I * z * t)

/-- `|e^{i z t}| ≤ e^{τ |z|}` for `|t| ≤ τ`. -/
lemma norm_exp_I_mul_le {τ t : ℝ} (ht : |t| ≤ τ) (z : ℂ) :
    ‖Complex.exp (Complex.I * z * t)‖ ≤ Real.exp (τ * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * z * t).re = -(z.im * t) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
    _ = |z.im| * |t| := abs_mul _ _
    _ ≤ ‖z‖ * τ := mul_le_mul (Complex.abs_im_le_norm z) ht (abs_nonneg _) (norm_nonneg _)
    _ = τ * ‖z‖ := mul_comm _ _

/-- **The growth bound.**  `|F(z)| ≤ (∫_{-τ}^{τ} |g|) e^{τ |z|}`. -/
theorem norm_bandLimited_le {g : ℝ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : IntervalIntegrable g volume (-τ) τ) (z : ℂ) :
    ‖bandLimited g τ z‖ ≤ (∫ t in (-τ)..τ, ‖g t‖) * Real.exp (τ * ‖z‖) := by
  unfold bandLimited
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : |t| ≤ τ := abs_le.mpr ⟨ht.1.le, ht.2⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_exp_I_mul_le ht' z) (norm_nonneg _)
  · exact hg.norm.mul_const _

/-- **Band-limited functions have exponential type at most `τ`.** -/
theorem bandLimited_hasExponentialTypeAtMost {g : ℝ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : IntervalIntegrable g volume (-τ) τ) :
    HasExponentialTypeAtMost (bandLimited g τ) τ := by
  intro ε hε
  set M := ∫ t in (-τ)..τ, ‖g t‖
  refine ⟨M + 1, ?_, fun z => ?_⟩
  · have : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _
    linarith
  · have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _
    calc ‖bandLimited g τ z‖ ≤ M * Real.exp (τ * ‖z‖) := norm_bandLimited_le hτ hg z
      _ ≤ (M + 1) * Real.exp ((τ + ε) * ‖z‖) := by
        apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
        nlinarith [norm_nonneg z]

/-- On the real axis a band-limited function is bounded by `‖g‖₁`. -/
theorem norm_bandLimited_ofReal_le {g : ℝ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : IntervalIntegrable g volume (-τ) τ) (x : ℝ) :
    ‖bandLimited g τ x‖ ≤ ∫ t in (-τ)..τ, ‖g t‖ := by
  unfold bandLimited
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · refine Filter.Eventually.of_forall fun t _ => ?_
    rw [norm_mul]
    have : ‖Complex.exp (Complex.I * (x : ℂ) * t)‖ = 1 := by
      rw [show Complex.I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  · exact hg.norm

/-- **Band-limited functions are entire** (differentiation under the integral sign). -/
theorem bandLimited_differentiable {g : ℝ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : IntervalIntegrable g volume (-τ) τ) : Differentiable ℂ (bandLimited g τ) := by
  intro z₀
  have hgm : AEStronglyMeasurable g (volume.restrict (Set.uIoc (-τ) τ)) :=
    hg.def'.aestronglyMeasurable
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ => Complex.exp (Complex.I * z * t) := by
    intro z; fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => g t * Complex.exp (Complex.I * z * t))
    (F' := fun z t => g t * (Complex.I * t * Complex.exp (Complex.I * z * t)))
    (x₀ := z₀) (a := -τ) (b := τ) (μ := volume)
    (bound := fun t => ‖g t‖ * (τ * Real.exp (τ * (‖z₀‖ + 1))))
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Filter.Eventually.of_forall fun z => hgm.mul (hcont z).aestronglyMeasurable)
    (by
      refine hg.mul_continuousOn ?_
      exact (hcont z₀).continuousOn)
    (hgm.mul (by fun_prop : Continuous fun t : ℝ =>
        Complex.I * t * Complex.exp (Complex.I * z₀ * t)).aestronglyMeasurable)
    (by
      refine Filter.Eventually.of_forall fun t ht z (hz : z ∈ Metric.ball z₀ 1) => ?_
      have ht' : |t| ≤ τ := by
        rw [Set.uIoc_of_le (by linarith)] at ht
        exact abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul ht' _ (norm_nonneg _) hτ
      refine (norm_exp_I_mul_le ht' z).trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_left hz' hτ)
    (hg.norm.mul_const _)
    (by
      refine Filter.Eventually.of_forall fun t _ z _ => ?_
      have h1 : HasDerivAt (fun z : ℂ => Complex.I * z * t) (Complex.I * t) z := by
        simpa using ((hasDerivAt_id z).const_mul Complex.I).mul_const (t : ℂ)
      have h2 := h1.cexp
      have h3 := h2.const_mul (g t)
      exact h3.congr_deriv (by ring))
  exact key.2.differentiableAt

end RiemannHypothesis
