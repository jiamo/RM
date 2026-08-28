/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The log-modulus of an analytic function along a segment

Littlewood's lemma turns the contour integral of `f′/f` around a rectangle into an integral of
`log ‖f‖` over its border.  Constructing a *branch of the logarithm* along the contour is what
makes that step delicate; the modulus, however, needs no branch: `log ‖f‖` is a genuine
real-valued function, and along a straight segment its derivative is the real part of `f′/f`
rotated by the direction of the segment.  That is what this file proves.

* `hasDerivAt_log_norm_comp` — for `g : ℝ → ℂ` differentiable and nonzero at `x`,
  `(log ‖g ·‖)′ x = re (g′(x) / g x)`.  No branch of `log` is involved: the proof differentiates
  `½ log (normSq g)`.
* `hasDerivAt_log_norm_horizontal`, `hasDerivAt_log_norm_vertical` — the two special cases used
  for a rectangle: moving in the `σ` direction the derivative is `re (f′/f)`, moving in the `t`
  direction it is `−im (f′/f)`.
* `integral_re_logDeriv_horizontal` — the fundamental theorem of calculus on a horizontal
  segment on which `f` is analytic and nonvanishing:
  `∫_a^b re (f′/f)(σ + it) dσ = log ‖f(b + it)‖ − log ‖f(a + it)‖`.
* `integral_im_logDeriv_vertical` — the vertical counterpart:
  `∫_c^d −im (f′/f)(σ + it) dt = log ‖f(σ + id)‖ − log ‖f(σ + ic)‖`.

These are the four sides of the border of a rectangle, and they are exactly the half of
Littlewood's lemma that does not need a branch of `log`: the remaining half is the *argument*,
the imaginary part, which is where the branch is needed and which is not treated here.  Nothing
in this file mentions `ζ`.
-/

open Complex

namespace RiemannHypothesis

/-! ## The derivative of the log-modulus -/

/-- **The derivative of `log ‖g‖`.**  If `g : ℝ → ℂ` has derivative `c` at `x` and `g x ≠ 0`,
then `σ ↦ log ‖g σ‖` has derivative `re (c / g x)` at `x`.  The proof differentiates
`½ log (normSq g)`, so no branch of the complex logarithm is needed. -/
theorem hasDerivAt_log_norm_comp {g : ℝ → ℂ} {c : ℂ} {x : ℝ} (hg : HasDerivAt g c x)
    (h0 : g x ≠ 0) : HasDerivAt (fun σ => Real.log ‖g σ‖) ((c / g x).re) x := by
  have hre : HasDerivAt (fun σ => (g σ).re) c.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg
  have him : HasDerivAt (fun σ => (g σ).im) c.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  have hfun : (fun σ => Complex.normSq (g σ))
      = fun σ => (g σ).re * (g σ).re + (g σ).im * (g σ).im :=
    funext fun σ => Complex.normSq_apply _
  have hval2 : c.re * (g x).re + (g x).re * c.re + (c.im * (g x).im + (g x).im * c.im)
      = 2 * ((g x).re * c.re + (g x).im * c.im) := by ring
  have hsq : HasDerivAt (fun σ => Complex.normSq (g σ))
      (2 * ((g x).re * c.re + (g x).im * c.im)) x := by
    rw [hfun, ← hval2]
    exact (hre.mul hre).add (him.mul him)
  have hne : Complex.normSq (g x) ≠ 0 := by simpa [Complex.normSq_eq_zero] using h0
  have hlog := (hsq.log hne).const_mul (1 / 2 : ℝ)
  have heq : (fun σ => (1 / 2 : ℝ) * Real.log (Complex.normSq (g σ)))
      = fun σ => Real.log ‖g σ‖ := by
    funext σ
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  rw [heq] at hlog
  have hval : (1 / 2 : ℝ) * (2 * ((g x).re * c.re + (g x).im * c.im) / Complex.normSq (g x))
      = (c / g x).re := by
    rw [Complex.div_re]
    field_simp
  rwa [hval] at hlog

/-! ## Moving along a horizontal or a vertical line -/

/-- Differentiating `f` along a horizontal line. -/
theorem hasDerivAt_horizontal {f : ℂ → ℂ} {t σ : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) :
    HasDerivAt (fun x : ℝ => f ((x : ℂ) + t * I)) (deriv f ((σ : ℂ) + t * I)) σ := by
  have hline : HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 σ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := σ)).add_const ((t : ℂ) * I)
  have h2 := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt σ hline
  simpa [Function.comp_def] using h2

/-- Differentiating `f` along a vertical line. -/
theorem hasDerivAt_vertical {f : ℂ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) :
    HasDerivAt (fun y : ℝ => f ((σ : ℂ) + y * I)) (deriv f ((σ : ℂ) + t * I) * I) t := by
  have hline : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add ((σ : ℂ))
  have h2 := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hline
  simpa [Function.comp_def, mul_comm] using h2

/-- Along a horizontal line, `log ‖f‖` has derivative `re (f′/f)`. -/
theorem hasDerivAt_log_norm_horizontal {f : ℂ → ℂ} {t σ : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) (h0 : f ((σ : ℂ) + t * I) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖f ((x : ℂ) + t * I)‖)
      ((logDeriv f ((σ : ℂ) + t * I)).re) σ := by
  have := hasDerivAt_log_norm_comp (hasDerivAt_horizontal hf) h0
  simpa [logDeriv] using this

/-- Along a vertical line, `log ‖f‖` has derivative `−im (f′/f)`. -/
theorem hasDerivAt_log_norm_vertical {f : ℂ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) (h0 : f ((σ : ℂ) + t * I) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log ‖f ((σ : ℂ) + y * I)‖)
      (-(logDeriv f ((σ : ℂ) + t * I)).im) t := by
  have h := hasDerivAt_log_norm_comp (hasDerivAt_vertical hf) h0
  have hval : ((deriv f ((σ : ℂ) + t * I) * I) / f ((σ : ℂ) + t * I)).re
      = -(logDeriv f ((σ : ℂ) + t * I)).im := by
    rw [logDeriv]
    rw [show deriv f ((σ : ℂ) + t * I) * I / f ((σ : ℂ) + t * I)
        = (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)) * I by ring]
    simp
  rwa [hval] at h

/-! ## The fundamental theorem of calculus along a side of a rectangle -/

/-- Continuity of `σ ↦ re (f′/f)(σ + it)` where `f` is analytic and nonvanishing. -/
theorem continuousOn_re_logDeriv_horizontal {f : ℂ → ℂ} {a b t : ℝ}
    (hf : ∀ σ ∈ Set.uIcc a b, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ Set.uIcc a b, f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => (logDeriv f ((x : ℂ) + t * I)).re) (Set.uIcc a b) := by
  intro σ hσ
  refine ContinuousAt.continuousWithinAt ?_
  have hpt : ContinuousAt (fun x : ℝ => (x : ℂ) + t * I) σ := by fun_prop
  have hderiv : ContinuousAt (deriv f) ((σ : ℂ) + t * I) := (hf σ hσ).deriv.continuousAt
  have hfc : ContinuousAt f ((σ : ℂ) + t * I) := (hf σ hσ).continuousAt
  have hz : ContinuousAt (fun z : ℂ => (logDeriv f z).re) ((σ : ℂ) + t * I) := by
    simp only [logDeriv]
    exact Complex.continuous_re.continuousAt.comp (hderiv.div hfc (h0 σ hσ))
  simpa [Function.comp_def] using
    ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + t * I) hz hpt

/-- Continuity of `t ↦ −im (f′/f)(σ + it)` where `f` is analytic and nonvanishing. -/
theorem continuousOn_im_logDeriv_vertical {f : ℂ → ℂ} {σ c d : ℝ}
    (hf : ∀ t ∈ Set.uIcc c d, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ Set.uIcc c d, f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun y : ℝ => -(logDeriv f ((σ : ℂ) + y * I)).im) (Set.uIcc c d) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hpt : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) t := by fun_prop
  have hderiv : ContinuousAt (deriv f) ((σ : ℂ) + t * I) := (hf t ht).deriv.continuousAt
  have hfc : ContinuousAt f ((σ : ℂ) + t * I) := (hf t ht).continuousAt
  have hz : ContinuousAt (fun z : ℂ => -(logDeriv f z).im) ((σ : ℂ) + t * I) := by
    simp only [logDeriv]
    exact (Complex.continuous_im.continuousAt.comp (hderiv.div hfc (h0 t ht))).neg
  simpa [Function.comp_def] using
    ContinuousAt.comp (f := fun y : ℝ => (σ : ℂ) + y * I) hz hpt

/-- **The log-modulus along a horizontal side.**  If `f` is analytic and nonvanishing on a
horizontal segment, then the integral of `re (f′/f)` along it is the increment of `log ‖f‖`.
This is the half of Littlewood's lemma that needs no branch of the logarithm. -/
theorem integral_re_logDeriv_horizontal {f : ℂ → ℂ} {a b t : ℝ}
    (hf : ∀ σ ∈ Set.uIcc a b, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ Set.uIcc a b, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in a..b, (logDeriv f ((σ : ℂ) + t * I)).re)
      = Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖ := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log ‖f ((x : ℂ) + t * I)‖) (fun σ hσ => ?_) ?_
  · exact hasDerivAt_log_norm_horizontal (hf σ hσ).differentiableAt (h0 σ hσ)
  · exact (continuousOn_re_logDeriv_horizontal hf h0).intervalIntegrable

/-- **The log-modulus along a vertical side.**  If `f` is analytic and nonvanishing on a
vertical segment, then the integral of `−im (f′/f)` along it is the increment of `log ‖f‖`. -/
theorem integral_im_logDeriv_vertical {f : ℂ → ℂ} {σ c d : ℝ}
    (hf : ∀ t ∈ Set.uIcc c d, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ Set.uIcc c d, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ t in c..d, -(logDeriv f ((σ : ℂ) + t * I)).im)
      = Real.log ‖f ((σ : ℂ) + d * I)‖ - Real.log ‖f ((σ : ℂ) + c * I)‖ := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => Real.log ‖f ((σ : ℂ) + y * I)‖) (fun t ht => ?_) ?_
  · exact hasDerivAt_log_norm_vertical (hf t ht).differentiableAt (h0 t ht)
  · exact (continuousOn_im_logDeriv_vertical hf h0).intervalIntegrable

end RiemannHypothesis
