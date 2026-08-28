/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LogModulusSegment
import RiemannHypothesis.RectangleArgumentPrinciple

/-!
# The log-modulus around the border of a rectangle

`RiemannHypothesis.LogModulusSegment` proves the fundamental theorem of calculus for `log ‖f‖`
along one side of a rectangle: the integral of `re (f′/f)` along a horizontal side, and of
`−im (f′/f)` along a vertical side, is the increment of `log ‖f‖`.  This file assembles the four
sides.  The increments telescope around the closed border, so the *real part* of the contour
integral of `f′/f` vanishes:

* `re_rectangleIntegral_logDeriv_eq_zero` — `re ∮_{∂R} f′/f = 0`.
* `im_rectangleIntegral'_logDeriv_eq_zero`, `rectangleIntegral'_logDeriv_eq_ofReal_re` — the
  normalized integral `(1/2πi) ∮_{∂R} f′/f` is a *real* number.

The hypotheses are only that `f` is analytic and nonvanishing at every point of the *border*:
nothing is assumed inside the rectangle.  That is what makes these statements independent of the
argument principle, which needs analyticity on the whole closed rectangle and then says that the
normalized integral is a natural number.  Where both apply they agree, and the argument principle
is the sharper statement; here the point is that reality of the contour integral is exactly the
half of Littlewood's lemma that the modulus alone gives, with no branch of the logarithm and no
control of what `f` does inside.

`RectangleIntegral`, `RectangleIntegral'`, `HIntegral`, `VIntegral` and `RectangleBorder` are
`Zeta23`'s; the notation `[[a, b]]` is `Set.uIcc`.
-/

open Complex Set MeasureTheory Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

variable {f : ℂ → ℂ} {z w : ℂ}

/-- The real part commutes with an interval integral of an integrable function. -/
private theorem intervalIntegral_re' {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, RCLike.re (g x) = RCLike.re (∫ x in a..b, g x) := by
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_re hg.def',
    RCLike.smul_re, smul_eq_mul]

/-- The imaginary part commutes with an interval integral of an integrable function. -/
private theorem intervalIntegral_im' {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, RCLike.im (g x) = RCLike.im (∫ x in a..b, g x) := by
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_im hg.def',
    RCLike.smul_im, smul_eq_mul]

/-! ## The four sides of the border -/

/-- A point of the horizontal segment at height `t` between `a` and `b`. -/
lemma mem_rectangleBorder_bottom {σ : ℝ} (hσ : σ ∈ [[z.re, w.re]]) :
    (σ : ℂ) + z.im * I ∈ RectangleBorder z w :=
  Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr ⟨by simpa using hσ, by simp⟩)))

/-- A point of the top side of the border. -/
lemma mem_rectangleBorder_top {σ : ℝ} (hσ : σ ∈ [[z.re, w.re]]) :
    (σ : ℂ) + w.im * I ∈ RectangleBorder z w :=
  Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨by simpa using hσ, by simp⟩))

/-- A point of the left side of the border. -/
lemma mem_rectangleBorder_left {t : ℝ} (ht : t ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + t * I ∈ RectangleBorder z w :=
  Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨by simp, by simpa using ht⟩)))

/-- A point of the right side of the border. -/
lemma mem_rectangleBorder_right {t : ℝ} (ht : t ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + t * I ∈ RectangleBorder z w :=
  Or.inr (Complex.mem_reProdIm.mpr ⟨by simp, by simpa using ht⟩)

/-! ## Continuity of `f′/f` along a side -/

/-- `f′/f` is continuous along a horizontal segment on which `f` is analytic and nonvanishing. -/
theorem continuousOn_logDeriv_horizontal {a b t : ℝ}
    (hf : ∀ σ ∈ [[a, b]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + t * I)) [[a, b]] := by
  intro σ hσ
  refine ContinuousAt.continuousWithinAt ?_
  have hpt : ContinuousAt (fun x : ℝ => (x : ℂ) + t * I) σ := by fun_prop
  have hderiv : ContinuousAt (deriv f) ((σ : ℂ) + t * I) := (hf σ hσ).deriv.continuousAt
  have hfc : ContinuousAt f ((σ : ℂ) + t * I) := (hf σ hσ).continuousAt
  have hz : ContinuousAt (fun s : ℂ => logDeriv f s) ((σ : ℂ) + t * I) := by
    simp only [logDeriv]
    exact hderiv.div hfc (h0 σ hσ)
  simpa [Function.comp_def] using
    ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + t * I) hz hpt

/-- `f′/f` is continuous along a vertical segment on which `f` is analytic and nonvanishing. -/
theorem continuousOn_logDeriv_vertical {σ c d : ℝ}
    (hf : ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I)) [[c, d]] := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hpt : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) t := by fun_prop
  have hderiv : ContinuousAt (deriv f) ((σ : ℂ) + t * I) := (hf t ht).deriv.continuousAt
  have hfc : ContinuousAt f ((σ : ℂ) + t * I) := (hf t ht).continuousAt
  have hz : ContinuousAt (fun s : ℂ => logDeriv f s) ((σ : ℂ) + t * I) := by
    simp only [logDeriv]
    exact hderiv.div hfc (h0 t ht)
  simpa [Function.comp_def] using
    ContinuousAt.comp (f := fun y : ℝ => (σ : ℂ) + y * I) hz hpt

/-! ## The real part of the integral along a side -/

/-- **The real part of the integral of `f′/f` along a horizontal side** is the increment of
`log ‖f‖` along it. -/
theorem re_HIntegral_logDeriv {a b t : ℝ}
    (hf : ∀ σ ∈ [[a, b]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I) ≠ 0) :
    (HIntegral (logDeriv f) a b t).re
      = Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖ := by
  have hint : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + t * I)) volume a b :=
    (continuousOn_logDeriv_horizontal hf h0).intervalIntegrable
  have h := intervalIntegral_re' (g := fun x : ℝ => logDeriv f ((x : ℂ) + t * I)) hint
  rw [HIntegral, ← RCLike.re_eq_complex_re, ← h]
  simpa [RCLike.re_eq_complex_re] using integral_re_logDeriv_horizontal hf h0

/-- **The real part of the integral of `f′/f` along a vertical side** is the increment of
`log ‖f‖` along it.  The factor `I` in `VIntegral` turns the real part into minus the imaginary
part of the integrand, which is the derivative of `log ‖f‖` in the vertical direction. -/
theorem re_VIntegral_logDeriv {σ c d : ℝ}
    (hf : ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    (VIntegral (logDeriv f) σ c d).re
      = Real.log ‖f ((σ : ℂ) + d * I)‖ - Real.log ‖f ((σ : ℂ) + c * I)‖ := by
  have hint : IntervalIntegrable (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I)) volume c d :=
    (continuousOn_logDeriv_vertical hf h0).intervalIntegrable
  have h := intervalIntegral_im' (g := fun y : ℝ => logDeriv f ((σ : ℂ) + y * I)) hint
  have hneg : (∫ t in c..d, -(logDeriv f ((σ : ℂ) + t * I)).im)
      = -(∫ t in c..d, logDeriv f ((σ : ℂ) + t * I)).im := by
    rw [intervalIntegral.integral_neg]
    simpa [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] using congrArg Neg.neg h
  rw [VIntegral, smul_eq_mul, Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  rw [← hneg]
  exact integral_im_logDeriv_vertical hf h0

/-! ## Around the border -/

/-- **The real part of the contour integral of `f′/f` around a rectangle vanishes.**  The four
sides contribute the increments of `log ‖f‖`, which telescope around the closed border.  Only
analyticity and nonvanishing *on the border* are assumed: nothing is required of `f` inside the
rectangle, where it may have zeroes or fail to be defined. -/
theorem re_rectangleIntegral_logDeriv_eq_zero
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (RectangleIntegral (logDeriv f) z w).re = 0 := by
  have hb := re_HIntegral_logDeriv (f := f) (a := z.re) (b := w.re) (t := z.im)
    (fun σ hσ => hf _ (mem_rectangleBorder_bottom hσ))
    (fun σ hσ => h0 _ (mem_rectangleBorder_bottom hσ))
  have ht := re_HIntegral_logDeriv (f := f) (a := z.re) (b := w.re) (t := w.im)
    (fun σ hσ => hf _ (mem_rectangleBorder_top hσ))
    (fun σ hσ => h0 _ (mem_rectangleBorder_top hσ))
  have hr := re_VIntegral_logDeriv (f := f) (σ := w.re) (c := z.im) (d := w.im)
    (fun t ht => hf _ (mem_rectangleBorder_right ht))
    (fun t ht => h0 _ (mem_rectangleBorder_right ht))
  have hl := re_VIntegral_logDeriv (f := f) (σ := z.re) (c := z.im) (d := w.im)
    (fun t ht => hf _ (mem_rectangleBorder_left ht))
    (fun t ht => h0 _ (mem_rectangleBorder_left ht))
  rw [RectangleIntegral]
  simp only [Complex.sub_re, Complex.add_re, hb, ht, hr, hl]
  ring

/-- **The normalized contour integral of `f′/f` around a rectangle is real**, as soon as `f` is
analytic and nonvanishing on the border.  When `f` is moreover analytic inside, the argument
principle identifies this real number with the number of zeroes inside. -/
theorem im_rectangleIntegral'_logDeriv_eq_zero
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (RectangleIntegral' (logDeriv f) z w).im = 0 := by
  have h := re_rectangleIntegral_logDeriv_eq_zero hf h0
  have hc : ((1 : ℂ) / (2 * Real.pi * I)).re = 0 := by
    simp [Complex.normSq_apply]
  rw [RectangleIntegral', smul_eq_mul, Complex.mul_im, hc, h]
  ring

/-! ## Fubini across the rectangle -/

/-- `re (f′/f)` is continuous as a function of the two real coordinates on a rectangle on which
`f` is analytic and nonvanishing. -/
theorem continuousOn_re_logDeriv_prod {a b c d : ℝ}
    (hf : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      ([[a, b]] ×ˢ [[c, d]]) := by
  rintro ⟨σ, t⟩ ⟨hσ, ht⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hpt : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) (σ, t) := by fun_prop
  have hderiv : ContinuousAt (deriv f) ((σ : ℂ) + t * I) := (hf σ hσ t ht).deriv.continuousAt
  have hfc : ContinuousAt f ((σ : ℂ) + t * I) := (hf σ hσ t ht).continuousAt
  have hz : ContinuousAt (fun s : ℂ => (logDeriv f s).re) ((σ : ℂ) + t * I) := by
    simp only [logDeriv]
    exact Complex.continuous_re.continuousAt.comp (hderiv.div hfc (h0 σ hσ t ht))
  simpa [Function.comp_def] using
    ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) hz hpt

/-- **Fubini for `re (f′/f)` on a rectangle** on which `f` is analytic and nonvanishing. -/
theorem integral_integral_re_logDeriv_swap {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in a..b, ∫ t in c..d, (logDeriv f ((σ : ℂ) + t * I)).re)
      = ∫ t in c..d, ∫ σ in a..b, (logDeriv f ((σ : ℂ) + t * I)).re := by
  have hcont := continuousOn_re_logDeriv_prod hf h0
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le hcd] at hcont
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hIcc : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Set.Icc a b ×ˢ Set.Icc c d) := hcont.integrableOn_compact hcompact
  have hIoc : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Set.Ioc a b ×ˢ Set.Ioc c d) :=
    hIcc.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hprod : Integrable
      (Function.uncurry fun (σ t : ℝ) => (logDeriv f ((σ : ℂ) + t * I)).re)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIoc
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hprod

/-- **The modulus part of Littlewood's lemma across the rectangle.**  Integrating the vertical
edge term of the contour integral over the position `σ` of the edge and using Fubini turns it
into the integral, over the height, of the increment of `log ‖f‖` between the two vertical
sides. -/
theorem integral_integral_re_logDeriv_eq_integral_log_norm {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in a..b, ∫ t in c..d, (logDeriv f ((σ : ℂ) + t * I)).re)
      = ∫ t in c..d, (Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖) := by
  rw [integral_integral_re_logDeriv_swap hab hcd hf h0]
  refine intervalIntegral.integral_congr fun t ht => ?_
  exact integral_re_logDeriv_horizontal (fun σ hσ => hf σ hσ t ht) (fun σ hσ => h0 σ hσ t ht)

/-- The normalized contour integral of `f′/f` around a rectangle equals the real number that is
its real part. -/
theorem rectangleIntegral'_logDeriv_eq_ofReal_re
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (logDeriv f) z w
      = ((RectangleIntegral' (logDeriv f) z w).re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simpa using re_rectangleIntegral_logDeriv_eq_zero hf h0

end RiemannHypothesis
