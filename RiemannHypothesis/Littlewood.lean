/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ArgumentSegment
import RiemannHypothesis.LogDerivIntegrable

/-!
# Littlewood's lemma

Littlewood's lemma turns the *positions* of the zeroes of an analytic function inside a rectangle
into *boundary data*: an integral of `log ‖f‖` over the two vertical sides, plus increments of a
continuous argument of `f` over the two horizontal sides.  It is the analytic engine of every
zero-density theorem for `ζ`.

The pieces were already in place in this repository:

* `integral_rectangleIntegral'_logDeriv_eq_finsum_of_border` — the counting identity: the
  `σ`-integral of the contour integrals of `f′/f` over the rectangles truncated at `re s = σ` is
  `∑_ρ ord_ρ (re ρ − z.re)`;
* `re_HIntegral_logDeriv`, `re_VIntegral_logDeriv` — the *modulus* half: the real part of the
  integral of `f′/f` along a side is the increment of `log ‖f‖`;
* `RiemannHypothesis.ArgumentSegment` — the *argument* half: the imaginary part of the integral
  of `f′/f` along a side is the increment of a continuous argument of `f`;
* `RiemannHypothesis.LogDerivIntegrable` — `f′/f` is integrable across a rectangle even when
  there are zeroes inside, because `1/‖s − ρ‖` is integrable in two real dimensions.

This file assembles them.  The one genuinely new analytic step is the Fubini exchange
`integral_integral_re_logDeriv_eq_integral_log_norm_of_border`: the double integral of
`re (f′/f)` over the rectangle may be computed in either order *even though the integrand blows
up at the zeroes inside*.  Integrating first in `σ` gives the increment of `log ‖f‖` along a
horizontal line, which is legitimate for all but the finitely many heights that meet a zero — a
null set.

## Main results

* `integrableOn_logDeriv_prod_rectangle` — `(σ, t) ↦ f′/f (σ + i t)` is integrable on the
  rectangle, zeroes inside notwithstanding.
* `integral_integral_re_logDeriv_eq_integral_log_norm_of_border` — the Fubini step.
* `littlewood_lemma` — **Littlewood's lemma**:
  `2π ∑_ρ ord_ρ (re ρ − z.re)` equals the integral over the height of
  `log ‖f‖` on the left side minus `log ‖f‖` on the right side, plus the two horizontal argument
  terms and the right-hand vertical argument term.
* `littlewood_lemma_arg` — the horizontal terms written with an honest continuous argument of `f`
  along the two horizontal sides.
-/

noncomputable section

open Complex Set Metric MeasureTheory Zeta23.Analytic

open scoped Interval Topology

namespace RiemannHypothesis

variable {f : ℂ → ℂ} {z w : ℂ}

/-! ## An open set of analyticity around the rectangle -/

/-- A closed rectangle on which `f` is analytic, and on which `f` does not vanish identically,
sits inside an open set on which `f` is analytic and vanishes nowhere identically.  The open set
is a thickening of the rectangle, hence convex, and the identity theorem propagates the
nonvanishing. -/
theorem exists_open_analytic_of_rectangle (hf : AnalyticOnNhd ℂ f (Rectangle z w)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ Rectangle z w) (hfs₀ : f s₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ Rectangle z w ⊆ U ∧ AnalyticOnNhd ℂ f U ∧
      ∀ ρ ∈ U, ¬ ∀ᶠ y in 𝓝 ρ, f y = 0 := by
  have hA : IsOpen {x : ℂ | AnalyticAt ℂ f x} := isOpen_analyticAt ℂ f
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_rectangle z w).exists_thickening_subset_open hA (fun x hx => hf x hx)
  refine ⟨thickening δ (Rectangle z w), isOpen_thickening, self_subset_thickening hδ _,
    fun x hx => hδsub hx, ?_⟩
  intro ρ hρ hev
  have hconn : IsPreconnected (thickening δ (Rectangle z w)) :=
    ((convex_rectangle z w).thickening δ).isPreconnected
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (f := f) (fun x hx => hδsub hx) hconn hρ (by filter_upwards [hev] with y hy using hy)
  exact hfs₀ (hzero (self_subset_thickening hδ _ hs₀))

/-! ## Integrability of the logarithmic derivative across the rectangle -/

/-- The preimage of a rectangle under the parametrization `(σ, t) ↦ σ + i t`. -/
theorem preimage_rectangle (z w : ℂ) :
    ((fun p : ℝ × ℝ => ((p.1 : ℂ) + p.2 * I)) ⁻¹' Rectangle z w)
      = [[z.re, w.re]] ×ˢ [[z.im, w.im]] := by
  ext p
  simp only [Set.mem_preimage, Rectangle, Complex.mem_reProdIm, Set.mem_prod,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num

/-- **`f′/f` is integrable across the rectangle**, in the two real coordinates, even though it
blows up at each zero of `f` inside: the singularity `1/‖s − ρ‖` is integrable in the plane. -/
theorem integrableOn_logDeriv_prod_rectangle (hf : AnalyticOnNhd ℂ f (Rectangle z w)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ Rectangle z w) (hfs₀ : f s₀ ≠ 0) :
    IntegrableOn (fun p : ℝ × ℝ => logDeriv f ((p.1 : ℂ) + p.2 * I))
      ([[z.re, w.re]] ×ˢ [[z.im, w.im]]) volume := by
  obtain ⟨U, hU, hsub, hfU, hne⟩ := exists_open_analytic_of_rectangle hf hs₀ hfs₀
  have hC : IntegrableOn (logDeriv f) (Rectangle z w) volume :=
    integrableOn_logDeriv_of_isCompact hU hfU hne (isCompact_rectangle z w) hsub
  have hmp : MeasurePreserving (Complex.measurableEquivRealProd.symm) volume volume :=
    (Complex.volume_preserving_equiv_real_prod).symm
  have hme : MeasurableEmbedding (Complex.measurableEquivRealProd.symm) :=
    Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hfun : (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ)
      = fun p : ℝ × ℝ => ((p.1 : ℂ) + p.2 * I) := by
    funext p
    simp [Complex.measurableEquivRealProd, ← Complex.equivRealProdCLM_symm_apply]
  have h := (hmp.integrableOn_comp_preimage hme (f := logDeriv f) (s := Rectangle z w)).2 hC
  rw [hfun, preimage_rectangle] at h
  exact h

/-! ## The Fubini step -/

/-- **The double integral of `re (f′/f)` across a rectangle, computed in both orders.**  The
inner integral in `σ` is the increment of `log ‖f‖` along a horizontal line, which is valid for
all but the finitely many heights that meet a zero of `f`; the exchange of the two integrations
is legitimate because `f′/f` is integrable in two dimensions.  Zeroes inside the rectangle are
allowed: only the border is assumed zero-free. -/
theorem integral_integral_re_logDeriv_eq_integral_log_norm_of_border (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (∫ σ in z.re..w.re, ∫ t in z.im..w.im, (logDeriv f ((σ : ℂ) + t * I)).re)
      = ∫ t in z.im..w.im,
          (Real.log ‖f ((w.re : ℂ) + t * I)‖ - Real.log ‖f ((z.re : ℂ) + t * I)‖) := by
  have hzb : z ∈ RectangleBorder z w := Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hzr : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩
  have hint := integrableOn_logDeriv_prod_rectangle hf hzr (hborder z hzb)
  have hintre : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      ([[z.re, w.re]] ×ˢ [[z.im, w.im]]) volume := hint.re
  have hIoc : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Set.Ioc z.re w.re ×ˢ Set.Ioc z.im w.im) volume := by
    refine hintre.mono_set (Set.prod_mono ?_ ?_)
    · rw [uIcc_of_le hre]; exact Set.Ioc_subset_Icc_self
    · rw [uIcc_of_le him]; exact Set.Ioc_subset_Icc_self
  have hprod : Integrable
      (Function.uncurry fun (σ t : ℝ) => (logDeriv f ((σ : ℂ) + t * I)).re)
      ((volume.restrict (Set.Ioc z.re w.re)).prod (volume.restrict (Set.Ioc z.im w.im))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIoc
  simp_rw [intervalIntegral.integral_of_le hre, intervalIntegral.integral_of_le him]
  rw [integral_integral_swap hprod]
  -- all but finitely many heights avoid the zeroes
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hborder
  have hTfin : ((fun ρ : ℂ => ρ.im) '' rectZeros f z w).Finite := hfin.image _
  have hae : ∀ᵐ t : ℝ, t ∉ (fun ρ : ℂ => ρ.im) '' rectZeros f z w :=
    hTfin.countable.ae_notMem volume
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hae] with t htT ht
  have htmem : t ∈ [[z.im, w.im]] := by
    rw [uIcc_of_le him]; exact ⟨ht.1.le, ht.2⟩
  have hmemrect : ∀ σ ∈ [[z.re, w.re]], ((σ : ℂ) + t * I) ∈ Rectangle z w := by
    intro σ hσ
    exact ⟨by simpa using hσ, by simpa using htmem⟩
  have hne : ∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + t * I) ≠ 0 := by
    intro σ hσ hzero
    exact htT ⟨(σ : ℂ) + t * I, ⟨hmemrect σ hσ, hzero⟩, by simp⟩
  have hanal : ∀ σ ∈ [[z.re, w.re]], AnalyticAt ℂ f ((σ : ℂ) + t * I) :=
    fun σ hσ => hf _ (hmemrect σ hσ)
  have h := integral_re_logDeriv_horizontal (f := f) (a := z.re) (b := w.re) (t := t) hanal hne
  rw [intervalIntegral.integral_of_le hre] at h
  exact h

/-! ## The four sides, in real terms -/

/-- The real part of the normalized contour integral is the imaginary part of the contour
integral, divided by `2π`. -/
theorem re_rectangleIntegral'_eq_im_div (g : ℂ → ℂ) (z w : ℂ) :
    (RectangleIntegral' g z w).re = (RectangleIntegral g z w).im / (2 * Real.pi) := by
  have h1 : (1 / (2 * (Real.pi : ℂ) * I)).re = 0 := by simp [Complex.normSq_apply]
  have h2 : (1 / (2 * (Real.pi : ℂ) * I)).im = -(1 / (2 * Real.pi)) := by
    simp [Complex.normSq_apply]
  rw [RectangleIntegral', smul_eq_mul, Complex.mul_re, h1, h2]
  ring

/-- The real part commutes with an interval integral of a complex-valued function. -/
theorem re_intervalIntegral (g : ℝ → ℂ) {c d : ℝ}
    (hint : IntervalIntegrable g volume c d) :
    (∫ t in c..d, g t).re = ∫ t in c..d, (g t).re := by
  simp only [intervalIntegral, ← RCLike.re_eq_complex_re]
  rw [integral_re hint.1, integral_re hint.2, map_sub]

/-- **The imaginary part of the integral along a vertical side** is the integral of
`re (f′/f)`, which is the derivative of `log ‖f‖` in the horizontal direction. -/
theorem im_VIntegral_eq_integral_re (g : ℂ → ℂ) {σ c d : ℝ}
    (hint : IntervalIntegrable (fun t : ℝ => g ((σ : ℂ) + t * I)) volume c d) :
    (VIntegral g σ c d).im = ∫ t in c..d, (g ((σ : ℂ) + t * I)).re := by
  rw [VIntegral, smul_eq_mul, Complex.mul_im]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  exact re_intervalIntegral _ hint

/-- The argument increment along the horizontal side from `σ` to `b` depends continuously on
`σ`. -/
theorem continuousOn_im_HIntegral_logDeriv {a b t : ℝ}
    (hf : ∀ σ ∈ [[a, b]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => (HIntegral (logDeriv f) σ b t).im) [[a, b]] := by
  have hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + t * I)) [[a, b]] :=
    continuousOn_logDeriv_horizontal hf h0
  have hint : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + t * I)) volume a b :=
    hcont.intervalIntegrable
  have hprim : ContinuousOn
      (fun s : ℝ => ∫ x in b..s, logDeriv f ((x : ℂ) + t * I)) [[a, b]] :=
    intervalIntegral.continuousOn_primitive_interval' hint right_mem_uIcc
  refine ((Complex.continuous_im.comp_continuousOn hprim).neg).congr fun s _ => ?_
  rw [HIntegral, intervalIntegral.integral_symm]
  simp

/-- The inner integral of `re (f′/f)` over the height is integrable in the position `σ` of the
vertical line, by Fubini. -/
theorem intervalIntegrable_integral_re_logDeriv (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    IntervalIntegrable (fun σ : ℝ => ∫ t in z.im..w.im, (logDeriv f ((σ : ℂ) + t * I)).re)
      volume z.re w.re := by
  have hzb : z ∈ RectangleBorder z w := Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hzr : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩
  have hint := integrableOn_logDeriv_prod_rectangle hf hzr (hborder z hzb)
  have hintre : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      ([[z.re, w.re]] ×ˢ [[z.im, w.im]]) volume := hint.re
  have hIoc : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Set.Ioc z.re w.re ×ˢ Set.Ioc z.im w.im) volume := by
    refine hintre.mono_set (Set.prod_mono ?_ ?_)
    · rw [uIcc_of_le hre]; exact Set.Ioc_subset_Icc_self
    · rw [uIcc_of_le him]; exact Set.Ioc_subset_Icc_self
  have hprod : Integrable
      (Function.uncurry fun (σ t : ℝ) => (logDeriv f ((σ : ℂ) + t * I)).re)
      ((volume.restrict (Set.Ioc z.re w.re)).prod (volume.restrict (Set.Ioc z.im w.im))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIoc
  have hleft := hprod.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hre]
  refine hleft.congr ?_
  filter_upwards with σ
  rw [intervalIntegral.integral_of_le him]
  rfl

/-! ## Littlewood's lemma -/

/-- **Littlewood's lemma.**  For `f` analytic on a neighbourhood of the closed rectangle with
corners `z` and `w` and nonvanishing on its border,

`2π ∑_ρ ord_ρ(f) (re ρ − z.re)`
  `= ∫ (log ‖f‖ on the left side − log ‖f‖ on the right side) dt`
  `+ ∫ (argument increment along the bottom side from σ to w.re) dσ`
  `− ∫ (argument increment along the top side from σ to w.re) dσ`
  `+ (w.re − z.re) · (argument increment along the right side)`,

the sum being over the zeroes of `f` inside the rectangle, counted with multiplicity.  The
argument increments appear as the imaginary parts of the integrals of `f′/f` along the sides;
`littlewood_lemma_arg` rewrites the two horizontal ones with a genuine continuous argument. -/
theorem littlewood_lemma (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖f ((z.re : ℂ) + t * I)‖ - Real.log ‖f ((w.re : ℂ) + t * I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv f) w.re z.im w.im).im := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have key := integral_rectangleIntegral'_logDeriv_eq_finsum_of_border hre him hf hborder
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hborder
  have hSfin : ((fun ρ : ℂ => ρ.re) '' rectZeros f z w).Finite := hfin.image _
  have hae : ∀ᵐ σ : ℝ, σ ∉ (fun ρ : ℂ => ρ.re) '' rectZeros f z w :=
    hSfin.countable.ae_notMem volume
  -- the bottom and the top side are zero-free
  have hbot_anal : ∀ σ ∈ [[z.re, w.re]], AnalyticAt ℂ f ((σ : ℂ) + z.im * I) := fun σ hσ =>
    hf _ (rectangleBorder_subset_rectangle z w (mem_rectangleBorder_bottom hσ))
  have hbot_ne : ∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + z.im * I) ≠ 0 := fun σ hσ =>
    hborder _ (mem_rectangleBorder_bottom hσ)
  have htop_anal : ∀ σ ∈ [[z.re, w.re]], AnalyticAt ℂ f ((σ : ℂ) + w.im * I) := fun σ hσ =>
    hf _ (rectangleBorder_subset_rectangle z w (mem_rectangleBorder_top hσ))
  have htop_ne : ∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + w.im * I) ≠ 0 := fun σ hσ =>
    hborder _ (mem_rectangleBorder_top hσ)
  -- integrability of the three nonconstant terms
  have hA : IntervalIntegrable (fun σ : ℝ => (HIntegral (logDeriv f) σ w.re z.im).im)
      volume z.re w.re :=
    (continuousOn_im_HIntegral_logDeriv hbot_anal hbot_ne).intervalIntegrable
  have hB : IntervalIntegrable (fun σ : ℝ => (HIntegral (logDeriv f) σ w.re w.im).im)
      volume z.re w.re :=
    (continuousOn_im_HIntegral_logDeriv htop_anal htop_ne).intervalIntegrable
  have hD : IntervalIntegrable
      (fun σ : ℝ => ∫ t in z.im..w.im, (logDeriv f ((σ : ℂ) + t * I)).re) volume z.re w.re :=
    intervalIntegrable_integral_re_logDeriv hre him hf hborder
  -- rewrite the integrand of the counting identity
  have hcongr : (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re)
      = ∫ σ in z.re..w.re, (1 / (2 * Real.pi)) *
          ((HIntegral (logDeriv f) σ w.re z.im).im
            - (HIntegral (logDeriv f) σ w.re w.im).im
            + (VIntegral (logDeriv f) w.re z.im w.im).im
            - ∫ t in z.im..w.im, (logDeriv f ((σ : ℂ) + t * I)).re) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with σ hσS hσ
    rw [Set.uIoc_of_le hre] at hσ
    have hσ' : σ ∈ [[z.re, w.re]] := by rw [uIcc_of_le hre]; exact ⟨hσ.1.le, hσ.2⟩
    have hmem : ∀ t ∈ [[z.im, w.im]], ((σ : ℂ) + t * I) ∈ Rectangle z w := by
      intro t ht
      exact ⟨by simpa using hσ', by simpa using ht⟩
    have hvert_anal : ∀ t ∈ [[z.im, w.im]], AnalyticAt ℂ f ((σ : ℂ) + t * I) :=
      fun t ht => hf _ (hmem t ht)
    have hvert_ne : ∀ t ∈ [[z.im, w.im]], f ((σ : ℂ) + t * I) ≠ 0 := by
      intro t ht hzero
      exact hσS ⟨(σ : ℂ) + t * I, ⟨hmem t ht, hzero⟩, by simp⟩
    have hvint : IntervalIntegrable (fun t : ℝ => logDeriv f ((σ : ℂ) + t * I)) volume z.im w.im :=
      (continuousOn_logDeriv_vertical hvert_anal hvert_ne).intervalIntegrable
    rw [re_rectangleIntegral'_eq_im_div, RectangleIntegral]
    simp only [leftCorner, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_add, add_zero, Complex.sub_im]
    rw [im_VIntegral_eq_integral_re _ hvint]
    ring
  -- split the integral into its four terms
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (((hA.sub hB).add intervalIntegrable_const)) hD,
    intervalIntegral.integral_add (hA.sub hB) intervalIntegrable_const,
    intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const, smul_eq_mul,
    integral_integral_re_logDeriv_eq_integral_log_norm_of_border hre him hf hborder] at key
  -- and rearrange
  have hflip : (∫ t in z.im..w.im,
        (Real.log ‖f ((z.re : ℂ) + t * I)‖ - Real.log ‖f ((w.re : ℂ) + t * I)‖))
      = -∫ t in z.im..w.im,
        (Real.log ‖f ((w.re : ℂ) + t * I)‖ - Real.log ‖f ((z.re : ℂ) + t * I)‖) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hflip, ← key, ← mul_assoc, mul_one_div, div_self (ne_of_gt hpi), one_mul]
  ring

/-- **Littlewood's lemma, with a genuine argument.**  Same statement as `littlewood_lemma`, with
the two horizontal terms written using continuous branches `θb`, `θt` of the argument of `f`
along the bottom and the top side: no branch cut is chosen, the branches are produced by
integrating `f′/f`. -/
theorem littlewood_lemma_arg (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    ∃ θb θt : ℝ → ℝ, ContinuousOn θb [[z.re, w.re]] ∧ ContinuousOn θt [[z.re, w.re]] ∧
      (∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + z.im * I)
        = (‖f ((σ : ℂ) + z.im * I)‖ : ℂ) * Complex.exp (θb σ * I)) ∧
      (∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + w.im * I)
        = (‖f ((σ : ℂ) + w.im * I)‖ : ℂ) * Complex.exp (θt σ * I)) ∧
      2 * Real.pi * ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
        = (∫ t in z.im..w.im,
              (Real.log ‖f ((z.re : ℂ) + t * I)‖ - Real.log ‖f ((w.re : ℂ) + t * I)‖))
          + (∫ σ in z.re..w.re, (θb w.re - θb σ))
          - (∫ σ in z.re..w.re, (θt w.re - θt σ))
          + (w.re - z.re) * (VIntegral (logDeriv f) w.re z.im w.im).im := by
  have hbot_anal : ∀ σ ∈ [[z.re, w.re]], AnalyticAt ℂ f ((σ : ℂ) + z.im * I) := fun σ hσ =>
    hf _ (rectangleBorder_subset_rectangle z w (mem_rectangleBorder_bottom hσ))
  have hbot_ne : ∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + z.im * I) ≠ 0 := fun σ hσ =>
    hborder _ (mem_rectangleBorder_bottom hσ)
  have htop_anal : ∀ σ ∈ [[z.re, w.re]], AnalyticAt ℂ f ((σ : ℂ) + w.im * I) := fun σ hσ =>
    hf _ (rectangleBorder_subset_rectangle z w (mem_rectangleBorder_top hσ))
  have htop_ne : ∀ σ ∈ [[z.re, w.re]], f ((σ : ℂ) + w.im * I) ≠ 0 := fun σ hσ =>
    hborder _ (mem_rectangleBorder_top hσ)
  obtain ⟨θb, hθbc, hθbp, hθbi⟩ := exists_continuousOn_arg_horizontal hbot_anal hbot_ne
  obtain ⟨θt, hθtc, hθtp, hθti⟩ := exists_continuousOn_arg_horizontal htop_anal htop_ne
  refine ⟨θb, θt, hθbc, hθtc, hθbp, hθtp, ?_⟩
  have hb : (∫ σ in z.re..w.re, (θb w.re - θb σ))
      = ∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re z.im).im := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hre] at hσ
    exact hθbi σ (by rw [uIcc_of_le hre]; exact hσ) w.re (by rw [uIcc_of_le hre]; exact
      ⟨hre, le_rfl⟩)
  have ht : (∫ σ in z.re..w.re, (θt w.re - θt σ))
      = ∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re w.im).im := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hre] at hσ
    exact hθti σ (by rw [uIcc_of_le hre]; exact hσ) w.re (by rw [uIcc_of_le hre]; exact
      ⟨hre, le_rfl⟩)
  rw [hb, ht]
  exact littlewood_lemma hre him hf hborder

end RiemannHypothesis
