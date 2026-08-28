/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.RectangleLogModulus

/-!
# A continuous branch of the argument along a segment, and the integrality of the winding number

`RiemannHypothesis.LogModulusSegment` and `RiemannHypothesis.RectangleLogModulus` prove the half
of Littlewood's lemma that needs no branch of the logarithm: along a side of a rectangle on which
`f` is analytic and nonvanishing, the real part of the integral of `f′/f` is the increment of
`log ‖f‖`, and around the closed border those increments telescope, so the contour integral of
`f′/f` is a real number.  This file proves the *other* half, the one that does need a branch: the
imaginary part of the integral of `f′/f` along a segment is the increment of a continuous
argument of `f` along that segment.

The branch is constructed, not assumed.  For a nonvanishing differentiable `g : ℝ → ℂ` the
primitive `F u = ∫_a^u g′/g` satisfies `(g · exp (-F))′ = 0`, hence

`exp (∫_a^b g′/g) = g b / g a`  (`exp_integral_logDeriv_comp`),

and `θ u = arg (g a) + im (F u)` is a continuous argument of `g` along the segment
(`exists_continuousOn_arg`): `g u = ‖g u‖ · exp (i θ u)` for every `u`, and each increment
`θ v - θ u` is the imaginary part of the integral of `g′/g` from `u` to `v`.  No branch cut and
no analytic continuation is involved; the logarithm is built by integration.

Applied to the four sides of a rectangle, the ratios telescope, so

`exp (∮_{∂R} f′/f) = 1`  (`exp_rectangleIntegral_logDeriv_eq_one`),

which says exactly that the winding number `(1/2πi) ∮_{∂R} f′/f` is an **integer**
(`exists_int_rectangleIntegral'_logDeriv`), under the sole hypothesis that `f` is analytic and
nonvanishing *on the border*: nothing is assumed inside the rectangle, where `f` may have zeroes,
poles, or not be defined at all.  The argument principle, which does assume analyticity inside,
identifies that integer with the number of zeroes; here the integrality itself is unconditional.
Together with `im_rectangleIntegral'_logDeriv_eq_zero` (the modulus half) this upgrades "the
normalized contour integral is real" to "it is an integer".

## Main results

* `exp_integral_logDeriv_comp` — `exp (∫_a^b g′/g) = g b / g a` for `g : ℝ → ℂ` differentiable
  and nonvanishing on the segment.
* `exists_continuousOn_arg` — a continuous branch of the argument of `g` along the segment, whose
  increments are the imaginary parts of the integrals of `g′/g`.
* `exists_continuousOn_arg_horizontal` — the same for a horizontal side of a rectangle, with the
  increments written as `HIntegral (logDeriv f)`.
* `exp_HIntegral_logDeriv`, `exp_VIntegral_logDeriv` — the same for a horizontal, respectively a
  vertical, side of a rectangle, in the vocabulary of `Zeta23`'s `HIntegral` and `VIntegral`.
* `exp_rectangleIntegral_logDeriv_eq_one`, `exists_int_rectangleIntegral_logDeriv`,
  `exists_int_rectangleIntegral'_logDeriv` — the contour integral around the border lies in
  `2πi ℤ`, and the normalized one is an integer.
-/

open Complex Set MeasureTheory Filter Topology Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

/-! ## The exponential of the integral of the logarithmic derivative -/

/-- **The exponential of the integral of `g′/g`**, for an increasing segment.  The proof
differentiates `g · exp (-F)`, where `F` is the primitive of `g′/g` given by the fundamental
theorem of calculus, and finds derivative zero. -/
theorem exp_integral_logDeriv_comp_of_le {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (h0 : ∀ x ∈ Icc a b, g x ≠ 0)
    (hc : ContinuousOn (fun x => g' x / g x) (Icc a b)) :
    Complex.exp (∫ x in a..b, g' x / g x) = g b / g a := by
  have hcu : ContinuousOn (fun x => g' x / g x) (uIcc a b) := by rwa [uIcc_of_le hab]
  have hintab : IntervalIntegrable (fun x => g' x / g x) volume a b := hcu.intervalIntegrable
  have hint : ∀ u ∈ Icc a b, IntervalIntegrable (fun x => g' x / g x) volume a u := fun u hu =>
    hintab.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hu.1]; exact Icc_subset_Icc le_rfl hu.2)
  have hFderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun u => ∫ y in a..u, g' y / g y) (g' x / g x) (Ici x) x := by
    intro x hx
    have hsub : 𝓝[>] x ≤ 𝓝[Icc a b] x :=
      nhdsWithin_le_iff.2 (mem_of_superset (Ioc_mem_nhdsGT hx.2)
        (fun y hy => ⟨le_trans hx.1 hy.1.le, hy.2⟩))
    have hcw : ContinuousWithinAt (fun x => g' x / g x) (Ioi x) x :=
      (hc x ⟨hx.1, hx.2.le⟩).mono_left hsub
    have hmeas : StronglyMeasurableAtFilter (fun x => g' x / g x) (𝓝[>] x) volume :=
      ⟨Icc a b, hsub self_mem_nhdsWithin, hc.aestronglyMeasurable measurableSet_Icc⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hint x ⟨hx.1, hx.2.le⟩) hmeas hcw
  have hcontF : ContinuousOn (fun u => ∫ y in a..u, g' y / g y) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume) hintab
      (a := a) (by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
    rwa [uIcc_of_le hab] at h
  have hcontg : ContinuousOn g (Icc a b) := fun x hx => ((hg x hx).continuousAt).continuousWithinAt
  have hconth : ContinuousOn (fun u => g u * Complex.exp (-∫ y in a..u, g' y / g y)) (Icc a b) :=
    hcontg.mul ((hcontF.neg).cexp)
  have hderiv0 : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun u => g u * Complex.exp (-∫ y in a..u, g' y / g y)) 0 (Ici x) x := by
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
    have hgx : g x ≠ 0 := h0 x hx'
    have h1 : HasDerivWithinAt g (g' x) (Ici x) x := (hg x hx').hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun u => Complex.exp (-∫ y in a..u, g' y / g y))
        (Complex.exp (-∫ y in a..x, g' y / g y) * (-(g' x / g x))) (Ici x) x := by
      simpa using ((hFderiv x hx).neg).cexp
    have hmul := h1.mul h2
    have heq : g' x * Complex.exp (-∫ y in a..x, g' y / g y)
        + g x * (Complex.exp (-∫ y in a..x, g' y / g y) * (-(g' x / g x))) = 0 := by
      field_simp; ring
    rw [heq] at hmul
    exact hmul
  have hconst := constant_of_has_deriv_right_zero hconth hderiv0 b ⟨hab, le_rfl⟩
  have hga : g a ≠ 0 := h0 a ⟨le_rfl, hab⟩
  have key : g b * Complex.exp (-∫ y in a..b, g' y / g y) = g a := by simpa using hconst
  have hfin : g a * Complex.exp (∫ y in a..b, g' y / g y) = g b := by
    rw [← key, Complex.exp_neg]; field_simp
  rw [eq_div_iff hga, mul_comm]
  exact hfin

/-- **The exponential of the integral of `g′/g` along a segment**, in either direction:
`exp (∫_a^b g′/g) = g b / g a` as soon as `g` is differentiable and nonvanishing on the segment
joining `a` and `b`, with continuous logarithmic derivative there. -/
theorem exp_integral_logDeriv_comp {g g' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ [[a, b]], HasDerivAt g (g' x) x) (h0 : ∀ x ∈ [[a, b]], g x ≠ 0)
    (hc : ContinuousOn (fun x => g' x / g x) [[a, b]]) :
    Complex.exp (∫ x in a..b, g' x / g x) = g b / g a := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hg h0 hc
    exact exp_integral_logDeriv_comp_of_le hab hg h0 hc
  · rw [uIcc_comm, uIcc_of_le hba] at hg h0 hc
    have h := exp_integral_logDeriv_comp_of_le hba hg h0 hc
    have hga : g a ≠ 0 := h0 a ⟨hba, le_rfl⟩
    have hgb : g b ≠ 0 := h0 b ⟨le_rfl, hba⟩
    rw [intervalIntegral.integral_symm, Complex.exp_neg, h]
    field_simp

/-- **A continuous branch of the argument along a segment.**  If `g` is differentiable and
nonvanishing on the segment joining `a` and `b`, with continuous logarithmic derivative, then
there is a continuous real function `θ` with `g u = ‖g u‖ · exp (i θ u)` on the segment, whose
increments `θ v - θ u` are the imaginary parts of `∫_u^v g′/g`.  This is the half of Littlewood's
lemma that needs a logarithm: the logarithm is built here by integration, so no branch cut is
chosen and no monodromy is assumed away. -/
theorem exists_continuousOn_arg {g g' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ [[a, b]], HasDerivAt g (g' x) x) (h0 : ∀ x ∈ [[a, b]], g x ≠ 0)
    (hc : ContinuousOn (fun x => g' x / g x) [[a, b]]) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ [[a, b]] ∧
      (∀ u ∈ [[a, b]], g u = (‖g u‖ : ℂ) * Complex.exp (θ u * I)) ∧
      ∀ u ∈ [[a, b]], ∀ v ∈ [[a, b]], θ v - θ u = (∫ x in u..v, g' x / g x).im := by
  have hintab : IntervalIntegrable (fun x => g' x / g x) volume a b := hc.intervalIntegrable
  set F : ℝ → ℂ := fun u => ∫ y in a..u, g' y / g y with hF
  refine ⟨fun u => (g a).arg + (F u).im, ?_, ?_, ?_⟩
  · have hcontF : ContinuousOn F [[a, b]] :=
      intervalIntegral.continuousOn_primitive_interval' (μ := volume) hintab left_mem_uIcc
    exact continuousOn_const.add (Complex.continuous_im.comp_continuousOn hcontF)
  · intro u hu
    have hsub : [[a, u]] ⊆ [[a, b]] := uIcc_subset_uIcc left_mem_uIcc hu
    have hexp : Complex.exp (F u) = g u / g a :=
      exp_integral_logDeriv_comp (fun x hx => hg x (hsub hx)) (fun x hx => h0 x (hsub hx))
        (hc.mono hsub)
    have hga : g a ≠ 0 := h0 a left_mem_uIcc
    have hgu : g u = g a * Complex.exp (F u) := by
      rw [hexp]; field_simp
    have harg : g a = (‖g a‖ : ℂ) * Complex.exp (((g a).arg : ℝ) * I) :=
      (Complex.norm_mul_exp_arg_mul_I (g a)).symm
    have hsplit : Complex.exp (F u)
        = (Real.exp (F u).re : ℂ) * Complex.exp (((F u).im : ℝ) * I) := by
      conv_lhs => rw [← Complex.re_add_im (F u)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    rw [hgu, norm_mul, Complex.norm_exp, Complex.ofReal_add, add_mul, Complex.exp_add]
    push_cast
    conv_lhs => rw [harg, hsplit]
    rw [Complex.ofReal_exp]
    ring
  · intro u hu v hv
    have hiu : IntervalIntegrable (fun x => g' x / g x) volume a u :=
      hintab.mono_set (uIcc_subset_uIcc left_mem_uIcc hu)
    have hiv : IntervalIntegrable (fun x => g' x / g x) volume a v :=
      hintab.mono_set (uIcc_subset_uIcc left_mem_uIcc hv)
    have hsub : F v - F u = ∫ x in u..v, g' x / g x :=
      intervalIntegral.integral_interval_sub_left hiv hiu
    rw [← hsub, Complex.sub_im]
    ring

/-! ## The sides of a rectangle -/

variable {f : ℂ → ℂ} {z w : ℂ}

/-- **The exponential of the integral of `f′/f` along a horizontal side**: the ratio of the
values of `f` at the two endpoints. -/
theorem exp_HIntegral_logDeriv {a b t : ℝ}
    (hf : ∀ σ ∈ [[a, b]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I) ≠ 0) :
    Complex.exp (HIntegral (logDeriv f) a b t)
      = f ((b : ℂ) + t * I) / f ((a : ℂ) + t * I) := by
  have hderiv : ∀ σ ∈ [[a, b]], HasDerivAt (fun x : ℝ => f ((x : ℂ) + t * I))
      (deriv f ((σ : ℂ) + t * I)) σ := fun σ hσ =>
    hasDerivAt_horizontal (hf σ hσ).differentiableAt
  have hcont : ContinuousOn
      (fun x : ℝ => deriv f ((x : ℂ) + t * I) / f ((x : ℂ) + t * I)) [[a, b]] := by
    simpa [logDeriv] using continuousOn_logDeriv_horizontal hf h0
  have h := exp_integral_logDeriv_comp (g := fun x : ℝ => f ((x : ℂ) + t * I))
    (g' := fun x : ℝ => deriv f ((x : ℂ) + t * I)) hderiv h0 hcont
  simpa [HIntegral, logDeriv] using h

/-- **A continuous branch of the argument along a horizontal side.**  If `f` is analytic and
nonvanishing at every point of the horizontal segment at height `t` between the abscissae `a`
and `b`, there is a continuous `θ` with `f (σ + i t) = ‖f (σ + i t)‖ · exp (i θ σ)`, whose
increments are the imaginary parts of the integrals of `f′/f` along the corresponding
subsegments. -/
theorem exists_continuousOn_arg_horizontal {a b t : ℝ}
    (hf : ∀ σ ∈ [[a, b]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I) ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ [[a, b]] ∧
      (∀ σ ∈ [[a, b]], f ((σ : ℂ) + t * I)
        = (‖f ((σ : ℂ) + t * I)‖ : ℂ) * Complex.exp (θ σ * I)) ∧
      ∀ u ∈ [[a, b]], ∀ v ∈ [[a, b]], θ v - θ u = (HIntegral (logDeriv f) u v t).im := by
  have hderiv : ∀ σ ∈ [[a, b]], HasDerivAt (fun x : ℝ => f ((x : ℂ) + t * I))
      (deriv f ((σ : ℂ) + t * I)) σ := fun σ hσ =>
    hasDerivAt_horizontal (hf σ hσ).differentiableAt
  have hcont : ContinuousOn
      (fun x : ℝ => deriv f ((x : ℂ) + t * I) / f ((x : ℂ) + t * I)) [[a, b]] := by
    simpa [logDeriv] using continuousOn_logDeriv_horizontal hf h0
  obtain ⟨θ, hθc, hθp, hθi⟩ := exists_continuousOn_arg (g := fun x : ℝ => f ((x : ℂ) + t * I))
    (g' := fun x : ℝ => deriv f ((x : ℂ) + t * I)) hderiv h0 hcont
  refine ⟨θ, hθc, hθp, fun u hu v hv => ?_⟩
  simpa [HIntegral, logDeriv] using hθi u hu v hv

/-- **The exponential of the integral of `f′/f` along a vertical side**: the ratio of the values
of `f` at the two endpoints.  The factor `I` in `VIntegral` is exactly the derivative of the
parametrization `y ↦ σ + i y`. -/
theorem exp_VIntegral_logDeriv {σ c d : ℝ}
    (hf : ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ [[c, d]], f ((σ : ℂ) + t * I) ≠ 0) :
    Complex.exp (VIntegral (logDeriv f) σ c d)
      = f ((σ : ℂ) + d * I) / f ((σ : ℂ) + c * I) := by
  have hderiv : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => f ((σ : ℂ) + y * I))
      (deriv f ((σ : ℂ) + y * I) * I) y := fun y hy =>
    hasDerivAt_vertical (hf y hy).differentiableAt
  have hcont : ContinuousOn
      (fun y : ℝ => deriv f ((σ : ℂ) + y * I) * I / f ((σ : ℂ) + y * I)) [[c, d]] := by
    have h : ContinuousOn (fun y : ℝ => I * logDeriv f ((σ : ℂ) + y * I)) [[c, d]] :=
      continuousOn_const.mul (continuousOn_logDeriv_vertical hf h0)
    exact h.congr fun y _ => by simp only [logDeriv, Pi.div_apply]; ring
  have h := exp_integral_logDeriv_comp (g := fun y : ℝ => f ((σ : ℂ) + y * I))
    (g' := fun y : ℝ => deriv f ((σ : ℂ) + y * I) * I) hderiv h0 hcont
  have hI : (∫ y in c..d, deriv f ((σ : ℂ) + y * I) * I / f ((σ : ℂ) + y * I))
      = VIntegral (logDeriv f) σ c d := by
    rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [logDeriv, Pi.div_apply]
    ring
  rwa [hI] at h

/-- **A continuous branch of the argument along a vertical side.**  If `f` is analytic and
nonvanishing at every point of the vertical segment at abscissa `sigma` between the heights `c`
and `d`, there is a continuous `theta` with `f (sigma + i t) = ‖f (sigma + i t)‖ · exp (i theta t)`,
whose increments are the imaginary parts of the integrals of `f′/f` along the corresponding
subsegments. -/
theorem exists_continuousOn_arg_vertical {sigma c d : ℝ}
    (hf : ∀ t ∈ [[c, d]], AnalyticAt ℂ f ((sigma : ℂ) + t * I))
    (h0 : ∀ t ∈ [[c, d]], f ((sigma : ℂ) + t * I) ≠ 0) :
    ∃ theta : ℝ → ℝ, ContinuousOn theta [[c, d]] ∧
      (∀ t ∈ [[c, d]], f ((sigma : ℂ) + t * I)
        = (‖f ((sigma : ℂ) + t * I)‖ : ℂ) * Complex.exp (theta t * I)) ∧
      ∀ u ∈ [[c, d]], ∀ v ∈ [[c, d]],
        theta v - theta u = (VIntegral (logDeriv f) sigma u v).im := by
  have hderiv : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => f ((sigma : ℂ) + y * I))
      (deriv f ((sigma : ℂ) + y * I) * I) y := fun y hy =>
    hasDerivAt_vertical (hf y hy).differentiableAt
  have hcont : ContinuousOn
      (fun y : ℝ => deriv f ((sigma : ℂ) + y * I) * I / f ((sigma : ℂ) + y * I)) [[c, d]] := by
    have h : ContinuousOn (fun y : ℝ => I * logDeriv f ((sigma : ℂ) + y * I)) [[c, d]] :=
      continuousOn_const.mul (continuousOn_logDeriv_vertical hf h0)
    exact h.congr fun y _ => by simp only [logDeriv, Pi.div_apply]; ring
  obtain ⟨theta, hthetac, hthetap, hthetai⟩ :=
    exists_continuousOn_arg (g := fun y : ℝ => f ((sigma : ℂ) + y * I))
      (g' := fun y : ℝ => deriv f ((sigma : ℂ) + y * I) * I) hderiv h0 hcont
  refine ⟨theta, hthetac, hthetap, fun u hu v hv => ?_⟩
  have hI : (∫ y in u..v, deriv f ((sigma : ℂ) + y * I) * I / f ((sigma : ℂ) + y * I))
      = VIntegral (logDeriv f) sigma u v := by
    rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [logDeriv, Pi.div_apply]
    ring
  rw [hthetai u hu v hv, hI]

/-! ## Around the border: the winding number is an integer -/

/-- **The exponential of the contour integral of `f′/f` around a rectangle is `1`.**  The four
sides contribute the ratios of the values of `f` at the corners, and these telescope.  Only
analyticity and nonvanishing *on the border* are assumed. -/
theorem exp_rectangleIntegral_logDeriv_eq_one
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    Complex.exp (RectangleIntegral (logDeriv f) z w) = 1 := by
  have hb := exp_HIntegral_logDeriv (f := f) (a := z.re) (b := w.re) (t := z.im)
    (fun σ hσ => hf _ (mem_rectangleBorder_bottom hσ))
    (fun σ hσ => h0 _ (mem_rectangleBorder_bottom hσ))
  have ht := exp_HIntegral_logDeriv (f := f) (a := z.re) (b := w.re) (t := w.im)
    (fun σ hσ => hf _ (mem_rectangleBorder_top hσ))
    (fun σ hσ => h0 _ (mem_rectangleBorder_top hσ))
  have hr := exp_VIntegral_logDeriv (f := f) (σ := w.re) (c := z.im) (d := w.im)
    (fun t ht => hf _ (mem_rectangleBorder_right ht))
    (fun t ht => h0 _ (mem_rectangleBorder_right ht))
  have hl := exp_VIntegral_logDeriv (f := f) (σ := z.re) (c := z.im) (d := w.im)
    (fun t ht => hf _ (mem_rectangleBorder_left ht))
    (fun t ht => h0 _ (mem_rectangleBorder_left ht))
  have hzz : f ((z.re : ℂ) + z.im * I) ≠ 0 :=
    h0 _ (mem_rectangleBorder_bottom left_mem_uIcc)
  have hwz : f ((w.re : ℂ) + z.im * I) ≠ 0 :=
    h0 _ (mem_rectangleBorder_bottom right_mem_uIcc)
  have hzw : f ((z.re : ℂ) + w.im * I) ≠ 0 :=
    h0 _ (mem_rectangleBorder_top left_mem_uIcc)
  have hww : f ((w.re : ℂ) + w.im * I) ≠ 0 :=
    h0 _ (mem_rectangleBorder_top right_mem_uIcc)
  rw [RectangleIntegral, Complex.exp_sub, Complex.exp_add, Complex.exp_sub, hb, ht, hr, hl]
  field_simp
  rw [div_self (mul_ne_zero (by simpa [mul_comm] using hww) (by simpa [mul_comm] using hzw))]

/-- **The contour integral of `f′/f` around a rectangle lies in `2πi ℤ`**, assuming only that `f`
is analytic and nonvanishing on the border.  Nothing is assumed inside the rectangle. -/
theorem exists_int_rectangleIntegral_logDeriv
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    ∃ n : ℤ, RectangleIntegral (logDeriv f) z w = (n : ℂ) * (2 * Real.pi * I) :=
  Complex.exp_eq_one_iff.1 (exp_rectangleIntegral_logDeriv_eq_one hf h0)

/-- **The winding number of `f` around the border of a rectangle is an integer.**  The normalized
contour integral `(1/2πi) ∮_{∂R} f′/f` is an integer as soon as `f` is analytic and nonvanishing
on the border; the argument principle, which needs analyticity inside as well, identifies that
integer with the number of zeroes of `f` inside the rectangle. -/
theorem exists_int_rectangleIntegral'_logDeriv
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    ∃ n : ℤ, RectangleIntegral' (logDeriv f) z w = (n : ℂ) := by
  obtain ⟨n, hn⟩ := exists_int_rectangleIntegral_logDeriv hf h0
  refine ⟨n, ?_⟩
  have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [RectangleIntegral', smul_eq_mul, hn]
  field_simp

end RiemannHypothesis
