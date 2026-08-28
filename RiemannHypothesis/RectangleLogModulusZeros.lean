/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LogDerivIntegrable
import RiemannHypothesis.LogModulusSegment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The modulus half of Littlewood's lemma, across zeroes

`RiemannHypothesis.RectangleLogModulus` proves

`∫_a^b ∫_c^d re (f′/f)(σ + i t) dt dσ = ∫_c^d (log ‖f(b + i t)‖ − log ‖f(a + i t)‖) dt`

under the hypothesis that `f` has **no zero at all** in the closed rectangle.  For Littlewood's
lemma — and hence for any density estimate — the rectangle must be allowed to contain zeroes:
that is the whole point of the identity.  This file removes the hypothesis.

Two ingredients make this possible.

* `RiemannHypothesis.LogDerivIntegrable` shows that `f′/f` is *locally integrable* across a
  zero: the singularity `k/(z − ρ)` is integrable in two real dimensions.  So Fubini still
  applies, once integrability is transported from `ℂ` to `ℝ × ℝ` along the measure-preserving
  identification.
* The zeroes are finitely many, so all but finitely many horizontal segments miss them, and the
  fundamental theorem of calculus of `RiemannHypothesis.LogModulusSegment` applies for almost
  every height.

## Main results

* `integrableOn_re_logDeriv_prod_of_zeros` — `re (f′/f)` is integrable on the real rectangle,
  zeroes and all.
* `integral_integral_re_logDeriv_swap_of_zeros` — Fubini across the rectangle.
* `integral_integral_re_logDeriv_eq_integral_log_norm_of_zeros` — the identity above, with
  zeroes allowed inside the rectangle.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace RiemannHypothesis

/-- The closed complex rectangle with corners `a + i c` and `b + i d`, described by its real and
imaginary coordinates. -/
def coordRect (a b c d : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

lemma coordRect_eq_image (a b c d : ℝ) :
    coordRect a b c d = (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) '' (Icc a b ×ˢ Icc c d) := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im), ⟨h1, h2⟩, by simp⟩
  · rintro ⟨⟨σ, t⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simpa using h1, by simpa using h2⟩

lemma isCompact_coordRect (a b c d : ℝ) : IsCompact (coordRect a b c d) := by
  rw [coordRect_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

lemma preimage_measurableEquivRealProd (a b c d : ℝ) :
    Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) = coordRect a b c d := by
  ext z
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, coordRect, Set.mem_setOf_eq,
    Complex.measurableEquivRealProd]
  tauto

/-! ## Integrability across the zeroes -/

/-- **`re (f′/f)` is integrable on the real rectangle**, even when `f` has zeroes inside it. -/
theorem integrableOn_re_logDeriv_prod_of_zeros {f : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in 𝓝 ρ, f z = 0)
    (hsub : coordRect a b c d ⊆ U) :
    IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Icc a b ×ˢ Icc c d) volume := by
  have hK : IntegrableOn (logDeriv f) (coordRect a b c d) volume :=
    integrableOn_logDeriv_of_isCompact hU hf hne (isCompact_coordRect a b c d) hsub
  have hKre : IntegrableOn (fun z : ℂ => (logDeriv f z).re) (coordRect a b c d) volume :=
    hK.re
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hme : MeasurableEmbedding (Complex.measurableEquivRealProd) :=
    Complex.measurableEquivRealProd.measurableEmbedding
  rw [← hmp.integrableOn_comp_preimage hme
    (f := fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re) (s := Icc a b ×ˢ Icc c d)]
  rw [preimage_measurableEquivRealProd]
  have hfun : ((fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      ∘ Complex.measurableEquivRealProd) = fun z : ℂ => (logDeriv f z).re := by
    funext z
    simp [Complex.measurableEquivRealProd, Complex.re_add_im]
  rw [hfun]
  exact hKre

/-- **Fubini for `re (f′/f)` across a rectangle containing zeroes.** -/
theorem integral_integral_re_logDeriv_swap_of_zeros {f : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) (hsub : coordRect a b c d ⊆ U) :
    (∫ σ in a..b, ∫ t in c..d, (logDeriv f ((σ : ℂ) + t * I)).re)
      = ∫ t in c..d, ∫ σ in a..b, (logDeriv f ((σ : ℂ) + t * I)).re := by
  have hIcc := integrableOn_re_logDeriv_prod_of_zeros hU hf hne hsub
  have hIoc : IntegrableOn (fun p : ℝ × ℝ => (logDeriv f ((p.1 : ℂ) + p.2 * I)).re)
      (Ioc a b ×ˢ Ioc c d) volume :=
    hIcc.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hprod : Integrable
      (Function.uncurry fun (σ t : ℝ) => (logDeriv f ((σ : ℂ) + t * I)).re)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIoc
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.integral_integral_swap hprod

/-! ## The identity -/

/-- **The modulus half of Littlewood's lemma, with zeroes allowed inside the rectangle.**
Integrating `re (f′/f)` across the rectangle and using Fubini turns it into the integral, over
the height, of the increment of `log ‖f‖` between the two vertical sides.  The only hypotheses
are that `f` is analytic on an open set containing the rectangle, vanishes nowhere identically,
that its zeroes inside the rectangle are finitely many, and that the two vertical sides carry
no zero. -/
theorem integral_integral_re_logDeriv_eq_integral_log_norm_of_zeros {f : ℂ → ℂ} {U : Set ℂ}
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) (hsub : coordRect a b c d ⊆ U)
    (hfin : {z ∈ coordRect a b c d | f z = 0}.Finite) :
    (∫ σ in a..b, ∫ t in c..d, (logDeriv f ((σ : ℂ) + t * I)).re)
      = ∫ t in c..d, (Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖) := by
  rw [integral_integral_re_logDeriv_swap_of_zeros hab hcd hU hf hne hsub]
  -- the heights at which the horizontal segment meets a zero form a finite, hence null, set
  have hbad : ((fun z : ℂ => z.im) '' {z ∈ coordRect a b c d | f z = 0}).Finite := hfin.image _
  have hae : ∀ᵐ t : ℝ, t ∉ (fun z : ℂ => z.im) '' {z ∈ coordRect a b c d | f z = 0} :=
    hbad.countable.ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with t hbadt ht
  rw [Set.uIoc_of_le hcd] at ht
  have htIcc : t ∈ Icc c d := ⟨ht.1.le, ht.2⟩
  have hmem : ∀ σ ∈ Set.uIcc a b, ((σ : ℂ) + t * I) ∈ coordRect a b c d := by
    intro σ hσ
    rw [Set.uIcc_of_le hab] at hσ
    exact ⟨by simpa using hσ, by simpa using htIcc⟩
  refine integral_re_logDeriv_horizontal (fun σ hσ => hf _ (hsub (hmem σ hσ))) ?_
  intro σ hσ hzero
  exact hbadt ⟨(σ : ℂ) + t * I, ⟨hmem σ hσ, hzero⟩, by simp⟩

end RiemannHypothesis
