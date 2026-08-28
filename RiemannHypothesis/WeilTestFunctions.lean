/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeilPositivity

/-!
# Convolution squares are positive test functions

`RiemannHypothesis.WeilPositivity` states Weil's positivity criterion on the class
`IsPositiveTestFunction` of `C²` compactly supported functions whose transform
`h(r) = ∫ k(u) e^{i r u} du` is real and nonnegative on the real axis.  Nothing there shows
that the class contains anything other than `0`.  This file fills that gap with the classical
construction: for `g` of class `C²` with compact support, the **convolution square**

`k = g ⋆ g^*`,   `g^*(x) = conj (g (-x))`,

is again `C²` with compact support, and its transform is `|ĝ(r)|² ≥ 0`.

## Main results

* `testTransform_ofReal` : the paper's transform is mathlib's Fourier integral,
  `h(r) = 𝓕 k (−r/2π)`.
* `fourier_starReflect` : `𝓕 g^* = conj ∘ 𝓕 g` on the real axis.
* `testTransform_weilSquare` : `h_{g ⋆ g^*}(r) = ‖𝓕 g (−r/2π)‖²`.
* `isPositiveTestFunction_weilSquare` : convolution squares are positive test functions.
* `exists_isPositiveTestFunction_ne_zero` : the class contains a nonzero function, so Weil's
  criterion is not vacuous.
-/

noncomputable section

open MeasureTheory Complex Filter
open scoped FourierTransform Convolution Topology

namespace RiemannHypothesis

/-- The involution `g^*(x) = conj (g (-x))`. -/
def starReflect (g : ℝ → ℂ) : ℝ → ℂ := fun x => (starRingEnd ℂ) (g (-x))

/-- The convolution square `g ⋆ g^*`. -/
def weilSquare (g : ℝ → ℂ) : ℝ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] starReflect g

lemma continuous_starReflect {g : ℝ → ℂ} (hg : Continuous g) : Continuous (starReflect g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)

lemma hasCompactSupport_starReflect {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (starReflect g) :=
  (hg.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := (starRingEnd ℂ)) (by simp)

lemma contDiff_starReflect {n : ℕ} {g : ℝ → ℂ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (starReflect g) := by
  have hconj : ContDiff ℝ n (fun z : ℂ => (starRingEnd ℂ) z) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff
  exact hconj.comp (hg.comp contDiff_neg)

lemma integrable_starReflect {g : ℝ → ℂ} (hg : Integrable g) : Integrable (starReflect g) := by
  have h1 : Integrable (fun x : ℝ => g (-x)) volume := hg.comp_neg
  refine Integrable.mono' h1.norm ?_ (Eventually.of_forall fun x => ?_)
  · exact Complex.continuous_conj.comp_aestronglyMeasurable h1.aestronglyMeasurable
  · simp [starReflect]

/-- The transform used in the explicit formula is mathlib's Fourier integral, evaluated at
`−r/2π`. -/
lemma testTransform_ofReal (k : ℝ → ℂ) (r : ℝ) :
    testTransform k (r : ℂ) = 𝓕 k (-(r / (2 * Real.pi))) := by
  change Zeta23.paperFT k (r : ℂ) = _
  rw [Zeta23.paperFT, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- The Fourier transform of `g^*` is the conjugate of that of `g`, on the real axis. -/
lemma fourier_starReflect (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (starReflect g) ξ = (starRingEnd ℂ) (𝓕 g ξ) := by
  change 𝓕 (fun x => (starRingEnd ℂ) (g (-x))) ξ = _
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← MeasureTheory.integral_neg_eq_self (fun x : ℝ =>
    Complex.exp (((-2 * Real.pi * x * ξ : ℝ)) * Complex.I) • (starRingEnd ℂ) (g (-x)))]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, neg_neg, map_mul, ← Complex.exp_conj]
  have hexp : ((-2 * Real.pi * -v * ξ : ℝ) : ℂ) * I
      = (starRingEnd ℂ) ((-2 * Real.pi * v * ξ : ℝ) : ℂ) * (starRingEnd ℂ) I := by
    rw [Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hexp]

/-- The transform of a convolution square is `|ĝ|²`. -/
theorem testTransform_weilSquare {g : ℝ → ℂ} (hg : Integrable g) (r : ℝ) :
    testTransform (weilSquare g) (r : ℂ) = ((‖𝓕 g (-(r / (2 * Real.pi)))‖ ^ 2 : ℝ) : ℂ) := by
  have hstar : Integrable (starReflect g) := integrable_starReflect hg
  rw [testTransform_ofReal, weilSquare,
    Real.fourier_mul_convolution_eq hg hstar,
    fourier_starReflect, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- **Convolution squares are positive test functions.** -/
theorem isPositiveTestFunction_weilSquare {g : ℝ → ℂ} (hg2 : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : IsPositiveTestFunction (weilSquare g) := by
  have hcont : Continuous g := hg2.continuous
  have hint : Integrable g := hcont.integrable_of_hasCompactSupport hgc
  refine ⟨?_, ?_, ?_⟩
  · exact (hasCompactSupport_starReflect hgc).contDiff_convolution_right
      (μ := volume) (L := ContinuousLinearMap.mul ℝ ℂ) (hcont.locallyIntegrable (μ := volume))
      (contDiff_starReflect hg2)
  · exact hgc.convolution (μ := volume) (L := ContinuousLinearMap.mul ℂ ℂ)
      (hasCompactSupport_starReflect hgc)
  · intro r
    exact ⟨‖𝓕 g (-(r / (2 * Real.pi)))‖ ^ 2, by positivity, testTransform_weilSquare hint r⟩

/-- The value of a convolution square at the origin is the `L²` norm of `g`. -/
theorem weilSquare_zero (g : ℝ → ℂ) :
    weilSquare g 0 = ∫ t : ℝ, ((‖g t‖ ^ 2 : ℝ) : ℂ) := by
  rw [weilSquare, convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [starReflect, zero_sub, neg_neg, ContinuousLinearMap.mul_apply']
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- **The class of positive test functions is not trivial**: it contains a function that is
nonzero at the origin, so Weil's criterion is not vacuous. -/
theorem exists_isPositiveTestFunction_ne_zero :
    ∃ k : ℝ → ℂ, IsPositiveTestFunction k ∧ k ≠ 0 := by
  set b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩ with hb
  set g : ℝ → ℂ := fun x => ((b x : ℝ) : ℂ) with hgdef
  have hbcont : Continuous fun x : ℝ => (b x : ℝ) := b.continuous
  have hg2 : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp (b.contDiff (n := 2))
  have hgc : HasCompactSupport g :=
    b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero
  refine ⟨weilSquare g, isPositiveTestFunction_weilSquare hg2 hgc, ?_⟩
  intro hzero
  have hval : weilSquare g 0 = 0 := by rw [hzero]; rfl
  rw [weilSquare_zero] at hval
  have hre : ∫ t : ℝ, ‖g t‖ ^ 2 = 0 := by
    rw [integral_complex_ofReal] at hval
    exact_mod_cast hval
  have hsupp : HasCompactSupport fun t : ℝ => ‖g t‖ ^ 2 :=
    hgc.norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hpos : 0 < ∫ t : ℝ, ‖g t‖ ^ 2 := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (by fun_prop) hsupp (fun x => by positivity) ?_
    have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [hgdef, hb0]
  exact absurd hre (ne_of_gt hpos)

end RiemannHypothesis

end
