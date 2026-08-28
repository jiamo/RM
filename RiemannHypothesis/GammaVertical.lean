/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Complex.PhragmenLindelof
import RiemannHypothesis.ImaginaryAxis
import RiemannHypothesis.Convexity

/-!
# Exponential decay of `Γ` on vertical lines

Stirling's formula gives `|Γ(σ + i t)| ≍ |t| ^ (σ - 1/2) e ^ (-π |t| / 2)` uniformly for `σ` in a
bounded interval, but complex Stirling asymptotics are not available in Mathlib.  This file
proves the *upper* half of that estimate, which is what the zero-counting arguments need, by a
Phragmén–Lindelöf argument that uses only Euler's reflection formula.

The point is that the entire function `cos (π s / 2)` grows exactly like `e ^ (π |t| / 2)` in the
imaginary direction, and that on the two vertical lines `re s = 1/2` and `re s = 3` the product
`Γ(s) cos (π s / 2)` has a closed form:

* `‖Γ(1/2 + i t)‖ ^ 2 = π / cosh (π t)` and `‖cos (π (1/2 + i t) / 2)‖ ^ 2 = cosh (π t) / 2`, so
  the product is the constant `√(π/2)`;
* `‖Γ(1 + i t)‖ ^ 2 = π t / sinh (π t)` (already in `RiemannHypothesis.ImaginaryAxis`) and the
  recurrence `Γ(3 + i t) = (2 + i t)(1 + i t) Γ(1 + i t)` bound the product on `re s = 3` by a
  polynomial in `t`.

Dividing by `(s + 3) ^ 3` to absorb that polynomial and applying Phragmén–Lindelöf in the strip
`1/2 ≤ re s ≤ 3` gives `‖Γ(s) cos (π s / 2)‖ ≤ 2 ‖s + 3‖ ^ 3` there, and `‖cos (π s / 2)‖ ≥
|sinh (π t / 2)|` converts this into the decay estimate.

## Main results

* `norm_Gamma_mul_cos_le_of_mem_strip` : `‖Γ(s) cos (π s / 2)‖ ≤ 2 ‖s + 3‖ ^ 3` for
  `1/2 ≤ re s ≤ 3`.
* `norm_Gamma_le_exp_neg` : `‖Γ(s)‖ ≤ 8 ‖s + 3‖ ^ 3 e ^ (-π |t| / 2)` for `1/2 ≤ re s ≤ 3`,
  `|t| ≥ 1`.
* `norm_Gamma_le_exp_decay` : the same with the strip widened to `1/4 ≤ re s ≤ 5`, in the form
  `‖Γ(s)‖ ≤ 8 (5 + ‖s‖) ^ 5 e ^ (-π |t| / 2)`.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace RiemannHypothesis

/-! ## The modulus of the cosine factor -/

/-- `‖cos (x + i y)‖ ^ 2 = cos x ^ 2 + sinh y ^ 2`. -/
lemma norm_cos_add_mul_I_sq (x y : ℝ) :
    ‖Complex.cos ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  nlinarith [Real.cosh_sq_sub_sinh_sq y, Real.sin_sq_add_cos_sq x]

/-- The cosine factor `cos (π s / 2)`, written out in terms of the real and imaginary parts of
`s`. -/
lemma norm_cos_pi_div_two_sq (s : ℂ) :
    ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2
      = Real.cos (Real.pi * s.re / 2) ^ 2 + Real.sinh (Real.pi * s.im / 2) ^ 2 := by
  have h : (Real.pi : ℂ) * s / 2
      = ((Real.pi * s.re / 2 : ℝ) : ℂ) + ((Real.pi * s.im / 2 : ℝ) : ℂ) * I := by
    rw [← Complex.re_add_im s]
    push_cast
    simp [Complex.ext_iff]
  rw [h, norm_cos_add_mul_I_sq]

/-- The cosine factor is at least `|sinh (π t / 2)|` in modulus. -/
lemma abs_sinh_le_norm_cos (s : ℂ) :
    |Real.sinh (Real.pi * s.im / 2)| ≤ ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ := by
  have h := norm_cos_pi_div_two_sq s
  have h1 : Real.sinh (Real.pi * s.im / 2) ^ 2
      ≤ ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg (Real.cos (Real.pi * s.re / 2))]
  have h2 : |Real.sinh (Real.pi * s.im / 2)| ^ 2 ≤ ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2 := by
    rwa [sq_abs]
  nlinarith [abs_nonneg (Real.sinh (Real.pi * s.im / 2)),
    norm_nonneg (Complex.cos ((Real.pi : ℂ) * s / 2))]

/-- The cosine factor grows at most like `e ^ (π |t| / 2)`. -/
lemma norm_cos_pi_div_two_le (s : ℂ) :
    ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ Real.exp (Real.pi * |s.im| / 2) := by
  have h := norm_cos_le_exp_abs_im ((Real.pi : ℂ) * s / 2)
  have him : ((Real.pi : ℂ) * s / 2).im = Real.pi * s.im / 2 := by
    simp [Complex.mul_im]
  rw [him] at h
  calc ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ Real.exp |Real.pi * s.im / 2| := h
    _ = Real.exp (Real.pi * |s.im| / 2) := by
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
        norm_num

/-! ## The modulus of `Γ` on the two boundary lines -/

/-- Euler's reflection formula on the critical line: `‖Γ(1/2 + i t)‖ ^ 2 = π / cosh (π t)`. -/
lemma norm_Gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hconj : (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) := by
    simp [Complex.ext_iff]
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 2 + (t : ℂ) * I))
      = (Real.cosh (Real.pi * t) : ℝ) := by
    have h : (Real.pi : ℂ) * (1 / 2 + (t : ℂ) * I)
        = (Real.pi / 2 : ℂ) + ((Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [h, Complex.sin_add_mul_I]
    simp [Complex.sin_pi_div_two, Complex.cos_pi_div_two]
  have key : Complex.Gamma (1 / 2 + (t : ℂ) * I)
      * (starRingEnd ℂ) (Complex.Gamma (1 / 2 + (t : ℂ) * I))
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_conj, hconj, Complex.Gamma_mul_Gamma_one_sub, hsin]
    push_cast
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj] at *
  exact_mod_cast key

/-- On the line `re s = 1/2` the product `Γ(s) cos (π s / 2)` has constant modulus `√(π/2)`; in
particular it is at most `2`. -/
lemma norm_Gamma_mul_cos_half (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * I) * Complex.cos ((Real.pi : ℂ) * (1 / 2 + (t : ℂ) * I) / 2)‖
      ≤ 2 := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hcos := norm_cos_pi_div_two_sq s
  rw [hre, him] at hcos
  have hq : Real.cos (Real.pi * (1 / 2) / 2) ^ 2 = 1 / 2 := by
    have h : Real.pi * (1 / 2) / 2 = Real.pi / 4 := by ring
    rw [h, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hch : Real.cosh (Real.pi * t) = 1 + 2 * Real.sinh (Real.pi * t / 2) ^ 2 := by
    have h := Real.cosh_two_mul (Real.pi * t / 2)
    have h2 : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
    rw [h2] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi * t / 2)]
  have hcos2 : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2 = Real.cosh (Real.pi * t) / 2 := by
    rw [hcos, hq, hch]; ring
  have hG := norm_Gamma_half_add_mul_I_sq t
  rw [← hs] at hG
  have hchpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hsq : ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2 = Real.pi / 2 := by
    rw [norm_mul, mul_pow, hcos2, hG]
    field_simp
  nlinarith [norm_nonneg (Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)),
    Real.pi_le_four]

/-- The combination of `Γ` and `cos` that appears on the boundary line `re s = 3`: the
exponentially large cosine factor cancels the exponential decay of `Γ`. -/
lemma sinh_sq_div_sinh_le {t : ℝ} (ht : t ≠ 0) :
    Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2
      ≤ Real.pi * |t| / 2 := by
  have hsinh_ne : Real.sinh (Real.pi * t) ≠ 0 := by
    simpa [Real.pi_ne_zero] using (Real.sinh_eq_zero (x := Real.pi * t)).not.2
      (by simpa [Real.pi_ne_zero] using ht)
  have hdouble : Real.sinh (Real.pi * t)
      = 2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have hcosh_pos : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  have hkey : Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2
      = Real.pi * t * Real.sinh (Real.pi * t / 2) / (2 * Real.cosh (Real.pi * t / 2)) := by
    rw [hdouble]; field_simp
  rw [hkey, div_le_iff₀ (by positivity)]
  have habs : Real.pi * t * Real.sinh (Real.pi * t / 2)
      = Real.pi * |t| * |Real.sinh (Real.pi * t / 2)| := by
    rcases lt_or_gt_of_ne ht with h | h
    · have h1 : |t| = -t := abs_of_neg h
      have h2 : Real.sinh (Real.pi * t / 2) < 0 := by
        have : Real.pi * t / 2 < 0 := by have := Real.pi_pos; nlinarith
        simpa using Real.sinh_lt_sinh.2 this
      rw [h1, abs_of_neg h2]; ring
    · have h1 : |t| = t := abs_of_pos h
      have h2 : 0 < Real.sinh (Real.pi * t / 2) := by
        have : 0 < Real.pi * t / 2 := by have := Real.pi_pos; positivity
        simpa using Real.sinh_lt_sinh.2 this
      rw [h1, abs_of_pos h2]
  rw [habs]
  have hle : |Real.sinh (Real.pi * t / 2)| ≤ Real.cosh (Real.pi * t / 2) := by
    have := Real.cosh_sq_sub_sinh_sq (Real.pi * t / 2)
    nlinarith [abs_nonneg (Real.sinh (Real.pi * t / 2)), Real.cosh_pos (Real.pi * t / 2),
      sq_abs (Real.sinh (Real.pi * t / 2))]
  have hpi : 0 ≤ Real.pi * |t| := by positivity
  nlinarith

/-- The recurrence `Γ(3 + i t) = (2 + i t)(1 + i t) Γ(1 + i t)`. -/
lemma Gamma_three_add_mul_I (t : ℝ) : Complex.Gamma (3 + (t : ℂ) * I)
    = (2 + (t : ℂ) * I) * (1 + (t : ℂ) * I) * Complex.Gamma (1 + (t : ℂ) * I) := by
  have h1 : Complex.Gamma ((1 + (t : ℂ) * I) + 1)
      = (1 + (t : ℂ) * I) * Complex.Gamma (1 + (t : ℂ) * I) :=
    Complex.Gamma_add_one _ (by simp [Complex.ext_iff])
  have h2 : Complex.Gamma ((2 + (t : ℂ) * I) + 1)
      = (2 + (t : ℂ) * I) * Complex.Gamma (2 + (t : ℂ) * I) :=
    Complex.Gamma_add_one _ (by simp [Complex.ext_iff])
  have e1 : (2 : ℂ) + (t : ℂ) * I = (1 + (t : ℂ) * I) + 1 := by ring
  have e2 : (3 : ℂ) + (t : ℂ) * I = (2 + (t : ℂ) * I) + 1 := by ring
  rw [e2, h2, e1, h1]
  ring

/-- `‖Γ(1 + i t)‖ ^ 2 = π t / sinh (π t)`, Euler's reflection formula on the line `re s = 1`. -/
lemma norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  have h := norm_Gamma_one_sub_mul_I_sq (t := -t) (by simpa using ht)
  have e : (1 : ℂ) - ((-t : ℝ) : ℂ) * I = 1 + (t : ℂ) * I := by push_cast; ring
  rw [e] at h
  rw [h]
  have hneg : Real.pi * -t = -(Real.pi * t) := by ring
  rw [hneg, Real.sinh_neg]
  field_simp

/-- On the line `re s = 3` the product `Γ(s) cos (π s / 2)` is bounded by a polynomial. -/
lemma norm_Gamma_mul_cos_three (t : ℝ) :
    ‖Complex.Gamma (3 + (t : ℂ) * I) * Complex.cos ((Real.pi : ℂ) * (3 + (t : ℂ) * I) / 2)‖
      ≤ 2 * ‖(3 : ℂ) + (t : ℂ) * I + 3‖ ^ 3 := by
  set s : ℂ := 3 + (t : ℂ) * I with hs
  have hre : s.re = 3 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hA : ‖s + 3‖ ^ 2 = 36 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [hs, Complex.normSq_apply]
    ring
  have hApos : 0 ≤ ‖s + 3‖ := norm_nonneg _
  have hcos0 : Real.cos (Real.pi * 3 / 2) = 0 := by
    have h : Real.pi * 3 / 2 = Real.pi + Real.pi / 2 := by ring
    rw [h, Real.cos_add]
    simp
  have hcos := norm_cos_pi_div_two_sq s
  rw [hre, him, hcos0] at hcos
  rcases eq_or_ne t 0 with rfl | ht
  · have hz : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ = 0 := by
      have h0 : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2 = 0 := by simp [hcos]
      simpa using h0
    rw [norm_mul, hz, mul_zero]
    positivity
  · have hGamma : ‖Complex.Gamma s‖ ^ 2
        = ‖(2 : ℂ) + (t : ℂ) * I‖ ^ 2 * ‖(1 : ℂ) + (t : ℂ) * I‖ ^ 2
          * (Real.pi * t / Real.sinh (Real.pi * t)) := by
      rw [hs, Gamma_three_add_mul_I, norm_mul, norm_mul, mul_pow, mul_pow,
        norm_Gamma_one_add_mul_I_sq ht]
    have h2 : ‖(2 : ℂ) + (t : ℂ) * I‖ ^ 2 = 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
    have h1 : ‖(1 : ℂ) + (t : ℂ) * I‖ ^ 2 = 1 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
    have hprod : ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2
        = (4 + t ^ 2) * (1 + t ^ 2)
          * (Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2) := by
      rw [norm_mul, mul_pow, hGamma, hcos, h2, h1]
      ring
    have hbound : ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2
        ≤ (4 + t ^ 2) * (1 + t ^ 2) * (Real.pi * |t| / 2) := by
      rw [hprod]
      have hnn : 0 ≤ (4 + t ^ 2) * (1 + t ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_left (sinh_sq_div_sinh_le ht) hnn
    have hpoly : (4 + t ^ 2) * (1 + t ^ 2) * (Real.pi * |t| / 2) ≤ 4 * (36 + t ^ 2) ^ 3 := by
      have habs : |t| ^ 2 = t ^ 2 := sq_abs t
      have h0 : 0 ≤ |t| := abs_nonneg t
      have h12 : 12 * |t| ≤ 36 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 6)]
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have hpipos : 0 < Real.pi := Real.pi_pos
      have hstep : (4 + t ^ 2) * (1 + t ^ 2) * (Real.pi * |t| / 2)
          ≤ (36 + t ^ 2) * (36 + t ^ 2) * ((36 + t ^ 2) / 6) := by
        have ha : Real.pi * |t| / 2 ≤ (36 + t ^ 2) / 6 := by nlinarith
        have hb : (4 + t ^ 2) * (1 + t ^ 2) ≤ (36 + t ^ 2) * (36 + t ^ 2) := by
          nlinarith [sq_nonneg t]
        have hc : (0 : ℝ) ≤ Real.pi * |t| / 2 := by positivity
        nlinarith [sq_nonneg t]
      nlinarith [sq_nonneg t, sq_nonneg ((36 : ℝ) + t ^ 2)]
    have hcube : (2 * ‖s + 3‖ ^ 3) ^ 2 = 4 * (36 + t ^ 2) ^ 3 := by
      have hsix : ‖s + 3‖ ^ 6 = (‖s + 3‖ ^ 2) ^ 3 := by ring
      calc (2 * ‖s + 3‖ ^ 3) ^ 2 = 4 * ‖s + 3‖ ^ 6 := by ring
        _ = 4 * (‖s + 3‖ ^ 2) ^ 3 := by rw [hsix]
        _ = 4 * (36 + t ^ 2) ^ 3 := by rw [hA]
    have hfinal : ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2
        ≤ (2 * ‖s + 3‖ ^ 3) ^ 2 := by rw [hcube]; linarith
    calc ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖
        = Real.sqrt (‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 * ‖s + 3‖ ^ 3) ^ 2) := Real.sqrt_le_sqrt hfinal
      _ = 2 * ‖s + 3‖ ^ 3 := Real.sqrt_sq (by positivity)

/-! ## The Phragmén–Lindelöf argument -/

/-- The auxiliary function `Γ(s) cos (π s / 2) / (s + 3) ^ 3`, bounded on the two boundary lines
of the strip `1/2 ≤ re s ≤ 3`. -/
def gammaCosAux (s : ℂ) : ℂ :=
  Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) / (s + 3) ^ 3

lemma differentiableAt_gammaCosAux {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gammaCosAux s := by
  have hG : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma _ ?_
    intro m hcon
    rw [hcon] at hs
    simp at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hne : s + 3 ≠ 0 := by
    intro hcon
    have h : (s + 3).re = 0 := by rw [hcon]; simp
    simp at h
    linarith
  have hcos : DifferentiableAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s :=
    (Complex.differentiable_cos.comp
      (by fun_prop : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2))).differentiableAt
  exact (hG.mul hcos).div (((differentiable_id.add_const 3).pow 3).differentiableAt)
    (pow_ne_zero _ hne)

lemma diffContOnCl_gammaCosAux :
    DiffContOnCl ℂ gammaCosAux (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) 3) := by
  constructor
  · intro s hs
    exact (differentiableAt_gammaCosAux (by linarith [hs.1])).differentiableWithinAt
  · intro s hs
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3)] at hs
    exact (differentiableAt_gammaCosAux (by linarith [hs.1])).continuousAt.continuousWithinAt

/-- `Γ ≤ 2` on the interval `[1/2, 3]`. -/
lemma Gamma_le_two_of_mem_Icc_three {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 3) :
    Real.Gamma x ≤ 2 := by
  have hG3 : Real.Gamma 3 = 2 := by
    have h := Real.Gamma_nat_eq_factorial 2
    norm_num at h ⊢
  rcases le_or_gt x 1 with hx | hx
  · exact Gamma_le_two_of_mem_Icc h1 hx
  · rcases le_or_gt x 2 with hx2 | hx2
    · linarith [Gamma_le_one_of_mem_Icc hx.le hx2]
    · have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn (a := x) (b := 3)
        (by simp; linarith) (by simp; norm_num) h2
      linarith [hG3 ▸ hmono]

/-- On the closed strip, `‖gammaCosAux‖` is bounded by a single exponential in `|t|`. -/
lemma norm_gammaCosAux_le {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h1 : s.re ≤ 3) :
    ‖gammaCosAux s‖ ≤ Real.exp (Real.pi * |s.im| / 2) := by
  have hGamma : ‖Complex.Gamma s‖ ≤ 2 :=
    le_trans (norm_Gamma_le_Gamma_re (by linarith)) (Gamma_le_two_of_mem_Icc_three h0 h1)
  have hcos := norm_cos_pi_div_two_le s
  have hden : (3 : ℝ) ≤ ‖s + 3‖ := by
    have h : |(s + 3).re| ≤ ‖s + 3‖ := Complex.abs_re_le_norm (s + 3)
    have hre : (s + 3).re = s.re + 3 := by simp
    rw [hre, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re + 3)] at h
    linarith
  have hpos : (0 : ℝ) < ‖s + 3‖ ^ 3 := by positivity
  have hcube : (27 : ℝ) ≤ ‖s + 3‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hden 3
    norm_num at h
    exact h
  have hnum : ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖
      ≤ 2 * Real.exp (Real.pi * |s.im| / 2) := by
    rw [norm_mul]
    exact mul_le_mul hGamma hcos (norm_nonneg _) (by norm_num)
  have he : 0 < Real.exp (Real.pi * |s.im| / 2) := Real.exp_pos _
  rw [gammaCosAux, norm_div, norm_pow, div_le_iff₀ hpos]
  nlinarith

lemma isBigO_gammaCosAux :
    ∃ c < Real.pi / (3 - 1 / 2), ∃ B : ℝ, gammaCosAux =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) 3)]
        fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  refine ⟨1, by rw [show (3 : ℝ) - 1 / 2 = 5 / 2 by norm_num]; nlinarith [Real.pi_gt_three], 5, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  have hmem : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) 3), z.re ∈ Set.Ioo (1 / 2 : ℝ) 3 := by
    exact Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => hz)
  filter_upwards [hmem] with z hz
  have hb := norm_gammaCosAux_le hz.1.le hz.2.le
  have hkey : Real.pi * |z.im| / 2 ≤ 5 * Real.exp (1 * |z.im|) := by
    have h1 : 1 * |z.im| ≤ Real.exp (1 * |z.im|) := by
      have := Real.add_one_le_exp (1 * |z.im|)
      linarith
    have h2 : (0 : ℝ) < Real.exp (1 * |z.im|) := Real.exp_pos _
    nlinarith [Real.pi_le_four, abs_nonneg z.im]
  have : Real.exp (Real.pi * |z.im| / 2) ≤ Real.exp (5 * Real.exp (1 * |z.im|)) :=
    Real.exp_le_exp.2 hkey
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb.trans this

/-- On the strip the denominator `(s + 3) ^ 3` is at least `27` in modulus. -/
lemma le_norm_add_three_cube {s : ℂ} (h0 : 1 / 2 ≤ s.re) : (27 : ℝ) ≤ ‖s + 3‖ ^ 3 := by
  have hden : (3 : ℝ) ≤ ‖s + 3‖ := by
    have h : |(s + 3).re| ≤ ‖s + 3‖ := Complex.abs_re_le_norm (s + 3)
    have hre : (s + 3).re = s.re + 3 := by simp
    rw [hre, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re + 3)] at h
    linarith
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hden 3
  norm_num at h
  exact h

lemma norm_gammaCosAux_le_two_of_re_half {z : ℂ} (hz : z.re = 1 / 2) :
    ‖gammaCosAux z‖ ≤ 2 := by
  have hz' : z = 1 / 2 + (z.im : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [hz]
    push_cast
    ring
  have hnum := norm_Gamma_mul_cos_half z.im
  rw [← hz'] at hnum
  have hden := le_norm_add_three_cube (s := z) (by rw [hz])
  have hpos : (0 : ℝ) < ‖z + 3‖ ^ 3 := by positivity
  rw [gammaCosAux, norm_div, norm_pow, div_le_iff₀ hpos]
  nlinarith

lemma norm_gammaCosAux_le_two_of_re_three {z : ℂ} (hz : z.re = 3) :
    ‖gammaCosAux z‖ ≤ 2 := by
  have hz' : z = 3 + (z.im : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [hz]
    push_cast
    ring
  have hnum := norm_Gamma_mul_cos_three z.im
  rw [← hz'] at hnum
  have hpos : (0 : ℝ) < ‖z + 3‖ ^ 3 := by
    have := le_norm_add_three_cube (s := z) (by rw [hz]; norm_num)
    linarith
  rw [gammaCosAux, norm_div, norm_pow, div_le_iff₀ hpos]
  linarith

/-- **The product bound in the strip.**  `‖Γ(s) cos (π s / 2)‖ ≤ 2 ‖s + 3‖ ^ 3` for
`1/2 ≤ re s ≤ 3`. -/
theorem norm_Gamma_mul_cos_le_of_mem_strip {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h1 : s.re ≤ 3) :
    ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ 2 * ‖s + 3‖ ^ 3 := by
  have hPL : ‖gammaCosAux s‖ ≤ 2 :=
    PhragmenLindelof.vertical_strip diffContOnCl_gammaCosAux isBigO_gammaCosAux
      (fun z hz => norm_gammaCosAux_le_two_of_re_half hz)
      (fun z hz => norm_gammaCosAux_le_two_of_re_three hz) h0 h1
  have hpos : (0 : ℝ) < ‖s + 3‖ ^ 3 := by
    have := le_norm_add_three_cube h0
    linarith
  rw [gammaCosAux, norm_div, norm_pow, div_le_iff₀ hpos] at hPL
  linarith

/-! ## The decay estimate -/

/-- `sinh u ≥ e ^ u / 4` for `u ≥ 1`. -/
lemma exp_div_four_le_sinh {u : ℝ} (hu : 1 ≤ u) : Real.exp u / 4 ≤ Real.sinh u := by
  rw [Real.sinh_eq]
  have hpos : 0 < Real.exp u := Real.exp_pos u
  have hge : (2 : ℝ) ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  have h1 : Real.exp (-u) ≤ Real.exp u / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  linarith

/-- **Exponential decay of `Γ` on vertical lines**, in the strip `1/2 ≤ re s ≤ 3`. -/
theorem norm_Gamma_le_exp_neg {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h1 : s.re ≤ 3) (ht : 1 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ≤ 8 * ‖s + 3‖ ^ 3 * Real.exp (-(Real.pi * |s.im| / 2)) := by
  have hprod := norm_Gamma_mul_cos_le_of_mem_strip h0 h1
  rw [norm_mul] at hprod
  -- a lower bound for the cosine factor
  have hsinh : Real.exp (Real.pi * |s.im| / 2) / 4 ≤ |Real.sinh (Real.pi * s.im / 2)| := by
    rw [Real.abs_sinh]
    have habs : |Real.pi * s.im / 2| = Real.pi * |s.im| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [habs]
    refine exp_div_four_le_sinh ?_
    nlinarith [Real.pi_gt_three]
  have hcos : Real.exp (Real.pi * |s.im| / 2) / 4
      ≤ ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ :=
    le_trans hsinh (abs_sinh_le_norm_cos s)
  have hexp_pos : (0 : ℝ) < Real.exp (Real.pi * |s.im| / 2) := Real.exp_pos _
  have hGnn : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hkey : ‖Complex.Gamma s‖ * (Real.exp (Real.pi * |s.im| / 2) / 4) ≤ 2 * ‖s + 3‖ ^ 3 :=
    le_trans (mul_le_mul_of_nonneg_left hcos hGnn) hprod
  have hne : Real.exp (-(Real.pi * |s.im| / 2)) = (Real.exp (Real.pi * |s.im| / 2))⁻¹ := by
    rw [Real.exp_neg]
  rw [hne, le_mul_inv_iff₀ hexp_pos]
  nlinarith

/-- **Exponential decay of `Γ` on vertical lines**, in the strip `1/4 ≤ re s ≤ 5`. -/
theorem norm_Gamma_le_exp_decay {s : ℂ} (h0 : 1 / 4 ≤ s.re) (h1 : s.re ≤ 5) (ht : 1 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ≤ 8 * (5 + ‖s‖) ^ 5 * Real.exp (-(Real.pi * |s.im| / 2)) := by
  have hE : 0 < Real.exp (-(Real.pi * |s.im| / 2)) := Real.exp_pos _
  have hsnn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  have hbase : (1 : ℝ) ≤ 5 + ‖s‖ := by linarith
  have hnorm_s : 1 ≤ ‖s‖ := le_trans ht (Complex.abs_im_le_norm s)
  have hs_ne : s ≠ 0 := by
    intro hc
    rw [hc] at hnorm_s
    simp at hnorm_s
    linarith
  -- a convenient monotonicity fact for the powers
  have hpow3 : ∀ z : ℂ, ‖z‖ ≤ 5 + ‖s‖ → ‖z‖ ^ 3 ≤ (5 + ‖s‖) ^ 3 := fun z hz =>
    pow_le_pow_left₀ (norm_nonneg z) hz 3
  have hpow : ∀ z : ℂ, ‖z‖ ≤ 5 + ‖s‖ → ‖z‖ ^ 3 ≤ (5 + ‖s‖) ^ 5 := by
    intro z hz
    calc ‖z‖ ^ 3 ≤ (5 + ‖s‖) ^ 3 := hpow3 z hz
      _ ≤ (5 + ‖s‖) ^ 5 := pow_le_pow_right₀ hbase (by norm_num)
  rcases le_or_gt s.re 3 with h3 | h3
  · rcases le_or_gt (1 / 2 : ℝ) s.re with hhalf | hhalf
    · have h := norm_Gamma_le_exp_neg hhalf h3 ht
      have hb : ‖s + 3‖ ≤ 5 + ‖s‖ := by
        have := norm_add_le s (3 : ℂ)
        have h3' : ‖(3 : ℂ)‖ = 3 := by simp
        rw [h3'] at this
        linarith
      have hcube := hpow (s + 3) hb
      nlinarith
    · -- `1/4 ≤ re s < 1/2` : use `Γ(s) = Γ(s+1)/s`
      have hrec : Complex.Gamma (s + 1) = s * Complex.Gamma s := Complex.Gamma_add_one s hs_ne
      have hre1 : 1 / 2 ≤ (s + 1).re := by simp; linarith
      have hre2 : (s + 1).re ≤ 3 := by simp; linarith
      have him1 : (s + 1).im = s.im := by simp
      have h := norm_Gamma_le_exp_neg hre1 hre2 (by rw [him1]; exact ht)
      rw [him1] at h
      have hb : ‖s + 1 + 3‖ ≤ 5 + ‖s‖ := by
        have hh := norm_add_le s (4 : ℂ)
        have h4 : ‖(4 : ℂ)‖ = 4 := by simp
        rw [h4] at hh
        have he : s + 1 + 3 = s + 4 := by ring
        rw [he]
        linarith
      have hcube := hpow (s + 1 + 3) hb
      have hnormrec : ‖s‖ * ‖Complex.Gamma s‖ = ‖Complex.Gamma (s + 1)‖ := by
        rw [hrec, norm_mul]
      nlinarith [norm_nonneg (Complex.Gamma s)]
  · -- `3 < re s ≤ 5` : use `Γ(s) = (s-1)(s-2)Γ(s-2)`
    have h1ne : s - 1 ≠ 0 := by
      intro hc
      have him : (s - 1).im = 0 := by rw [hc]; simp
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at him
      rw [him] at ht
      simp at ht
      linarith
    have h2ne : s - 2 ≠ 0 := by
      intro hc
      have him : (s - 2).im = 0 := by rw [hc]; simp
      simp only [Complex.sub_im, Complex.im_ofNat, sub_zero] at him
      rw [him] at ht
      simp at ht
      linarith
    have e1 : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
      have := Complex.Gamma_add_one (s - 1) h1ne
      simpa using this
    have e2 : Complex.Gamma (s - 1) = (s - 2) * Complex.Gamma (s - 2) := by
      have := Complex.Gamma_add_one (s - 2) h2ne
      have he : s - 2 + 1 = s - 1 := by ring
      rw [he] at this
      exact this
    have hre1 : 1 / 2 ≤ (s - 2).re := by simp; linarith
    have hre2 : (s - 2).re ≤ 3 := by simp; linarith
    have him2 : (s - 2).im = s.im := by simp
    have h := norm_Gamma_le_exp_neg hre1 hre2 (by rw [him2]; exact ht)
    rw [him2] at h
    have hb : ‖s - 2 + 3‖ ≤ 5 + ‖s‖ := by
      have hh := norm_add_le s (1 : ℂ)
      have h4 : ‖(1 : ℂ)‖ = 1 := by simp
      rw [h4] at hh
      have he : s - 2 + 3 = s + 1 := by ring
      rw [he]
      linarith
    have hcube := hpow3 (s - 2 + 3) hb
    have hn1 : ‖s - 1‖ ≤ 5 + ‖s‖ := by
      have hh := norm_sub_le s (1 : ℂ)
      have h4 : ‖(1 : ℂ)‖ = 1 := by simp
      rw [h4] at hh
      linarith
    have hn2 : ‖s - 2‖ ≤ 5 + ‖s‖ := by
      have hh := norm_sub_le s (2 : ℂ)
      have h4 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h4] at hh
      linarith
    have hGamma : ‖Complex.Gamma s‖ = ‖s - 1‖ * ‖s - 2‖ * ‖Complex.Gamma (s - 2)‖ := by
      rw [e1, e2, norm_mul, norm_mul]
      ring
    have hGnn : 0 ≤ ‖Complex.Gamma (s - 2)‖ := norm_nonneg _
    have hstep : ‖Complex.Gamma s‖
        ≤ (5 + ‖s‖) * (5 + ‖s‖) * (8 * (5 + ‖s‖) ^ 3
          * Real.exp (-(Real.pi * |s.im| / 2))) := by
      rw [hGamma]
      have hA : ‖s - 1‖ * ‖s - 2‖ ≤ (5 + ‖s‖) * (5 + ‖s‖) :=
        mul_le_mul hn1 hn2 (norm_nonneg _) (by linarith)
      have hB : ‖Complex.Gamma (s - 2)‖
          ≤ 8 * (5 + ‖s‖) ^ 3 * Real.exp (-(Real.pi * |s.im| / 2)) := by
        refine le_trans h ?_
        nlinarith [pow_nonneg (norm_nonneg (s - 2 + 3)) 3]
      exact mul_le_mul hA hB hGnn (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    ring

/-- **Exponential decay of `Γ` on vertical lines**, in the strip `1/4 ≤ re s ≤ 5 + n`, for every
`n`.  The right-hand edge of the strip is pushed out by the recurrence `Γ(s) = (s-1)Γ(s-1)`. -/
theorem norm_Gamma_le_exp_decay_of_le (n : ℕ) {s : ℂ} (h0 : 1 / 4 ≤ s.re) (h1 : s.re ≤ 5 + n)
    (ht : 1 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ≤ 8 * (5 + n + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2)) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_exp_decay h0 (by simpa using h1) ht
  | succ n ih =>
    have hE : 0 < Real.exp (-(Real.pi * |s.im| / 2)) := Real.exp_pos _
    have hsnn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbase : (1 : ℝ) ≤ 6 + n + ‖s‖ := by linarith
    rcases le_or_gt s.re (5 + n) with hle | hgt
    · refine le_trans (ih h0 hle ht) ?_
      have hb : (5 + (n : ℝ) + ‖s‖) ^ (5 + n) ≤ (6 + (n : ℝ) + ‖s‖) ^ (5 + (n + 1)) := by
        calc (5 + (n : ℝ) + ‖s‖) ^ (5 + n)
            ≤ (6 + (n : ℝ) + ‖s‖) ^ (5 + n) :=
              pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ (6 + (n : ℝ) + ‖s‖) ^ (5 + (n + 1)) := pow_le_pow_right₀ hbase (by omega)
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      have : (8 : ℝ) * (5 + (n : ℝ) + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2))
          ≤ 8 * (6 + (n : ℝ) + ‖s‖) ^ (5 + (n + 1)) * Real.exp (-(Real.pi * |s.im| / 2)) := by
        have h8 : (0 : ℝ) ≤ 8 := by norm_num
        nlinarith [hE.le]
      calc (8 : ℝ) * (5 + (n : ℝ) + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2))
          ≤ 8 * (6 + (n : ℝ) + ‖s‖) ^ (5 + (n + 1)) * Real.exp (-(Real.pi * |s.im| / 2)) := this
        _ = 8 * (5 + ((n + 1 : ℕ) : ℝ) + ‖s‖) ^ (5 + (n + 1))
              * Real.exp (-(Real.pi * |s.im| / 2)) := by push_cast; ring_nf
    · -- `5 + n < re s ≤ 6 + n` : one step of the recurrence
      have hne : s - 1 ≠ 0 := by
        intro hc
        have him : (s - 1).im = 0 := by rw [hc]; simp
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at him
        rw [him] at ht
        simp at ht
        linarith
      have hrec : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
        have h := Complex.Gamma_add_one (s - 1) hne
        simpa using h
      have hre1 : 1 / 4 ≤ (s - 1).re := by simp; linarith
      have hre2 : (s - 1).re ≤ 5 + n := by
        simp only [Complex.sub_re, Complex.one_re]
        have : s.re ≤ 5 + ((n : ℝ) + 1) := by push_cast at h1; linarith
        linarith
      have him1 : (s - 1).im = s.im := by simp
      have hIH := ih hre1 hre2 (by rw [him1]; exact ht)
      rw [him1] at hIH
      have hn1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
        have h := norm_sub_le s (1 : ℂ)
        simp only [norm_one] at h
        linarith
      have hbound : ‖Complex.Gamma (s - 1)‖
          ≤ 8 * (6 + (n : ℝ) + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2)) := by
        refine le_trans hIH ?_
        have hb : (5 + (n : ℝ) + ‖s - 1‖) ^ (5 + n) ≤ (6 + (n : ℝ) + ‖s‖) ^ (5 + n) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        nlinarith [hE.le]
      have hGnn : 0 ≤ ‖Complex.Gamma (s - 1)‖ := norm_nonneg _
      have hstep : ‖Complex.Gamma s‖
          ≤ (6 + (n : ℝ) + ‖s‖)
            * (8 * (6 + (n : ℝ) + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2))) := by
        rw [hrec, norm_mul]
        exact mul_le_mul (by linarith) hbound hGnn (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      push_cast
      ring

end RiemannHypothesis
