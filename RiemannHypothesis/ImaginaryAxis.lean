/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The square-root bound for `ζ` on the imaginary axis

The board row `M1-GROWTH` asks for the *convexity* bound
`|ζ(σ + i t)| = O(t ^ ((1 - σ) / 2))` inside the critical strip.  On the strip itself only the
trivial exponent `1 - σ` is available here (`RiemannHypothesis.norm_riemannZeta_le_strip`).
This file proves the convexity bound at the left edge `σ = 0`, where it says
`|ζ(i t)| = O(√t log t)`, and it does so *exactly*: the modulus of the functional-equation
factor `χ(s) = 2 (2π)^(-s) Γ(s) cos(π s / 2)` on the line `re s = 1` is computed in closed
form from Euler's reflection formula, no Stirling asymptotics being needed there.

The two closed-form ingredients are

* `norm_Gamma_one_sub_mul_I_sq` : `‖Γ(1 - i t)‖² = π t / sinh(π t)`, from
  `Γ(z) Γ(1 - z) = π / sin (π z)` and `Γ(z + 1) = z Γ(z)`;
* `norm_cos_pi_one_sub_mul_I_div_two` : `‖cos (π (1 - i t) / 2)‖ = |sinh (π t / 2)|`.

Multiplying them, the exponentially large and exponentially small factors cancel and leave the
algebraic factor `√(t tanh(π t / 2) / (2 π))`, which is at most `√(t / (2π))`.  Combined with
the logarithmic bound for `ζ` on the line `re s = 1`
(`RiemannHypothesis.norm_riemannZeta_le_log`, proved in `RiemannHypothesis.EulerMaclaurin`)
this gives the main result.

## Main results

* `norm_riemannZeta_mul_I_le` : `‖ζ(i t)‖ ≤ √(|t| / (2π)) * (6 + log (1 + |t|))` for `|t| ≥ 2`.
* `norm_riemannZeta_isBigO_imaginary_axis` : `‖ζ(i t)‖ = O(√t · log t)` as `t → ∞`, the
  convexity exponent `(1 - σ)/2 = 1/2` at `σ = 0`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-- Euler's reflection formula gives the modulus of `Γ` on the vertical line `re s = 1` in
closed form: `‖Γ(1 - i t)‖² = π t / sinh (π t)`. -/
lemma norm_Gamma_one_sub_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  have hI : ((t : ℂ) * I) ≠ 0 := by simp [Complex.ext_iff, ht]
  have hsinh_ne : Real.sinh (Real.pi * t) ≠ 0 := by
    simpa [Real.pi_ne_zero] using (Real.sinh_eq_zero (x := Real.pi * t)).not.2
      (by simpa [Real.pi_ne_zero] using ht)
  have hs : ((Real.sinh (Real.pi * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsinh_ne
  have hconj : (starRingEnd ℂ) (1 - (t : ℂ) * I) = (t : ℂ) * I + 1 := by
    simp [Complex.ext_iff]
  have h1 : Complex.Gamma ((t : ℂ) * I + 1)
      = ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) := Complex.Gamma_add_one _ hI
  have hsin : Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I))
      = (Real.sinh (Real.pi * t) : ℝ) * I := by
    have h : (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [h, Complex.sin_mul_I]
    norm_cast
  have h2 : Complex.Gamma ((t : ℂ) * I) * Complex.Gamma (1 - (t : ℂ) * I)
      = (Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℝ) * I) := by
    rw [Complex.Gamma_mul_Gamma_one_sub, hsin]
  have key : Complex.Gamma (1 - (t : ℂ) * I)
      * (starRingEnd ℂ) (Complex.Gamma (1 - (t : ℂ) * I))
      = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_conj, hconj, h1]
    calc Complex.Gamma (1 - (t : ℂ) * I) * ((t : ℂ) * I * Complex.Gamma ((t : ℂ) * I))
        = ((t : ℂ) * I) * (Complex.Gamma ((t : ℂ) * I)
            * Complex.Gamma (1 - (t : ℂ) * I)) := by ring
      _ = ((t : ℂ) * I) * ((Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℝ) * I)) := by rw [h2]
      _ = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
            rw [Complex.ofReal_div, Complex.ofReal_mul]
            field_simp
  have hnormSq : ((Complex.normSq (Complex.Gamma (1 - (t : ℂ) * I)) : ℝ) : ℂ)
      = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← Complex.mul_conj]; exact key
  rw [← Complex.normSq_eq_norm_sq]
  exact_mod_cast hnormSq

/-- The cosine factor of the functional equation on the line `re s = 1`:
`‖cos (π (1 - i t) / 2)‖ = |sinh (π t / 2)|`. -/
lemma norm_cos_pi_one_sub_mul_I_div_two (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖ = |Real.sinh (Real.pi * t / 2)| := by
  have h : (Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2
      = (Real.pi : ℂ) / 2 - ((Real.pi * t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.cos_pi_div_two_sub, Complex.sin_mul_I]
  simp only [norm_mul, Complex.norm_I, mul_one]
  rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]

/-- The product of the two closed-form factors is at most `√(π |t| / 2)`: the exponentially
large cosine factor exactly cancels the exponential decay of `Γ`, leaving `√(π t tanh(π t/2)/2)`.
-/
lemma norm_Gamma_mul_cos_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖
      ≤ Real.sqrt (Real.pi * |t| / 2) := by
  have hG := norm_Gamma_one_sub_mul_I_sq ht
  have hC := norm_cos_pi_one_sub_mul_I_div_two t
  have hsinh_ne : Real.sinh (Real.pi * t) ≠ 0 := by
    simpa [Real.pi_ne_zero] using (Real.sinh_eq_zero (x := Real.pi * t)).not.2
      (by simpa [Real.pi_ne_zero] using ht)
  have hdouble : Real.sinh (Real.pi * t)
      = 2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  -- square both sides
  have hnn : 0 ≤ ‖Complex.Gamma (1 - (t : ℂ) * I)‖
      * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖ := by positivity
  have hsq : (‖Complex.Gamma (1 - (t : ℂ) * I)‖
      * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖) ^ 2 ≤ Real.pi * |t| / 2 := by
    rw [mul_pow, hG, hC, sq_abs]
    have hcosh_pos : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
    have hkey : Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2
        = Real.pi * t * Real.sinh (Real.pi * t / 2) / (2 * Real.cosh (Real.pi * t / 2)) := by
      rw [hdouble]
      field_simp
    rw [hkey]
    rw [div_le_iff₀ (by positivity)]
    have habs : Real.pi * t * Real.sinh (Real.pi * t / 2)
        = Real.pi * |t| * |Real.sinh (Real.pi * t / 2)| := by
      rcases lt_or_gt_of_ne ht with h | h
      · have h1 : |t| = -t := abs_of_neg h
        have h2 : Real.sinh (Real.pi * t / 2) < 0 := by
          have : Real.pi * t / 2 < 0 := by
            have := Real.pi_pos; nlinarith
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
  calc ‖Complex.Gamma (1 - (t : ℂ) * I)‖
        * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖
      = Real.sqrt ((‖Complex.Gamma (1 - (t : ℂ) * I)‖
          * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖) ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt (Real.pi * |t| / 2) := Real.sqrt_le_sqrt hsq

/-- **The square-root bound for `ζ` on the imaginary axis.**  For `|t| ≥ 2`,
`‖ζ(i t)‖ ≤ √(|t| / (2π)) · (6 + log (1 + |t|))`.

This is the convexity bound `|ζ(σ + i t)| = O(t^((1-σ)/2))` at `σ = 0`, with the logarithmic
factor coming from the bound for `ζ` on the line `re s = 1`. -/
theorem norm_riemannZeta_mul_I_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖riemannZeta ((t : ℂ) * I)‖
      ≤ Real.sqrt (|t| / (2 * Real.pi)) * (6 + Real.log (1 + |t|)) := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; linarith
  set s : ℂ := 1 - (t : ℂ) * I with hs
  have hsim : s.im = -t := by simp [hs]
  have hsre : s.re = 1 := by simp [hs]
  have hne : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hcon
    have : s.im = 0 := by rw [hcon]; simp
    rw [hsim] at this
    exact ht0 (by linarith)
  have hne1 : s ≠ 1 := by
    intro hcon
    have : s.im = 0 := by rw [hcon]; simp
    rw [hsim] at this
    exact ht0 (by linarith)
  have hFE := riemannZeta_one_sub hne hne1
  have h1s : (1 : ℂ) - s = (t : ℂ) * I := by rw [hs]; ring
  rw [h1s] at hFE
  rw [hFE]
  -- take norms
  have hbase : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-(1 : ℝ)) := by
    have h : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp [hsre]
  have hzeta : ‖riemannZeta s‖ ≤ 6 + Real.log (1 + |t|) := by
    have := norm_riemannZeta_le_log (s := s) (by rw [hsre]) (by rw [hsre]; norm_num)
      (by rw [hsim, abs_neg]; exact ht)
    rwa [hsim, abs_neg] at this
  have hGC := norm_Gamma_mul_cos_le ht0
  have hnorm : ‖2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s
      * Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s‖
      = 2 * ((2 * Real.pi) ^ (-(1 : ℝ)))
        * (‖Complex.Gamma s‖ * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) * ‖riemannZeta s‖ := by
    simp only [norm_mul, hbase, Complex.norm_ofNat]
    ring
  rw [hnorm]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrpow : (2 * Real.pi) ^ (-(1 : ℝ)) = 1 / (2 * Real.pi) := by
    rw [Real.rpow_neg_one]
    exact one_div _ |>.symm
  rw [hrpow]
  have hzn : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hstep : 2 * (1 / (2 * Real.pi))
      * (‖Complex.Gamma s‖ * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) * ‖riemannZeta s‖
      ≤ 2 * (1 / (2 * Real.pi)) * Real.sqrt (Real.pi * |t| / 2) * (6 + Real.log (1 + |t|)) := by
    have h6 : (0 : ℝ) ≤ 6 + Real.log (1 + |t|) := by
      have : (0 : ℝ) ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    have hc : 0 ≤ 2 * (1 / (2 * Real.pi)) := by positivity
    calc 2 * (1 / (2 * Real.pi))
          * (‖Complex.Gamma s‖ * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) * ‖riemannZeta s‖
        ≤ 2 * (1 / (2 * Real.pi)) * Real.sqrt (Real.pi * |t| / 2) * ‖riemannZeta s‖ := by
          have := mul_le_mul_of_nonneg_left hGC hc
          exact mul_le_mul_of_nonneg_right this hzn
      _ ≤ 2 * (1 / (2 * Real.pi)) * Real.sqrt (Real.pi * |t| / 2)
            * (6 + Real.log (1 + |t|)) := by
          have hpos : 0 ≤ 2 * (1 / (2 * Real.pi)) * Real.sqrt (Real.pi * |t| / 2) := by positivity
          exact mul_le_mul_of_nonneg_left hzeta hpos
  refine hstep.trans_eq ?_
  have hsqrt : 2 * (1 / (2 * Real.pi)) * Real.sqrt (Real.pi * |t| / 2)
      = Real.sqrt (|t| / (2 * Real.pi)) := by
    rw [show (2 : ℝ) * (1 / (2 * Real.pi)) = Real.sqrt ((1 / Real.pi) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]; field_simp]
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [hsqrt]

/-- The convexity exponent at the left edge of the critical strip: on the imaginary axis
`‖ζ(i t)‖ = O(√t log t)` as `t → ∞`. -/
theorem norm_riemannZeta_isBigO_imaginary_axis :
    (fun t : ℝ => ‖riemannZeta ((t : ℂ) * I)‖)
      =O[atTop] fun t : ℝ => Real.sqrt t * Real.log t := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6 + 6, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 6), eventually_ge_atTop (2 : ℝ)] with t hexp ht2
  have habs : |t| = t := abs_of_pos (by linarith [Real.exp_pos (6 : ℝ)])
  have h := norm_riemannZeta_mul_I_le (t := t) (by rw [habs]; exact ht2)
  rw [habs] at h
  have hlog6 : (6 : ℝ) ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 6) hexp
    rwa [Real.log_exp] at this
  have hlogt : Real.log (1 + t) ≤ 2 * Real.log t := by
    have h1 : (1 : ℝ) + t ≤ t ^ 2 := by nlinarith
    have := Real.log_le_log (by linarith) h1
    rwa [Real.log_pow] at this
  have hsqrt_le : Real.sqrt (t / (2 * Real.pi)) ≤ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, (by linarith : (0 : ℝ) < t)]
  have hlogpos : 0 < Real.log t := by linarith
  have hstep : Real.sqrt (t / (2 * Real.pi)) * (6 + Real.log (1 + t))
      ≤ Real.sqrt t * ((6 + 6) * Real.log t) := by
    have h1 : (6 : ℝ) + Real.log (1 + t) ≤ (6 + 6) * Real.log t := by linarith
    have h2 : 0 ≤ 6 + Real.log (1 + t) := by
      have : (0:ℝ) ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
      linarith
    calc Real.sqrt (t / (2 * Real.pi)) * (6 + Real.log (1 + t))
        ≤ Real.sqrt t * (6 + Real.log (1 + t)) := by
          exact mul_le_mul_of_nonneg_right hsqrt_le h2
      _ ≤ Real.sqrt t * ((6 + 6) * Real.log t) := by
          exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg t)
  have hfin : ‖riemannZeta ((t : ℂ) * I)‖ ≤ (6 + 6) * (Real.sqrt t * Real.log t) := by
    calc ‖riemannZeta ((t : ℂ) * I)‖ ≤ Real.sqrt (t / (2 * Real.pi)) * (6 + Real.log (1 + t)) := h
      _ ≤ Real.sqrt t * ((6 + 6) * Real.log t) := hstep
      _ = (6 + 6) * (Real.sqrt t * Real.log t) := by ring
  calc ‖‖riemannZeta ((t : ℂ) * I)‖‖ = ‖riemannZeta ((t : ℂ) * I)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ (6 + 6) * (Real.sqrt t * Real.log t) := hfin
    _ ≤ (6 + 6) * ‖Real.sqrt t * Real.log t‖ := by
        gcongr
        exact le_abs_self _

end RiemannHypothesis
