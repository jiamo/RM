/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib

/-!
# The factor `χ` of the functional equation

The functional equation of `ζ` is usually written in the asymmetric form

`ζ(s) = χ(s) ζ(1 - s)`,  `χ(s) = 2 (2π)^(s-1) Γ(1 - s) sin (π s / 2)`,

and it is in this shape that it enters the *approximate functional equation*, where the
second sum is multiplied by `χ(s)`.  Mathlib has the functional equation in the form
`riemannZeta_one_sub`, from which the identity above is a rearrangement, but it has no name
for `χ` and none of the facts about `χ` that the approximate functional equation needs.

This file supplies them.

## Main results

* `zetaChi` — the factor `χ(s) = 2 (2π)^(s-1) Γ(1-s) sin (π s / 2)`.
* `riemannZeta_eq_zetaChi_mul` — `ζ(s) = χ(s) ζ(1-s)` for `s ≠ 0` and `s ∉ {1, 2, 3, …}`.
* `zetaChi_conj` — `χ(conj s) = conj (χ(s))` (Schwarz reflection, proved directly).
* `zetaChi_mul_zetaChi_one_sub` — `χ(s) χ(1-s) = 1` for `s ∉ ℤ`.
* `norm_zetaChi_criticalLine` — **`‖χ(1/2 + i t)‖ = 1`**: on the critical line the factor of the
  functional equation is a pure phase.  This is what makes the two sums of the approximate
  functional equation on the critical line conjugate to each other, and is the reason the
  Hardy `Z`-function is real.

Nothing here is an approximation: every statement is an exact identity about `χ`.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- The factor of the functional equation in its asymmetric form:
`χ(s) = 2 (2π)^(s-1) Γ(1-s) sin (π s / 2)`, so that `ζ(s) = χ(s) ζ(1-s)`. -/
def zetaChi (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) * Complex.sin ((Real.pi : ℂ) * s / 2)

lemma two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp [Real.pi_ne_zero]

/-- **The functional equation in asymmetric form**: `ζ(s) = χ(s) ζ(1-s)`. -/
theorem riemannZeta_eq_zetaChi_mul {s : ℂ} (hs0 : s ≠ 0) (hs : ∀ n : ℕ, s ≠ 1 + n) :
    riemannZeta s = zetaChi s * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n hn
    exact hs n (by linear_combination -hn)
  have h2 : (1 - s) ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have h := riemannZeta_one_sub h1 h2
  rw [show (1 : ℂ) - (1 - s) = s by ring] at h
  rw [h, zetaChi]
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = Complex.sin ((Real.pi : ℂ) * s / 2) := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
      Complex.cos_pi_div_two_sub]
  rw [hcos]
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) = (2 * (Real.pi : ℂ)) ^ (s - 1) := by
    congr 1
    ring
  rw [hpow]

/-- `χ` commutes with complex conjugation. -/
theorem zetaChi_conj (s : ℂ) : zetaChi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (zetaChi s) := by
  have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    have h : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have hpow : (2 * (Real.pi : ℂ)) ^ ((starRingEnd ℂ) s - 1)
      = (starRingEnd ℂ) ((2 * (Real.pi : ℂ)) ^ (s - 1)) := by
    have hconj : (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (s - 1) := by
      simp [map_sub]
    rw [hconj, Complex.cpow_conj _ _ harg]
    congr 2
    simp [Complex.ext_iff]
  rw [zetaChi, zetaChi, hpow]
  have hgamma : Complex.Gamma (1 - (starRingEnd ℂ) s)
      = (starRingEnd ℂ) (Complex.Gamma (1 - s)) := by
    rw [show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) by simp [map_sub], Gamma_conj]
  have htwo : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl
  have hsin : Complex.sin ((Real.pi : ℂ) * (starRingEnd ℂ) s / 2)
      = (starRingEnd ℂ) (Complex.sin ((Real.pi : ℂ) * s / 2)) := by
    rw [show (Real.pi : ℂ) * (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) ((Real.pi : ℂ) * s / 2) by
      rw [map_div₀, map_mul, Complex.conj_ofReal, htwo]]
    exact Complex.sin_conj _
  rw [hgamma, hsin, map_mul, map_mul, map_mul, htwo]

/-- `χ(s) χ(1-s) = 1`: the functional equation is an involution. -/
theorem zetaChi_mul_zetaChi_one_sub {s : ℂ} (hs : Complex.sin ((Real.pi : ℂ) * s) ≠ 0) :
    zetaChi s * zetaChi (1 - s) = 1 := by
  have hgamma : Complex.Gamma (1 - s) * Complex.Gamma s
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s) := by
    have h := Complex.Gamma_mul_Gamma_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring] at h
    rw [h, show (Real.pi : ℂ) * (1 - s) = (Real.pi : ℂ) - (Real.pi : ℂ) * s by ring,
      Complex.sin_pi_sub]
  have hpow : (2 * (Real.pi : ℂ)) ^ (s - 1) * (2 * (Real.pi : ℂ)) ^ ((1 - s) - 1)
      = (2 * (Real.pi : ℂ))⁻¹ := by
    rw [← Complex.cpow_add _ _ two_pi_ne_zero, show s - 1 + ((1 - s) - 1) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
  have hsinsin : Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.sin ((Real.pi : ℂ) * (1 - s) / 2)
      = Complex.sin ((Real.pi : ℂ) * s) / 2 := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
      Complex.sin_pi_div_two_sub]
    have := Complex.sin_two_mul ((Real.pi : ℂ) * s / 2)
    rw [show 2 * ((Real.pi : ℂ) * s / 2) = (Real.pi : ℂ) * s by ring] at this
    rw [this]
    ring
  have hs1 : (1 : ℂ) - (1 - s) = s := by ring
  rw [zetaChi, zetaChi, hs1]
  calc 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s)
        * Complex.sin ((Real.pi : ℂ) * s / 2) *
      (2 * (2 * (Real.pi : ℂ)) ^ ((1 - s) - 1) * Complex.Gamma s *
        Complex.sin ((Real.pi : ℂ) * (1 - s) / 2))
      = 4 * ((2 * (Real.pi : ℂ)) ^ (s - 1) * (2 * (Real.pi : ℂ)) ^ ((1 - s) - 1)) *
          (Complex.Gamma (1 - s) * Complex.Gamma s) *
          (Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.sin ((Real.pi : ℂ) * (1 - s) / 2)) := by
        ring
    _ = 4 * (2 * (Real.pi : ℂ))⁻¹ * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
          (Complex.sin ((Real.pi : ℂ) * s) / 2) := by rw [hpow, hgamma, hsinsin]
    _ = 1 := by
        field_simp
        ring

/-- The sine factor is nonzero off the real integers; in particular on the critical line. -/
lemma sin_pi_mul_ne_zero_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hzero
  have hre := congrArg Complex.re hn
  rw [Complex.re_ofReal_mul, hs] at hre
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hn2 : (2 * n : ℤ) = 1 := by
    have h2 : (2 : ℝ) * n = 1 := by
      have hpi := Real.pi_pos
      field_simp at hre
      nlinarith [hre]
    exact_mod_cast h2
  omega

/-- **On the critical line `χ` is a pure phase**: `‖χ(1/2 + i t)‖ = 1`. -/
theorem norm_zetaChi_criticalLine (t : ℝ) : ‖zetaChi (1 / 2 + (t : ℂ) * I)‖ = 1 := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    simp [hs, Complex.ext_iff]
    norm_num
  have hmul : zetaChi s * (starRingEnd ℂ) (zetaChi s) = 1 := by
    rw [← zetaChi_conj, hconj]
    exact zetaChi_mul_zetaChi_one_sub (sin_pi_mul_ne_zero_of_re_eq_half hre)
  have h := Complex.mul_conj (zetaChi s)
  rw [hmul] at h
  have : ‖zetaChi s‖ ^ 2 = 1 := by
    have h' : ((‖zetaChi s‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h.symm
    exact_mod_cast h'
  nlinarith [norm_nonneg (zetaChi s), this]

end RiemannHypothesis
