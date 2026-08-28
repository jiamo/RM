/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Growth
import RiemannHypothesis.EulerMaclaurin

/-!
# A quantitative lower bound for `ζ` to the right of the line `re s = 1`

Mathlib's `riemannZeta_ne_zero_of_one_le_re` says that `ζ` has no zero with `re s ≥ 1`, but
it is a qualitative statement.  The classical de la Vallée Poussin zero-free region needs a
*quantitative* version: a lower bound for `|ζ(1 + x + iy)|` that degenerates only
polynomially as `x → 0⁺`.  This file proves such a bound by combining the two ingredients
that the repository already has:

* the Mertens `3-4-1` inequality `|ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1`
  (`RiemannHypothesis.norm_riemannZeta_product_ge_one`);
* the upper bounds `|ζ(σ)| ≤ 1 + 1/(σ-1)` (`norm_riemannZeta_le_of_one_lt_re`) and
  `|ζ(σ+iu)| ≤ 6 + log(1+|u|)` for `1 ≤ σ ≤ 2`, `|u| ≥ 2`
  (`RiemannHypothesis.norm_riemannZeta_le_log`).

## Main result

* `norm_riemannZeta_pow_four_ge` : for `0 < x ≤ 1` and `1 ≤ |y|`,
  `x³ / (8 (6 + log(1 + 2|y|))) ≤ ‖ζ(1 + x + iy)‖⁴`.

## What is *not* proved here

This is the bound *to the right of* the line `re s = 1`.  Turning it into the zero-free
region `ζ(s) ≠ 0` for `re s > 1 - c / log |im s|` needs one further classical ingredient
that is not in this repository: an upper bound for `|ζ'|` (equivalently, a Borel–Carathéodory
or Landau estimate for `ζ'/ζ`) allowing `|ζ(σ+iy)|` to be compared with `|ζ(β+iy)| = 0` at a
hypothetical zero `β + iy` slightly to the left of the line.  The task board records that
gap on the row `M1-ZERO-FREE-REGION`.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- **A quantitative lower bound for `ζ` to the right of the line `re s = 1`.**
For `0 < x ≤ 1` and `1 ≤ |y|`,
`x³ / (8 (6 + log(1 + 2|y|))) ≤ ‖ζ(1 + x + i y)‖⁴`.

In particular `ζ(1 + x + iy)` is nonzero, with a lower bound that decays only like `x^(3/4)`
as `x → 0⁺` — the shape needed by the classical zero-free-region argument. -/
theorem norm_riemannZeta_pow_four_ge {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    x ^ 3 / (8 * (6 + Real.log (1 + 2 * |y|))) ≤ ‖riemannZeta (1 + x + I * y)‖ ^ 4 := by
  set L : ℝ := 6 + Real.log (1 + 2 * |y|) with hL
  have hlognn : 0 ≤ Real.log (1 + 2 * |y|) :=
    Real.log_nonneg (by linarith [abs_nonneg y])
  have hLpos : 0 < L := by rw [hL]; linarith
  -- the three factors
  set A : ℝ := ‖riemannZeta (1 + x)‖ with hA
  set B : ℝ := ‖riemannZeta (1 + x + I * y)‖ with hB
  set C : ℝ := ‖riemannZeta (1 + x + 2 * I * y)‖ with hC
  have hAnn : 0 ≤ A := norm_nonneg _
  have hBnn : 0 ≤ B := norm_nonneg _
  have hCnn : 0 ≤ C := norm_nonneg _
  -- the Mertens 3-4-1 inequality
  have h341 : 1 ≤ A ^ 3 * B ^ 4 * C := by
    have h := norm_riemannZeta_product_ge_one hx0 y
    rw [hA, hB, hC]
    simpa [norm_mul, norm_pow] using h
  -- the upper bound for the first factor
  have hAle : A ≤ 2 / x := by
    have hre : ((1 : ℂ) + x).re = 1 + x := by simp
    have h := norm_riemannZeta_le_of_one_lt_re (s := (1 : ℂ) + x) (by rw [hre]; linarith)
    rw [hre] at h
    have hx' : (1 : ℝ) + x - 1 = x := by ring
    rw [hx'] at h
    calc A ≤ 1 + 1 / x := h
      _ ≤ 2 / x := by
          have hdiff : 2 / x - (1 + 1 / x) = (1 - x) / x := by field_simp; ring
          have hnn : 0 ≤ (1 - x) / x := div_nonneg (by linarith) hx0.le
          linarith
  -- the upper bound for the third factor
  have hCle : C ≤ L := by
    have hre : ((1 : ℂ) + x + 2 * I * y).re = 1 + x := by simp
    have him : ((1 : ℂ) + x + 2 * I * y).im = 2 * y := by simp
    have habs : |2 * y| = 2 * |y| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := norm_riemannZeta_le_log (s := (1 : ℂ) + x + 2 * I * y)
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him, habs]; linarith)
    rw [him, habs] at h
    exact h
  -- combine
  have hApos : 0 < 2 / x := by positivity
  have hstep : 1 ≤ (2 / x) ^ 3 * B ^ 4 * L := by
    refine h341.trans ?_
    have h1 : A ^ 3 ≤ (2 / x) ^ 3 := pow_le_pow_left₀ hAnn hAle 3
    have hB4 : 0 ≤ B ^ 4 := by positivity
    calc A ^ 3 * B ^ 4 * C ≤ (2 / x) ^ 3 * B ^ 4 * C := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hB4) hCnn
      _ ≤ (2 / x) ^ 3 * B ^ 4 * L := by
          exact mul_le_mul_of_nonneg_left hCle (by positivity)
  have hcube : (2 / x) ^ 3 = 8 / x ^ 3 := by
    rw [div_pow]
    norm_num
  rw [hcube] at hstep
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hx3] at hstep
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * L)]
  have hring : (8 : ℝ) * B ^ 4 * L = B ^ 4 * (8 * L) := by ring
  linarith

/-- The quantitative bound in particular re-proves, with an explicit rate, that `ζ` has no
zero strictly to the right of the line `re s = 1`. -/
theorem riemannZeta_ne_zero_of_one_lt_re_of_one_le_abs_im {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : 1 ≤ |y|) : riemannZeta (1 + x + I * y) ≠ 0 := by
  intro hzero
  have h := norm_riemannZeta_pow_four_ge hx0 hx1 hy
  rw [hzero] at h
  simp only [norm_zero] at h
  have hlognn : 0 ≤ Real.log (1 + 2 * |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hpos : 0 < x ^ 3 / (8 * (6 + Real.log (1 + 2 * |y|))) := by positivity
  norm_num at h
  linarith

end RiemannHypothesis

end
