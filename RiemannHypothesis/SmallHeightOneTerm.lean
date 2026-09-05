/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SmallHeight
import RiemannHypothesis.Symmetry

/-!
# The Riemann hypothesis up to height `8`

`RiemannHypothesis.SmallHeight` verifies the Riemann hypothesis up to height `7/2` from the
second-order Euler–Maclaurin representation of `ζ` with **no** explicit Dirichlet term.  This
file adds the first explicit term (`N = 1`):

`ζ(s) = 1 + 2^(1-s)/(s-1) + 2^(-s)/2 + s 2^(-s-1)/12 + R₁(s)`,
`‖R₁(s)‖ ≤ 29 ‖s‖ ‖s+1‖ ‖s+2‖ / 38400`  (for `σ ≥ 1/2`)

(`riemannZeta_eq_main_one`, `norm_tsum_bernTerm_shift_le_half`; the constant is `1/192` from
`norm_bernTerm_le_sharp` times the tail `∑' n, (n+2)^(-p) ≤ 29/200`, valid for `p ≥ 7/2`, i.e.
in the right half `σ ≥ 1/2` of the strip).  Now the main term is the constant `1`, so a zero of
`ζ` forces

`1 ≤ 2^(-σ) ‖2/(s-1) + 1/2 + s/24‖ + 29 ‖s‖ ‖s+1‖ ‖s+2‖/38400`,

the three correction terms having been grouped — they partially cancel, and the grouping is
what makes the criterion strong.  Because `2^(-σ) ≤ 2^(-1/2) ≤ 71/100` in the right half
`σ ≥ 1/2` of the strip, because the grouped factor has real part at most `13/24` in absolute
value and controlled imaginary part, and because `‖s‖ ≤ |t| + 3/20`, `‖s+1‖ ≤ |t| + 3/5`,
`‖s+2‖ ≤ |t| + 4/3` for `|t| ≥ 17/5`, this is contradicted throughout `17/5 ≤ |t| ≤ 7`
(`riemannZeta_ne_zero_of_abs_im_mid`).  The functional equation moves a zero with `σ < 1/2` to
its mirror image `1 - s` (`riemannZeta_one_sub_eq_zero_of_mem_strip`, from
`RiemannHypothesis.Symmetry`), so the restriction
`σ ≥ 1/2` is harmless, and below `|t| = 17/5` the criterion of `SmallHeight` applies.  Hence

* `riemannZeta_ne_zero_of_abs_im_le_seven` : `ζ` has no zero in the strip with `|im s| ≤ 7`;
* `verifiedUpToHeight_seven` : `VerifiedUpToHeight 7`;
* `verifiedUpToHeight_of_le_seven` : hence `VerifiedUpToHeight H` for every `H ≤ 7`.

The first zero of `ζ` sits at `t ≈ 14.13`, so — as with `SmallHeight` — this is far below the
numerical verifications in the literature; the point is that it is unconditional and
machine-checked, with no floating-point input.
-/

noncomputable section

open Complex MeasureTheory

namespace RiemannHypothesis

/-- A telescoping bound for the partial sums of `∑ 1/(n+1)³`, sharper than
`sum_range_natAddOne_cube_inv_le` from the third term on. -/
theorem sum_range_natAddOne_cube_inv_le_sharp {M : ℕ} (hM : 3 ≤ M) :
    ∑ n ∈ Finset.range M, (1 : ℝ) / ((n : ℝ) + 1) ^ 3
      ≤ 65 / 54 - 1 / (2 * (M : ℝ) * ((M : ℝ) + 1)) := by
  refine Nat.le_induction ?_ ?_ M hM
  · norm_num [Finset.sum_range_succ]
  · intro M hM ih
    have hM0 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    rw [Finset.sum_range_succ]
    have hstep : (1 : ℝ) / ((M : ℝ) + 1) ^ 3 ≤ 1 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have harith : 65 / 54 - 1 / (2 * (M : ℝ) * ((M : ℝ) + 1))
          + 1 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2))
        = 65 / 54 - 1 / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 1 + 1)) := by
      have h1 : (M : ℝ) ≠ 0 := by linarith
      have h2 : (M : ℝ) + 1 ≠ 0 := by linarith
      have h3 : (M : ℝ) + 2 ≠ 0 := by linarith
      field_simp
      ring
    push_cast
    linarith

/-- `∑' n, (n+2)^(-p) ≤ 11/54` for `p ≥ 3` (the true value at `p = 3` is `ζ(3) - 1 = 0.2020…`). -/
theorem tsum_natAddTwo_rpow_neg_le {p : ℝ} (hp : 3 ≤ p) :
    ∑' n : ℕ, ((n : ℝ) + 2) ^ (-p) ≤ 11 / 54 := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  have hterm : ∀ n ∈ Finset.range M, ((n : ℝ) + 2) ^ (-p) ≤ (1 : ℝ) / ((n : ℝ) + 2) ^ 3 := by
    intro n _
    have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h := Real.rpow_le_rpow_of_exponent_le hx (show -p ≤ (-3 : ℝ) by linarith)
    have hcast : ((n : ℝ) + 2) ^ (-3 : ℝ) = 1 / ((n : ℝ) + 2) ^ 3 := by
      rw [show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
      simp
    rwa [hcast] at h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hshift : ∑ n ∈ Finset.range M, (1 : ℝ) / ((n : ℝ) + 2) ^ 3
      = (∑ n ∈ Finset.range (M + 1), (1 : ℝ) / ((n : ℝ) + 1) ^ 3) - 1 := by
    rw [Finset.sum_range_succ' (fun n => (1 : ℝ) / ((n : ℝ) + 1) ^ 3) M]
    push_cast
    ring_nf
  rw [hshift]
  rcases le_or_gt 2 M with hM | hM
  · have hsum := sum_range_natAddOne_cube_inv_le_sharp (M := M + 1) (by omega)
    have hpos : 0 < 1 / (2 * ((M : ℝ) + 1) * (((M : ℝ) + 1) + 1)) := by positivity
    push_cast at hsum
    linarith
  · interval_cases M <;> norm_num [Finset.sum_range_succ]

/-- The tail of the second-order Euler–Maclaurin expansion, at `N = 1`. -/
theorem norm_tsum_bernTerm_shift_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' n : ℕ, bernTerm (n + 1) s‖ ≤ 11 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 10368 := by
  have hp : (1 : ℝ) < 3 + s.re := by linarith
  have hsum_rpow : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-(3 + s.re))) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 + s.re))) 1).2
      (summable_natAddOne_rpow_neg hp)
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  have hbound : ∀ n : ℕ, ‖bernTerm (n + 1) s‖ ≤
      1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re)) := by
    intro n
    have h := norm_bernTerm_le_sharp (n + 1) hs0 hs1
    have hc : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rwa [hc] at h
  have hsum_maj : Summable
      (fun n : ℕ => 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re))) :=
    hsum_rpow.mul_left _
  have hsum_norm : Summable (fun n : ℕ => ‖bernTerm (n + 1) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum_maj
  have htail : ∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 + s.re)) ≤ 11 / 54 :=
    tsum_natAddTwo_rpow_neg_le (by linarith)
  calc ‖∑' n : ℕ, bernTerm (n + 1) s‖ ≤ ∑' n : ℕ, ‖bernTerm (n + 1) s‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re)) :=
        hsum_norm.tsum_le_tsum hbound hsum_maj
    _ = 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 + s.re)) :=
        hsum_rpow.tsum_mul_left _
    _ ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (11 / 54) := by
        have hpos : (0 : ℝ) ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by positivity
        exact mul_le_mul_of_nonneg_left htail hpos
    _ = 11 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 10368 := by ring

/-- The elementary bound `2^(-σ) ≤ 71/100` for `σ ≥ 1/2`. -/
theorem rpow_two_neg_le {x : ℝ} (h : 1 / 2 ≤ x) : (2:ℝ) ^ (-x) ≤ 71 / 100 := by
  have h1 : (2:ℝ) ^ (-x) ≤ (2:ℝ) ^ (-(1/2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2:ℝ) ^ (-(1/2) : ℝ) ≤ 71/100 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith

/-- Sharpened tail sum: for `p ≥ 7/2`, `∑' n, (n+2)^(-p) ≤ 29/200`.  This is the previous
bound `11/54` for the exponent `3` multiplied by the extra factor `2^(-1/2) ≤ 71/100` coming
from the half unit of decay available in the right half `σ ≥ 1/2` of the critical strip. -/
theorem tsum_natAddTwo_rpow_neg_le_half {p : ℝ} (hp : 7 / 2 ≤ p) :
    ∑' n : ℕ, ((n : ℝ) + 2) ^ (-p) ≤ 29 / 200 := by
  have hsum : ∀ q : ℝ, 1 < q → Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-q)) := by
    intro q hq
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-q)) 1).2
      (summable_natAddOne_rpow_neg hq)
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  have hsumL : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-p)) := hsum p (by linarith)
  have hsum3 : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-(3 : ℝ))) := hsum 3 (by norm_num)
  have hbound : ∀ n : ℕ, ((n : ℝ) + 2) ^ (-p) ≤ 71 / 100 * ((n : ℝ) + 2) ^ (-(3 : ℝ)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have h1 : ((n : ℝ) + 2) ^ (-p) ≤ ((n : ℝ) + 2) ^ (-(7 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : ((n : ℝ) + 2) ^ (-(7 / 2) : ℝ)
        = ((n : ℝ) + 2) ^ (-(3 : ℝ)) * ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have h3 : ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
    have h4 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 71 / 100 := rpow_two_neg_le (le_refl _)
    have h5 : (0 : ℝ) < ((n : ℝ) + 2) ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    calc ((n : ℝ) + 2) ^ (-p) ≤ ((n : ℝ) + 2) ^ (-(7 / 2) : ℝ) := h1
      _ = ((n : ℝ) + 2) ^ (-(3 : ℝ)) * ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) := h2
      _ ≤ ((n : ℝ) + 2) ^ (-(3 : ℝ)) * (71 / 100) := by nlinarith
      _ = 71 / 100 * ((n : ℝ) + 2) ^ (-(3 : ℝ)) := by ring
  calc ∑' n : ℕ, ((n : ℝ) + 2) ^ (-p)
      ≤ ∑' n : ℕ, 71 / 100 * ((n : ℝ) + 2) ^ (-(3 : ℝ)) :=
        hsumL.tsum_le_tsum hbound (hsum3.mul_left _)
    _ = 71 / 100 * ∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 : ℝ)) := hsum3.tsum_mul_left _
    _ ≤ 71 / 100 * (11 / 54) := by
        have := tsum_natAddTwo_rpow_neg_le (p := 3) (le_refl _)
        linarith
    _ ≤ 29 / 200 := by norm_num

/-- The tail of the second-order Euler–Maclaurin expansion at `N = 1`, sharpened by using the
half unit of decay available in the right half `σ ≥ 1/2` of the strip. -/
theorem norm_tsum_bernTerm_shift_le_half {s : ℂ} (hs0 : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖∑' n : ℕ, bernTerm (n + 1) s‖ ≤ 29 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 38400 := by
  have hspos : 0 < s.re := by linarith
  have hp : (1 : ℝ) < 3 + s.re := by linarith
  have hsum_rpow : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-(3 + s.re))) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 + s.re))) 1).2
      (summable_natAddOne_rpow_neg hp)
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  have hbound : ∀ n : ℕ, ‖bernTerm (n + 1) s‖ ≤
      1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re)) := by
    intro n
    have h := norm_bernTerm_le_sharp (n + 1) hspos hs1
    have hc : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rwa [hc] at h
  have hsum_maj : Summable
      (fun n : ℕ => 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re))) :=
    hsum_rpow.mul_left _
  have hsum_norm : Summable (fun n : ℕ => ‖bernTerm (n + 1) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum_maj
  have htail : ∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 + s.re)) ≤ 29 / 200 :=
    tsum_natAddTwo_rpow_neg_le_half (by linarith)
  calc ‖∑' n : ℕ, bernTerm (n + 1) s‖ ≤ ∑' n : ℕ, ‖bernTerm (n + 1) s‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 2) ^ (-(3 + s.re)) :=
        hsum_norm.tsum_le_tsum hbound hsum_maj
    _ = 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 + s.re)) :=
        hsum_rpow.tsum_mul_left _
    _ ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (29 / 200) := by
        have hpos : (0 : ℝ) ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by positivity
        exact mul_le_mul_of_nonneg_left htail hpos
    _ = 29 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 38400 := by ring

/-- **The second-order Euler–Maclaurin representation with one explicit term.** -/
theorem riemannZeta_eq_main_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (1 - s) / (s - 1) + (2 : ℂ) ^ (-s) / 2
      + s * (2 : ℂ) ^ (-s - 1) / 12 + ∑' n : ℕ, bernTerm (n + 1) s := by
  have h := riemannZeta_eq_bernApprox 1 hs0 hs1
  norm_num at h
  rw [h]

/-- The `N = 1` Euler–Maclaurin representation, with the three correction terms grouped:
`ζ(s) = 1 + 2^(-s) (2/(s-1) + 1/2 + s/24) + R₁(s)`.  The grouping is what makes the criterion
useful: the three terms partially cancel. -/
theorem riemannZeta_eq_main_one_grouped {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) * (2 / (s - 1) + 1 / 2 + s / 24)
      + ∑' n : ℕ, bernTerm (n + 1) s := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have e1 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ h2, Complex.cpow_one]
  have e2 : (2 : ℂ) ^ (-s - 1) = (2 : ℂ) ^ (-s) / 2 := by
    rw [show -s - 1 = -s + -1 by ring, Complex.cpow_add _ _ h2,
      show ((-1 : ℂ)) = ((-1 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
    ring
  rw [riemannZeta_eq_main_one hs0 hs1, e1, e2]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- The real part of the grouped factor. -/
theorem grouped_factor_re (s : ℂ) :
    ((2 : ℂ) / (s - 1) + 1 / 2 + s / 24).re
      = 1 / 2 + s.re / 24 + 2 * (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  simp [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.sub_im]
  ring

/-- The imaginary part of the grouped factor. -/
theorem grouped_factor_im (s : ℂ) :
    ((2 : ℂ) / (s - 1) + 1 / 2 + s / 24).im
      = s.im / 24 - 2 * s.im / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

private lemma mid_poly_pos {r : ℝ} (h1 : 17 / 5 ≤ r) (h2 : r ≤ 7) :
    71 / 100 * (13 / 24 + (2 / r - r / 24))
      + 11 * ((r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3)) / 10368 < 1 := by
  have hr0 : (0:ℝ) < r := by linarith
  rw [show 71 / 100 * (13 / 24 + (2 / r - r / 24))
        + 11 * ((r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3)) / 10368
      = (71 / 100 * (13 * r / 24 + (2 - r * r / 24))
          + r * (11 * ((r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3)) / 10368)) / r from by
    field_simp, div_lt_one hr0]
  nlinarith [sq_nonneg (r - 5), sq_nonneg (r - 7), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

private lemma mid_poly_neg {r : ℝ} (h1 : 17 / 5 ≤ r) (h2 : r ≤ 7) :
    71 / 100 * (13 / 24 + (r / 24 - 71 / 250))
      + 11 * ((r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3)) / 10368 < 1 := by
  nlinarith [sq_nonneg (r - 5), sq_nonneg (r - 7), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

private lemma two_div_ge {r : ℝ} (h1 : 17 / 5 ≤ r) (h2 : r ≤ 7) :
    71 / 250 ≤ 2 * r / (r ^ 2 + 1 / 4) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-- `‖s‖ ≤ |t| + 3/20` inside the strip, for `|t| ≥ 17/5`. -/
private lemma norm_le_abs_im_add {s : ℂ} (h1 : s.re < 1) (h0 : 0 ≤ s.re)
    (hr : 17 / 5 ≤ |s.im|) : ‖s‖ ≤ |s.im| + 3 / 20 := by
  have hns : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg s, sq_abs s.im, abs_nonneg s.im]

/-- `‖s+1‖ ≤ |t| + 3/5` inside the strip, for `|t| ≥ 17/5`. -/
private lemma norm_add_one_le_abs_im_add {s : ℂ} (h1 : s.re < 1) (h0 : 0 ≤ s.re)
    (hr : 17 / 5 ≤ |s.im|) : ‖s + 1‖ ≤ |s.im| + 3 / 5 := by
  have hns : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
    ring
  nlinarith [norm_nonneg (s + 1), sq_abs s.im, abs_nonneg s.im]

/-- `‖s+2‖ ≤ |t| + 4/3` inside the strip, for `|t| ≥ 17/5`. -/
private lemma norm_add_two_le_abs_im_add {s : ℂ} (h1 : s.re < 1) (h0 : 0 ≤ s.re)
    (hr : 17 / 5 ≤ |s.im|) : ‖s + 2‖ ≤ |s.im| + 4 / 3 := by
  have hns : ‖s + 2‖ ^ 2 = (s.re + 2) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero]
    ring
  nlinarith [norm_nonneg (s + 2), sq_abs s.im, abs_nonneg s.im]

/-- **No zero of `ζ` in the right half of the strip with `17/5 ≤ |im s| ≤ 7`.** -/
theorem riemannZeta_ne_zero_of_abs_im_mid {s : ℂ} (hhalf : 1 / 2 ≤ s.re) (h1 : s.re < 1)
    (hlo : 17 / 5 ≤ |s.im|) (hhi : |s.im| ≤ 7) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  set r : ℝ := |s.im| with hrdef
  have hr0 : (0:ℝ) < r := by linarith
  have hsq : s.im ^ 2 = r ^ 2 := (sq_abs s.im).symm
  set D : ℝ := (s.re - 1) ^ 2 + s.im ^ 2 with hDdef
  have hD0 : 0 < D := by
    rw [hDdef, hsq]
    positivity
  have hDlow : r ^ 2 ≤ D := by
    rw [hDdef, hsq]
    nlinarith [sq_nonneg (s.re - 1)]
  have hDhigh : D ≤ r ^ 2 + 1 / 4 := by
    rw [hDdef, hsq]
    nlinarith
  -- the size of `2^(-s)`
  have hcast : ((2:ℝ) : ℂ) = (2:ℂ) := by norm_num
  have hp2 : ‖(2:ℂ) ^ (-s)‖ = (2:ℝ) ^ (-s.re) := by
    rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have hc : (2:ℝ) ^ (-s.re) ≤ 71 / 100 := rpow_two_neg_le hhalf
  have hc0 : (0:ℝ) < (2:ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by norm_num) _
  -- the size of the grouped factor
  set B : ℂ := 2 / (s - 1) + 1 / 2 + s / 24 with hBdef
  have hBre : B.re = 1 / 2 + s.re / 24 + 2 * (s.re - 1) / D := grouped_factor_re s
  have hBim : B.im = s.im / 24 - 2 * s.im / D := grouped_factor_im s
  have hre_le : |B.re| ≤ 13 / 24 := by
    rw [abs_le, hBre]
    have hneg : 2 * (s.re - 1) / D ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hD0.le
    have hlow : -(1 / D) ≤ 2 * (s.re - 1) / D := by
      rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hD0]
      linarith
    have hDbig : (1:ℝ) / D ≤ 1 / (17 / 5) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    constructor <;> [nlinarith; nlinarith]
  have him_le : |B.im| ≤ max (2 / r - r / 24) (r / 24 - 71 / 250) := by
    rw [hBim]
    have habs : |s.im / 24 - 2 * s.im / D| = r * |1 / 24 - 2 / D| := by
      rw [show s.im / 24 - 2 * s.im / D = s.im * (1 / 24 - 2 / D) by ring, abs_mul, hrdef]
    rw [habs]
    rcases le_or_gt (2 / D) (1 / 24) with hcase | hcase
    · refine le_trans ?_ (le_max_right _ _)
      rw [abs_of_nonneg (by linarith)]
      have h2D : 2 / (r ^ 2 + 1 / 4) ≤ 2 / D :=
        div_le_div_of_nonneg_left (by norm_num) hD0 hDhigh
      have hgr : 71 / 250 ≤ 2 * r / (r ^ 2 + 1 / 4) := two_div_ge hlo hhi
      have : r * (2 / (r ^ 2 + 1 / 4)) = 2 * r / (r ^ 2 + 1 / 4) := by ring
      nlinarith [mul_le_mul_of_nonneg_left h2D hr0.le]
    · refine le_trans ?_ (le_max_left _ _)
      rw [abs_of_nonpos (by linarith)]
      have h2D : 2 / D ≤ 2 / r ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hDlow
      have hrr : r * (2 / r ^ 2) = 2 / r := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left h2D hr0.le]
  have hBnorm : ‖B‖ ≤ 13 / 24 + max (2 / r - r / 24) (r / 24 - 71 / 250) :=
    le_trans (Complex.norm_le_abs_re_add_abs_im B) (by linarith)
  -- the linear factors
  have hns : ‖s‖ ≤ r + 3 / 20 := norm_le_abs_im_add h1 hs0.le hlo
  have hn1 : ‖s + 1‖ ≤ r + 3 / 5 := norm_add_one_le_abs_im_add h1 hs0.le hlo
  have hn2 : ‖s + 2‖ ≤ r + 4 / 3 := norm_add_two_le_abs_im_add h1 hs0.le hlo
  have hT : ‖∑' n : ℕ, bernTerm (n + 1) s‖
      ≤ 11 * ((r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3)) / 10368 := by
    refine (norm_tsum_bernTerm_shift_le hs0 hs1).trans ?_
    have h0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    have h0' : (0:ℝ) ≤ ‖s + 1‖ := norm_nonneg _
    have h0'' : (0:ℝ) ≤ ‖s + 2‖ := norm_nonneg _
    have hstep : ‖s‖ * ‖s + 1‖ ≤ (r + 3 / 20) * (r + 3 / 5) :=
      mul_le_mul hns hn1 h0' (by linarith)
    have hprod : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (r + 3 / 20) * (r + 3 / 5) * (r + 4 / 3) :=
      mul_le_mul hstep hn2 h0'' (by nlinarith)
    linarith
  -- combine
  have hrep := riemannZeta_eq_main_one_grouped hs0 hs1
  rw [hz, ← hBdef] at hrep
  have hone : (1:ℝ) ≤ ‖(2:ℂ) ^ (-s) * B‖ + ‖∑' n : ℕ, bernTerm (n + 1) s‖ := by
    have hsum : (1 : ℂ) = -((2:ℂ) ^ (-s) * B + ∑' n : ℕ, bernTerm (n + 1) s) := by
      linear_combination -hrep
    calc (1:ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖-((2:ℂ) ^ (-s) * B + ∑' n : ℕ, bernTerm (n + 1) s)‖ := by rw [← hsum]
      _ = ‖(2:ℂ) ^ (-s) * B + ∑' n : ℕ, bernTerm (n + 1) s‖ := norm_neg _
      _ ≤ ‖(2:ℂ) ^ (-s) * B‖ + ‖∑' n : ℕ, bernTerm (n + 1) s‖ := norm_add_le _ _
  have hmul : ‖(2:ℂ) ^ (-s) * B‖
      ≤ 71 / 100 * (13 / 24 + max (2 / r - r / 24) (r / 24 - 71 / 250)) := by
    rw [norm_mul, hp2]
    have hBnn : (0:ℝ) ≤ ‖B‖ := norm_nonneg B
    have hmax : (0:ℝ) ≤ 13 / 24 + max (2 / r - r / 24) (r / 24 - 71 / 250) := by linarith
    exact mul_le_mul hc hBnorm hBnn (by norm_num)
  -- the numerical contradiction
  rcases max_cases (2 / r - r / 24) (r / 24 - 71 / 250) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm] at hmul
    have := mid_poly_pos hlo hhi
    linarith
  · rw [hm] at hmul
    have := mid_poly_neg hlo hhi
    linarith

/-- **`ζ` has no zero in the critical strip below height `7`.** -/
theorem riemannZeta_ne_zero_of_abs_im_le_seven {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (ht : |s.im| ≤ 7) : riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt (17 / 5 : ℝ) |s.im| with hlo | hlo
  · rcases le_or_gt (1 / 2 : ℝ) s.re with hh | hh
    · exact riemannZeta_ne_zero_of_abs_im_mid hh h1 hlo ht hz
    · have hz' := riemannZeta_one_sub_eq_zero_of_mem_strip h0 h1 hz
      have hre : (1 - s).re = 1 - s.re := by simp
      have him : |(1 - s).im| = |s.im| := by simp
      refine riemannZeta_ne_zero_of_abs_im_mid (s := 1 - s) ?_ ?_ ?_ ?_ hz'
      · rw [hre]; linarith
      · rw [hre]; linarith
      · rw [him]; exact hlo
      · rw [him]; exact ht
  · exact riemannZeta_ne_zero_of_abs_im_le h0 h1 (by linarith) hz

/-- **The Riemann hypothesis, verified up to height `7`.** -/
theorem verifiedUpToHeight_seven : VerifiedUpToHeight 7 := by
  intro s hz him hlt
  exfalso
  have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
    rintro ⟨n, rfl⟩
    simp at him
  obtain ⟨hl, hr⟩ := zero_of_nontrivial_mem_strip hz htriv
  exact riemannZeta_ne_zero_of_abs_im_le_seven hl hr
    (by rw [abs_of_pos him]; linarith) hz

/-- The Riemann hypothesis is verified up to every height at most `7`. -/
theorem verifiedUpToHeight_of_le_seven {H : ℝ} (hH : H ≤ 7) : VerifiedUpToHeight H :=
  fun s hz him hlt => verifiedUpToHeight_seven s hz him (lt_of_lt_of_le hlt hH)

end RiemannHypothesis

end
