/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareBernoulli
import RiemannHypothesis.Partial
import RiemannHypothesis.Zeros

/-!
# The Riemann hypothesis, verified up to a positive height

`RiemannHypothesis.Partial` states the numerical verification `VerifiedUpToHeight H` — *every
zero of `ζ` with `0 < im s < H` lies on the critical line* — and
`RiemannHypothesis.zeta_strip_iff_forall_verifiedUpToHeight` proves that the Riemann hypothesis
is exactly the conjunction of these statements over all heights `H`.  Until now the repository
proved no instance of `VerifiedUpToHeight` with `H > 0`.  This file proves one,
unconditionally and without any numerics:

* `verifiedUpToHeight_seven_halves` : `VerifiedUpToHeight (7/2)`.

The proof is the second-order Euler–Maclaurin representation of `ζ` of
`RiemannHypothesis.StripMeanSquareBernoulli`, taken with **no** explicit Dirichlet terms
(`N = 0`):

`ζ(s) = 1/(s-1) + 1/2 + s/12 + R(s)`,  `‖R(s)‖ ≤ 5 ‖s‖ ‖s+1‖ ‖s+2‖ / 768`

on the punctured right half-plane (`norm_riemannZeta_sub_main_le`).  The constant `5/768` is the
constant `1/192` of `norm_bernTerm_le_sharp` times the tail bound `5/4` of
`tsum_natAddOne_rpow_neg_le_five_quarters`.  Two sharpenings of the material in
`StripMeanSquareBernoulli` feed into it:

* the mean `∫₀¹ |B₃(u)|/6 du = 1/192` replaces the supremum bound `‖B₃/6‖ ≤ 1/48` used in
  `norm_bernTerm_le` — a factor of `4` (`integral_abs_bern3Poly`, `norm_bernTerm_le_sharp`);
* `∑' n, (n+1)^(-p) ≤ 5/4` for `p ≥ 3` replaces the bound `2` of `tsum_shift_rpow_neg_le`
  (`tsum_natAddOne_rpow_neg_le_five_quarters`).

The main term factors,

`1/(s-1) + 1/2 + s/12 = (s+2)(s+3) / (12 (s-1))`,

so a zero of `ζ` forces `64 ‖s+3‖ ≤ 5 ‖s‖ ‖s+1‖ ‖s-1‖` — the factor `‖s+2‖` cancels.  This is
an entirely explicit nonvanishing criterion:

* `riemannZeta_ne_zero_of_norm_mul_lt` : if `0 < re s`, `s ≠ 1` and
  `5 (‖s‖ ‖s+1‖ ‖s-1‖) < 64 ‖s+3‖`, then `ζ(s) ≠ 0`.

Squaring, the criterion is the polynomial inequality
`25 (σ² + t²)((σ+1)² + t²)((σ-1)² + t²) < 4096 ((σ+3)² + t²)`, which holds throughout the
critical strip as long as `|t| ≤ 7/2` (`riemannZeta_ne_zero_of_abs_im_le`).  The criterion itself
breaks down at `|t| ≈ 3.89`, and the first zero of `ζ` sits at `t ≈ 14.13`, so this is very far
from the numerical verifications in the literature (Platt–Trudgian: `3 × 10¹²`); what it does
give is a genuine, unconditional, machine-checked slice of the Riemann hypothesis.

## Main results

* `integral_abs_bern3Poly` — `∫₀¹ |B₃| = 1/32`;
* `norm_bernTerm_le_sharp` — the second-order Euler–Maclaurin term in mean, constant `1/192`;
* `tsum_natAddOne_rpow_neg_le_five_quarters` — `∑' n, (n+1)^(-p) ≤ 5/4` for `3 ≤ p`;
* `norm_riemannZeta_sub_main_le` — the `N = 0` second-order Euler–Maclaurin bound;
* `riemannZeta_ne_zero_of_norm_mul_lt` — the nonvanishing criterion;
* `riemannZeta_ne_zero_of_abs_im_le` — `ζ` has no zero in the critical strip with `|im s| ≤ 7/2`;
* `verifiedUpToHeight_seven_halves` — `VerifiedUpToHeight (7/2)`;
* `verifiedUpToHeight_of_le_seven_halves` — hence `VerifiedUpToHeight H` for every `H ≤ 7/2`.
-/

noncomputable section

open Complex MeasureTheory

namespace RiemannHypothesis

/-! ## The mean of the third Bernoulli polynomial -/

private lemma hasDerivAt_bern3Prim (u : ℝ) :
    HasDerivAt (fun v : ℝ => v ^ 4 / 4 - v ^ 3 / 2 + v ^ 2 / 4)
      (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) u := by
  have h := (((hasDerivAt_pow 4 u).div_const 4).sub ((hasDerivAt_pow 3 u).div_const 2)).add
    ((hasDerivAt_pow 2 u).div_const 4)
  norm_num at h
  exact h.congr_deriv (by ring)

private lemma continuous_bern3Poly :
    Continuous (fun u : ℝ => u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) := by fun_prop

/-- **The mean of the third Bernoulli polynomial** `B₃(u) = u(u - 1/2)(u - 1)`:
`∫₀¹ |B₃| = 1/32`, four times smaller than its supremum `1/8` on `[0, 1]`. -/
theorem integral_abs_bern3Poly :
    ∫ u in (0:ℝ)..1, |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u| = 1 / 32 := by
  have hsplit : ∫ u in (0:ℝ)..1, |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u|
      = (∫ u in (0:ℝ)..(1/2), |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u|)
        + ∫ u in (1/2:ℝ)..1, |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u| := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact continuous_bern3Poly.abs.intervalIntegrable _ _
    · exact continuous_bern3Poly.abs.intervalIntegrable _ _
  have h1 : ∫ u in (0:ℝ)..(1/2), |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u|
      = ∫ u in (0:ℝ)..(1/2), (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    obtain ⟨h0, h1⟩ := hu
    refine abs_of_nonneg ?_
    nlinarith [mul_nonneg (mul_nonneg h0 (show (0:ℝ) ≤ 1/2 - u by linarith))
      (show (0:ℝ) ≤ 1 - u by linarith)]
  have h2 : ∫ u in (1/2:ℝ)..1, |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u|
      = ∫ u in (1/2:ℝ)..1, -(u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    obtain ⟨h0, h1⟩ := hu
    refine abs_of_nonpos ?_
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ u by linarith)
      (show (0:ℝ) ≤ u - 1/2 by linarith)) (show (0:ℝ) ≤ 1 - u by linarith)]
  have e1 : ∫ u in (0:ℝ)..(1/2), (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) = 1 / 64 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_bern3Prim u)
      (continuous_bern3Poly.intervalIntegrable _ _)]
    norm_num
  have e2 : ∫ u in (1/2:ℝ)..1, (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) = -(1 / 64) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_bern3Prim u)
      (continuous_bern3Poly.intervalIntegrable _ _)]
    norm_num
  rw [hsplit, h1, h2, intervalIntegral.integral_neg, e1, e2]
  norm_num

/-- The exact size of the Green's function of the second Euler–Maclaurin correction. -/
theorem norm_bern3Green_eq (a x : ℝ) :
    ‖bern3Green a (x : ℂ)‖ = |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| / 6 := by
  have hcast : (x : ℂ) - (a : ℂ) = ((x - a : ℝ) : ℂ) := by push_cast; ring
  have hre : bern3Green a (x : ℂ)
      = ((((x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)) / 6 : ℝ) : ℂ) := by
    unfold bern3Green
    rw [hcast]
    push_cast
    ring
  rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]

/-- **The size of the second-order Euler–Maclaurin term, sharpened**:
`‖bernTerm n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ (n+1)^(-(3+σ))/192`.  This is `norm_bernTerm_le` with the
supremum bound `‖B₃/6‖ ≤ 1/48` replaced by the mean `∫₀¹ |B₃|/6 = 1/192`. -/
theorem norm_bernTerm_le_sharp (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖bernTerm n s‖ ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  set M : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * a ^ (-(3 + s.re)) with hM
  rw [bernTerm_eq_integral n hs0 hs1, ← ha]
  have hbd : ∀ x ∈ Set.Ioc a (a + 1),
      ‖bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))‖
        ≤ M / 6 * |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_trans ha0 hx1
    have hnorm : ‖(x : ℂ) ^ (-s - 3)‖ = x ^ (-(3 + s.re)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp [Complex.sub_re, Complex.neg_re]
      ring
    have hpow : x ^ (-(3 + s.re)) ≤ a ^ (-(3 + s.re)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hx1.le (by linarith)
    simp only [norm_mul, norm_neg]
    rw [norm_bern3Green_eq, hnorm]
    have h1 : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * x ^ (-(3 + s.re)) ≤ M := by
      rw [hM]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    calc |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| / 6
          * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * x ^ (-(3 + s.re)))
        ≤ |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| / 6 * M :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M / 6 * |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| := by ring
  have hcont : Continuous fun x : ℝ =>
      M / 6 * |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)| := by fun_prop
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := a) (b := a + 1)
    (by linarith) (Filter.Eventually.of_forall hbd) (hcont.intervalIntegrable _ _)
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  have hsub : (∫ x in a..(a + 1), |(x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)|)
      = ∫ u in (0:ℝ)..1, |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u| := by
    have := intervalIntegral.integral_comp_sub_right
      (a := a) (b := a + 1) (fun u : ℝ => |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u|) a
    simpa using this
  rw [hsub, integral_abs_bern3Poly, hM]
  ring

/-! ## A sharp tail bound for the cubic `p`-series -/

/-- The partial sums of `∑ 1/(n+1)³`, bounded by telescoping against
`1/(n(n+1)(n+2))`. -/
theorem sum_range_natAddOne_cube_inv_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.range M, (1 : ℝ) / ((n : ℝ) + 1) ^ 3 ≤ 5 / 4 - 1 / (2 * (M : ℝ) * ((M : ℝ) + 1))
    := by
  refine Nat.le_induction ?_ ?_ M hM
  · norm_num
  · intro M hM ih
    have hM0 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    rw [Finset.sum_range_succ]
    have hstep : (1 : ℝ) / ((M : ℝ) + 1) ^ 3 ≤ 1 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have harith : 5 / 4 - 1 / (2 * (M : ℝ) * ((M : ℝ) + 1))
          + 1 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2))
        = 5 / 4 - 1 / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 1 + 1)) := by
      have h1 : (M : ℝ) ≠ 0 := by linarith
      have h2 : (M : ℝ) + 1 ≠ 0 := by linarith
      have h3 : (M : ℝ) + 2 ≠ 0 := by linarith
      field_simp
      ring
    push_cast
    linarith

/-- **The tail bound** `∑' n, (n+1)^(-p) ≤ 5/4` for every `p ≥ 3`.  (The true value at `p = 3`
is `ζ(3) = 1.202…`; the bound `2` of `tsum_shift_rpow_neg_le` would cost a factor `8/5` in the
height reached below.) -/
theorem tsum_natAddOne_rpow_neg_le_five_quarters {p : ℝ} (hp : 3 ≤ p) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) ≤ 5 / 4 := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  have hterm : ∀ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-p) ≤ (1 : ℝ) / ((n : ℝ) + 1) ^ 3 := by
    intro n _
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h := Real.rpow_le_rpow_of_exponent_le hx (show -p ≤ (-3 : ℝ) by linarith)
    have hcast : ((n : ℝ) + 1) ^ (-3 : ℝ) = 1 / ((n : ℝ) + 1) ^ 3 := by
      rw [show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
      simp
    rwa [hcast] at h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · norm_num
  · have hsum := sum_range_natAddOne_cube_inv_le hM
    have hMpos : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hpos : 0 < 1 / (2 * (M : ℝ) * ((M : ℝ) + 1)) := by positivity
    linarith

/-! ## The second-order Euler–Maclaurin representation with no explicit terms -/

/-- The tail of the second-order Euler–Maclaurin expansion, at `N = 0`:
`‖∑' n, bernTerm n s‖ ≤ 5 ‖s‖ ‖s+1‖ ‖s+2‖ / 768`. -/
theorem norm_tsum_bernTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' n : ℕ, bernTerm n s‖ ≤ 5 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 768 := by
  have hp : (1 : ℝ) < 3 + s.re := by linarith
  have hsum_rpow : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 + s.re))) :=
    summable_natAddOne_rpow_neg hp
  have hbound : ∀ n : ℕ, ‖bernTerm n s‖ ≤
      1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re)) :=
    fun n => norm_bernTerm_le_sharp n hs0 hs1
  have hsum_maj : Summable
      (fun n : ℕ => 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re))) :=
    hsum_rpow.mul_left _
  have hsum_norm : Summable (fun n : ℕ => ‖bernTerm n s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum_maj
  have htail : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 + s.re)) ≤ 5 / 4 :=
    tsum_natAddOne_rpow_neg_le_five_quarters (by linarith)
  calc ‖∑' n : ℕ, bernTerm n s‖ ≤ ∑' n : ℕ, ‖bernTerm n s‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re)) :=
        hsum_norm.tsum_le_tsum hbound hsum_maj
    _ = 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 + s.re)) :=
        hsum_rpow.tsum_mul_left _
    _ ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (5 / 4) := by
        have hpos : (0 : ℝ) ≤ 1 / 192 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by positivity
        exact mul_le_mul_of_nonneg_left htail hpos
    _ = 5 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 768 := by ring

/-- **The second-order Euler–Maclaurin bound with no explicit Dirichlet terms**:
`ζ(s) = 1/(s-1) + 1/2 + s/12 + R(s)` with `‖R(s)‖ ≤ 5 ‖s‖ ‖s+1‖ ‖s+2‖ / 768`, on the punctured
right half-plane. -/
theorem norm_riemannZeta_sub_main_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - (1 / (s - 1) + 1 / 2 + s / 12)‖ ≤ 5 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 768 := by
  have h := riemannZeta_eq_bernApprox 0 hs0 hs1
  simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add, Complex.ofReal_one,
    Complex.one_cpow, mul_one, Nat.add_zero] at h
  have heq : riemannZeta s - (1 / (s - 1) + 1 / 2 + s / 12) = ∑' n : ℕ, bernTerm n s := by
    rw [h]; ring
  rw [heq]
  exact norm_tsum_bernTerm_le hs0 hs1

/-! ## The nonvanishing criterion -/

/-- **A nonvanishing criterion for `ζ` on the right half-plane.**  If `0 < re s`, `s ≠ 1` and
`5 (‖s‖ ‖s+1‖ ‖s-1‖) < 64 ‖s+3‖`, then `ζ(s) ≠ 0`.  This is the second-order Euler–Maclaurin
expansion at `N = 0`, whose main term is `(s+2)(s+3) / (12 (s-1))`. -/
theorem riemannZeta_ne_zero_of_norm_mul_lt {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (h : 5 * (‖s‖ * ‖s + 1‖ * ‖s - 1‖) < 64 * ‖s + 3‖) : riemannZeta s ≠ 0 := by
  intro hz
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs2 : s + 2 ≠ 0 := by
    intro h2
    have hre : s.re = -2 := by
      have := congrArg Complex.re h2
      simp only [Complex.add_re, Complex.re_ofNat, Complex.zero_re] at this
      linarith
    rw [hre] at hs0
    norm_num at hs0
  have hmain := norm_riemannZeta_sub_main_le hs0 hs1
  rw [hz, zero_sub, norm_neg] at hmain
  have hfac : 1 / (s - 1) + 1 / 2 + s / 12 = (s + 2) * (s + 3) / (12 * (s - 1)) := by
    field_simp
    ring
  rw [hfac] at hmain
  have hnorm : ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ = ‖s + 2‖ * ‖s + 3‖ / (12 * ‖s - 1‖) := by
    rw [norm_div, norm_mul, norm_mul]
    norm_num
  rw [hnorm] at hmain
  have hnorm_sub : (0 : ℝ) < ‖s - 1‖ := norm_pos_iff.mpr hsub
  have hnorm_s2 : (0 : ℝ) < ‖s + 2‖ := norm_pos_iff.mpr hs2
  have h1 : ‖s + 2‖ * ‖s + 3‖ ≤ 5 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) / 768 * (12 * ‖s - 1‖) :=
    (div_le_iff₀ (by positivity)).mp hmain
  have h2 : ‖s + 2‖ * (64 * ‖s + 3‖) ≤ ‖s + 2‖ * (5 * (‖s‖ * ‖s + 1‖ * ‖s - 1‖)) := by
    nlinarith [h1, hnorm_s2]
  have h3 := le_of_mul_le_mul_left h2 hnorm_s2
  linarith

/-! ## No zeroes in the strip below height `7/2` -/

/-- The polynomial form of the criterion inside the strip: for `0 ≤ σ ≤ 1` and `0 ≤ t² ≤ 49/4`,
`25 (σ² + t²)((σ+1)² + t²)((σ-1)² + t²) < 4096 ((σ+3)² + t²)`. -/
private lemma small_height_poly {x u : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (hu : 0 ≤ u)
    (hu2 : u ≤ 49 / 4) :
    25 * ((x ^ 2 + u) * ((x + 1) ^ 2 + u) * ((x - 1) ^ 2 + u)) < 4096 * ((x + 3) ^ 2 + u) := by
  have hv0 : 0 ≤ x * (1 - x) := mul_nonneg h0 (by linarith)
  have hv4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  rcases le_or_gt u (1 / 8) with h | h
  · nlinarith [sq_nonneg (u - x * (1 - x)), sq_nonneg x, sq_nonneg (x - 1)]
  · have hAC : (x ^ 2 + u) * ((x - 1) ^ 2 + u) ≤ u + u ^ 2 := by nlinarith
    have hB : (x + 1) ^ 2 + u ≤ 4 + u := by nlinarith
    have hstep : 25 * ((x ^ 2 + u) * ((x + 1) ^ 2 + u) * ((x - 1) ^ 2 + u))
        ≤ 25 * ((u + u ^ 2) * (4 + u)) := by nlinarith [sq_nonneg x]
    have hfinal : 25 * ((u + u ^ 2) * (4 + u)) < 4096 * (9 + u) := by
      nlinarith [mul_nonneg hu hu, sq_nonneg u]
    nlinarith [hstep, hfinal, sq_nonneg x]

/-- **`ζ` has no zero in the critical strip below height `7/2`.** -/
theorem riemannZeta_ne_zero_of_abs_im_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (ht : |s.im| ≤ 7 / 2) : riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  refine riemannZeta_ne_zero_of_norm_mul_lt h0 hs1 ?_
  set x : ℝ := s.re with hx
  set u : ℝ := s.im ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu2 : u ≤ 49 / 4 := by
    rw [hu]
    nlinarith [abs_nonneg s.im, sq_abs s.im, neg_abs_le s.im, le_abs_self s.im]
  have hns : ‖s‖ ^ 2 = x ^ 2 + u := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hx, hu]
    ring
  have hn1 : ‖s + 1‖ ^ 2 = (x + 1) ^ 2 + u := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero, hx, hu]
    ring
  have hn3 : ‖s + 3‖ ^ 2 = (x + 3) ^ 2 + u := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero,
      hx, hu]
    ring
  have hnm1 : ‖s - 1‖ ^ 2 = (x - 1) ^ 2 + u := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, hx, hu]
    ring
  have hpoly := small_height_poly (x := x) h0.le h1.le hu0 hu2
  have hsq : (5 * (‖s‖ * ‖s + 1‖ * ‖s - 1‖)) ^ 2 < (64 * ‖s + 3‖) ^ 2 := by
    have hl : (5 * (‖s‖ * ‖s + 1‖ * ‖s - 1‖)) ^ 2
        = 25 * ((x ^ 2 + u) * ((x + 1) ^ 2 + u) * ((x - 1) ^ 2 + u)) := by
      rw [mul_pow, mul_pow, mul_pow, hns, hn1, hnm1]
      norm_num
    have hr : (64 * ‖s + 3‖) ^ 2 = 4096 * ((x + 3) ^ 2 + u) := by
      rw [mul_pow, hn3]
      norm_num
    rw [hl, hr]
    exact hpoly
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-! ## The Riemann hypothesis up to height `7/2` -/

/-- **The Riemann hypothesis, verified up to height `7/2`.**  Every zero of `ζ` with
`0 < im s < 7/2` lies on the critical line — vacuously, since `ζ` has no such zero at all. -/
theorem verifiedUpToHeight_seven_halves : VerifiedUpToHeight (7 / 2) := by
  intro s hz him hlt
  exfalso
  have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
    rintro ⟨n, rfl⟩
    simp at him
  obtain ⟨hl, hr⟩ := zero_of_nontrivial_mem_strip hz htriv
  exact riemannZeta_ne_zero_of_abs_im_le hl hr (by rw [abs_of_pos him]; linarith) hz

/-- The Riemann hypothesis is verified up to every height at most `7/2`. -/
theorem verifiedUpToHeight_of_le_seven_halves {H : ℝ} (hH : H ≤ 7 / 2) : VerifiedUpToHeight H :=
  fun s hz him hlt => verifiedUpToHeight_seven_halves s hz him (lt_of_lt_of_le hlt hH)

end RiemannHypothesis

end
