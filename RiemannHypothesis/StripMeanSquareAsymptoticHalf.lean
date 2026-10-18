/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareAsymptotic
import RiemannHypothesis.StripMeanSquareBohrLandau

/-!
# The Bohr–Landau asymptotic mean square of `ζ` for every `σ > 1/2`

`RiemannHypothesis.StripMeanSquareAsymptotic` proves the asymptotic

`∫₀ᵀ ‖ζ(σ + i t)‖² dt = ζ(2σ) T + O_σ(T^(1-c))`

only in the range `3/5 < σ < 1`, because it compares `ζ` with a Dirichlet polynomial through the
*trapezoidal* Euler–Maclaurin expansion, whose error `O(‖s‖² N^(-1-σ))` forces the polynomial to
be of length at least `T^(2/(1+σ))`.  `RiemannHypothesis.StripMeanSquareBohrLandau` removes that
obstruction for the *upper bound* by expanding to an arbitrary order `m`, with error
`O_m(‖s‖^m N^(1-σ-m))`.  This file combines the two: the two-sided mean value theorem for
Dirichlet polynomials of the first file, applied to a polynomial of length `N ≍ T^e` with

`m/(σ + m - 1) < e < 1/(2 - 2σ)`,

an interval which is non-empty exactly when `m (2σ - 1) > 1 - σ`, hence for some `m` as soon as
`σ > 1/2`.  The result is the theorem of Bohr and Landau in its full range.

## Main results

* `emOrder` and `meanSquareExponentHalf` — the order of the expansion and the exponent of the
  length of the Dirichlet polynomial, together with the two inequalities placing the exponent
  inside its admissible interval.
* `integral_normSq_error_em_le` — the mean square of the Euler–Maclaurin error of order `m`.
* `exists_integral_normSq_riemannZeta_asymptotic_half` — for `1/2 < σ < 1` there are `C, c > 0`
  with `|∫₀ᵀ ‖ζ(σ + i t)‖² dt - ζ(2σ) T| ≤ C T^(1-c)` for every `T ≥ 1`.
* `tendsto_integral_normSq_riemannZeta_div_half` — the same statement in limit form.

Nothing is claimed in this file on the critical line `σ = 1/2`, where the mean square is
`~ T log T` (proved in `RiemannHypothesis/HardyLittlewoodMeanSquare.lean`, without the
approximate functional equation); and no consequence for the zeroes is drawn.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## The mean square of the Euler–Maclaurin error of order `m` -/

/-- The mean square of the error of the Euler–Maclaurin expansion of order `m`: the analogue,
for the expansion of arbitrary order, of `integral_normSq_error_trap_le`. -/
theorem integral_normSq_error_em_le {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2))
        + 3 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T
        + 3 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set D : ℝ := 3 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) with hD
  set E : ℝ := 3 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) with hE
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))) + D + E := by
    rintro t ⟨ht0, htT⟩
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have habs : |t| = t := abs_of_nonneg ht0
    have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hs]
      simp [Complex.normSq_apply]
      ring
    have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
      have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
      nlinarith [norm_nonneg (s - 1), hnormsq]
    have hbdt := hbd N hN t (by rw [habs]; linarith)
    set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
    set A1 : ℝ := (N : ℝ) ^ (-σ) with hA1
    set B1 : ℝ := (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)) with hB1
    have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
    have hA10 : 0 ≤ A1 := by rw [hA1]; positivity
    have hB10 : 0 ≤ B1 := by
      rw [hB1]
      have h : (0 : ℝ) ≤ σ + |t| + m := by positivity
      positivity
    have hsq : ‖riemannZeta s - dirichletPoly (fun _ => 1) N s‖ ^ 2
        ≤ 3 * (E1 ^ 2 + (C * A1) ^ 2 + (C * B1) ^ 2) := by
      have hexp : ‖riemannZeta s - dirichletPoly (fun _ => 1) N s‖ ≤ E1 + C * A1 + C * B1 := by
        have hCd : C * (A1 + B1) = C * A1 + C * B1 := by ring
        linarith [hbdt, hCd]
      have hCA : 0 ≤ C * A1 := mul_nonneg hC hA10
      have hCB : 0 ≤ C * B1 := mul_nonneg hC hB10
      nlinarith [norm_nonneg (riemannZeta s - dirichletPoly (fun _ => 1) N s), hexp,
        sq_nonneg (E1 - C * A1), sq_nonneg (E1 - C * B1), sq_nonneg (C * A1 - C * B1),
        hE10, hCA, hCB]
    have hE1sq : E1 ^ 2 = A * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
      rw [hE1, div_pow, hnormsq, hA, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hA1pow : A1 ^ 2 = (N : ℝ) ^ (-(2 * σ)) := by
      rw [hA1, ← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have hA1sq : (C * A1) ^ 2 = C ^ 2 * (N : ℝ) ^ (-(2 * σ)) := by
      rw [mul_pow, hA1pow]
    have hB1sq : (C * B1) ^ 2
        ≤ C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) := by
      have hpow : ((N : ℝ) ^ (1 - σ - (m : ℝ))) ^ 2 = (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (1 - σ - (m : ℝ))) 2, ← Real.rpow_mul hN0.le]
        norm_num
        ring_nf
      have hbase : σ + |t| + m ≤ σ + T + m := by rw [habs]; linarith
      have hb0 : (0 : ℝ) ≤ σ + |t| + m := by positivity
      have hmono : ((σ + |t| + m) ^ m) ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hb0 hbase m) 2
      have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
      have hstep : B1 ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
        rw [hB1, mul_pow, hpow]
        exact mul_le_mul_of_nonneg_right hmono hrp
      have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
      calc (C * B1) ^ 2 = C ^ 2 * B1 ^ 2 := by ring
        _ ≤ C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep hC2
    rw [hD, hE]
    linarith [hsq, hE1sq, hA1sq, hB1sq]
  -- integrate
  have hdiff : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    (((continuous_riemannZeta_line_of_lt_one h1).sub
      (continuous_dirichletPoly_line N)).norm).pow 2
  have hcont1 : Continuous (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) :=
    Continuous.div continuous_const (by fun_prop) fun t => by
      have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by
        have : (0 : ℝ) < (1 - σ) ^ 2 := pow_pos (by linarith) 2
        nlinarith [sq_nonneg t]
      exact ne_of_gt hpos
  have hi1 : IntervalIntegrable (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))))
      volume 0 T :=
    (continuous_const.mul (continuous_const.mul hcont1)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun _ : ℝ => D) volume 0 T :=
    intervalIntegrable_const
  have hi3 : IntervalIntegrable (fun _ : ℝ => E) volume 0 T :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hdiff.intervalIntegrable 0 T)
    ((hi1.add hi2).add hi3) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hphi : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero]
  nlinarith [hphi, hA0]

/-! ## The order of the expansion and the length of the Dirichlet polynomial -/

/-- The order of the Euler–Maclaurin expansion used for the abscissa `σ`: the least integer with
`m (2σ - 1) > 1 - σ`, which exists for every `σ > 1/2`. -/
def emOrder (σ : ℝ) : ℕ := ⌈(1 - σ) / (2 * σ - 1)⌉₊ + 1

theorem one_le_emOrder (σ : ℝ) : 1 ≤ emOrder σ := by
  rw [emOrder]; omega

theorem emOrder_spec {σ : ℝ} (h0 : 1 / 2 < σ) : 1 - σ < (emOrder σ : ℝ) * (2 * σ - 1) := by
  have h2s : (0 : ℝ) < 2 * σ - 1 := by linarith
  have h := Nat.le_ceil ((1 - σ) / (2 * σ - 1))
  have hcast : ((⌈(1 - σ) / (2 * σ - 1)⌉₊ : ℕ) : ℝ) + 1 = (emOrder σ : ℝ) := by
    rw [emOrder]; push_cast; ring
  have hlt : (1 - σ) / (2 * σ - 1) < (emOrder σ : ℝ) := by linarith
  rw [div_lt_iff₀ h2s] at hlt
  linarith

/-- The exponent used for the length of the Dirichlet polynomial: the midpoint of the interval
`(m/(σ + m - 1), 1/(2 - 2σ))`, with `m = emOrder σ`; the interval is non-empty for every
`σ > 1/2`. -/
def meanSquareExponentHalf (σ : ℝ) : ℝ :=
  ((emOrder σ : ℝ) / (σ + (emOrder σ : ℝ) - 1) + 1 / (2 - 2 * σ)) / 2

theorem meanSquareExponentHalf_gt {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    (emOrder σ : ℝ) / (σ + (emOrder σ : ℝ) - 1) < meanSquareExponentHalf σ := by
  have hm1 : (1 : ℝ) ≤ (emOrder σ : ℝ) := by exact_mod_cast one_le_emOrder σ
  have hden : (0 : ℝ) < σ + (emOrder σ : ℝ) - 1 := by linarith
  have h2σ : (0 : ℝ) < 2 - 2 * σ := by linarith
  have hkey := emOrder_spec h0
  have hlt : (emOrder σ : ℝ) / (σ + (emOrder σ : ℝ) - 1) < 1 / (2 - 2 * σ) := by
    rw [div_lt_div_iff₀ hden h2σ]
    nlinarith
  rw [meanSquareExponentHalf]
  linarith

theorem meanSquareExponentHalf_lt {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    meanSquareExponentHalf σ < 1 / (2 - 2 * σ) := by
  have hm1 : (1 : ℝ) ≤ (emOrder σ : ℝ) := by exact_mod_cast one_le_emOrder σ
  have hden : (0 : ℝ) < σ + (emOrder σ : ℝ) - 1 := by linarith
  have h2σ : (0 : ℝ) < 2 - 2 * σ := by linarith
  have hkey := emOrder_spec h0
  have hlt : (emOrder σ : ℝ) / (σ + (emOrder σ : ℝ) - 1) < 1 / (2 - 2 * σ) := by
    rw [div_lt_div_iff₀ hden h2σ]
    nlinarith
  rw [meanSquareExponentHalf]
  linarith

theorem one_lt_meanSquareExponentHalf {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    1 < meanSquareExponentHalf σ := by
  have hm1 : (1 : ℝ) ≤ (emOrder σ : ℝ) := by exact_mod_cast one_le_emOrder σ
  have hden : (0 : ℝ) < σ + (emOrder σ : ℝ) - 1 := by linarith
  have h : (1 : ℝ) < (emOrder σ : ℝ) / (σ + (emOrder σ : ℝ) - 1) := by
    rw [lt_div_iff₀ hden]; linarith
  linarith [meanSquareExponentHalf_gt h0 h1]

/-- The data used in the proof of the asymptotic: an order `m` of the Euler–Maclaurin expansion
and an exponent `e` of the length of the Dirichlet polynomial, with `e` inside the admissible
interval `(m/(σ + m - 1), 1/(2 - 2σ))`.  Stated as an existence statement so that the proof of
the asymptotic never unfolds `emOrder` or `meanSquareExponentHalf`. -/
theorem exists_emOrder_meanSquareExponent {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ (m : ℕ) (e : ℝ), 1 ≤ m ∧ 1 < e ∧ (m : ℝ) / (σ + (m : ℝ) - 1) < e ∧ e < 1 / (2 - 2 * σ) :=
  ⟨emOrder σ, meanSquareExponentHalf σ, one_le_emOrder σ, one_lt_meanSquareExponentHalf h0 h1,
    meanSquareExponentHalf_gt h0 h1, meanSquareExponentHalf_lt h0 h1⟩

/-! ## Arithmetic helpers -/

private theorem rpow_neg_mul_base' {T : ℝ} (hT : 0 < T) (r : ℝ) :
    T ^ (-r) * T = T ^ (1 - r) := by
  have h : T ^ (-r) * T ^ (1 : ℝ) = T ^ (-r + 1) := (Real.rpow_add hT _ _).symm
  rw [Real.rpow_one] at h
  rw [h, show -r + 1 = 1 - r by ring]

/-- If `y ≤ c x` with `c ≥ 1` and the exponent `r` lies in `[0, 2]`, then `y^r ≤ c² x^r`. -/
private theorem rpow_le_sq_mul' {c x y r : ℝ} (hc : 1 ≤ c) (hx : 0 < x) (hy : 0 ≤ y)
    (hyc : y ≤ c * x) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) : y ^ r ≤ c ^ 2 * x ^ r := by
  have h1 : y ^ r ≤ (c * x) ^ r := Real.rpow_le_rpow hy hyc hr0
  rw [Real.mul_rpow (by linarith) hx.le] at h1
  have h2 : c ^ r ≤ c ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hr2
  have h3 : c ^ (2 : ℝ) = c ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at h2
  have h4 : (0 : ℝ) ≤ x ^ r := Real.rpow_nonneg hx.le r
  nlinarith

/-- Multiplying a bound `A ≤ a T^(1-g)` by a bound `L ≤ b T^(g/2)`. -/
private theorem prod_le_rpow_of_bounds' {T A L a b g : ℝ} (hT : 0 < T) (hA0 : 0 ≤ A)
    (hL0 : 0 ≤ L) (hA : A ≤ a * T ^ (1 - g)) (hL : L ≤ b * T ^ (g / 2)) :
    A * L ≤ a * b * T ^ (1 - g / 2) := by
  have h1 : A * L ≤ a * T ^ (1 - g) * (b * T ^ (g / 2)) :=
    mul_le_mul hA hL hL0 (le_trans hA0 hA)
  have h2 : a * T ^ (1 - g) * (b * T ^ (g / 2)) = a * b * T ^ (1 - g / 2) := by
    rw [show a * T ^ (1 - g) * (b * T ^ (g / 2)) = a * b * (T ^ (1 - g) * T ^ (g / 2)) by ring,
      ← Real.rpow_add hT]
    congr 2
    ring
  linarith [h1, h2]

/-- Turning the comparison inequality into a power saving, with `ε = T^(-c)` and `cs = 2c`. -/
private theorem comparison_bound' {Z P E T a CE c : ℝ} (hT : 1 ≤ T) (hc : 0 < c)
    (hCE : 0 ≤ CE) (hcomp : |Z - P| ≤ T ^ (-c) * P + E / T ^ (-c) + E)
    (hP : P ≤ a * T) (hE : E ≤ CE * T ^ (1 - 2 * c)) :
    |Z - P| ≤ (a + 2 * CE) * T ^ (1 - c) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hε : (0 : ℝ) < T ^ (-c) := Real.rpow_pos_of_pos hT0 _
  have hmul : T ^ (1 - c) * T ^ (-c) = T ^ (1 - 2 * c) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have p1 : T ^ (-c) * P ≤ a * T ^ (1 - c) := by
    have h := mul_le_mul_of_nonneg_left hP hε.le
    rw [show T ^ (-c) * (a * T) = a * (T ^ (-c) * T) by ring, rpow_neg_mul_base' hT0] at h
    exact h
  have p2 : E / T ^ (-c) ≤ CE * T ^ (1 - c) := by
    rw [div_le_iff₀ hε, show CE * T ^ (1 - c) * T ^ (-c) = CE * (T ^ (1 - c) * T ^ (-c)) by ring,
      hmul]
    exact hE
  have p3 : E ≤ CE * T ^ (1 - c) := by
    refine hE.trans (mul_le_mul_of_nonneg_left ?_ hCE)
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  linarith

/-- A three-step triangle inequality. -/
private theorem abs_sub_three' (A B C D : ℝ) : |A - D| ≤ |A - B| + |B - C| + |C - D| := by
  have h1 := abs_sub_le A B D
  have h2 := abs_sub_le B C D
  linarith

/-! ## The asymptotic mean square for every `σ > 1/2` -/

set_option maxHeartbeats 1000000 in
-- the proof is a long chain of `calc` estimates and needs more than the default budget
/-- **The Bohr–Landau asymptotic mean square of `ζ` on a vertical line with `1/2 < σ < 1`.**

`∫₀ᵀ ‖ζ(σ + i t)‖² dt = ζ(2σ) T + O_σ(T^(1-c))` for some `c = c(σ) > 0`; the constant `ζ(2σ)` is
written here as the sum of the Dirichlet series `∑_{n ≥ 1} n^(-2σ)`, which converges since
`2σ > 1` (see `ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta`). -/
theorem exists_integral_normSq_riemannZeta_asymptotic_half {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
          - (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))) * T| ≤ C * T ^ (1 - c) := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  have h1σ : (0 : ℝ) < 1 - σ := by linarith
  obtain ⟨m, ee, hm, hee1, heeL, heeU⟩ := exists_emOrder_meanSquareExponent h0 h1
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < σ + (m : ℝ) - 1 := by linarith
  have hee0 : (0 : ℝ) < ee := by linarith
  -- the four power savings
  set g1 : ℝ := 1 - ee * (2 - 2 * σ) with hg1def
  set g2 : ℝ := 2 * σ * ee with hg2def
  set g3 : ℝ := ee * (2 * (m : ℝ) + 2 * σ - 2) - 2 * (m : ℝ) with hg3def
  set g4 : ℝ := ee * (2 * σ - 1) with hg4def
  have hg1 : 0 < g1 := by
    rw [hg1def]
    nlinarith [(lt_div_iff₀ (by linarith : (0 : ℝ) < 2 - 2 * σ)).mp heeU]
  have hg2 : 0 < g2 := by rw [hg2def]; positivity
  have hg3 : 0 < g3 := by
    rw [hg3def]
    have h := (div_lt_iff₀ hden).mp heeL
    nlinarith
  have hg4 : 0 < g4 := by rw [hg4def]; nlinarith
  set cs : ℝ := min (min (g1 / 2) g2) (min g3 g4) with hcsdef
  have hcs : 0 < cs := by
    rw [hcsdef]
    exact lt_min (lt_min (by linarith) hg2) (lt_min hg3 hg4)
  have hcs1 : cs ≤ g1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcs2 : cs ≤ g2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcs3 : cs ≤ g3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcs4 : cs ≤ g4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set c : ℝ := cs / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  -- the constants
  obtain ⟨C₁, hC₁, hoff⟩ := offDiagSum_one_le h0 h1
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le h0 h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_one_add_log_le_rpow (γ := g1 / 2) (by linarith)
  obtain ⟨Cem, hCem, hembd⟩ := exists_norm_riemannZeta_sub_dirichletPoly_le_em m hm hs0 h1
  set K : ℝ := Real.pi / 2 / (1 - σ) ^ 2 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  set S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) with hSdef
  set CD : ℝ := 9 * ((3 + ee) * C₃) with hCDdef
  have hCD : 0 < CD := by rw [hCDdef]; positivity
  set CE : ℝ := 48 * K + 3 * Cem ^ 2 + 3 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 with hCEdef
  have hCE : 0 < CE := by rw [hCEdef]; positivity
  have hlast : (0 : ℝ) < 1 / (2 * σ - 1) := div_pos one_pos (by linarith)
  refine ⟨C₂ * (1 + CD) + 2 * CE + C₁ * CD + 1 / (2 * σ - 1), c,
    by nlinarith [mul_pos hC₂ (by linarith : (0:ℝ) < 1 + CD), mul_pos hC₁ hCD], hc, ?_⟩
  intro T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hmono : ∀ u v : ℝ, u ≤ v → T ^ (1 - v) ≤ T ^ (1 - u) := fun u v h =>
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  set x : ℝ := T ^ ee with hxdef
  have hpowT : ∀ r : ℝ, x ^ r = T ^ (ee * r) := fun r => by
    rw [hxdef]; exact (Real.rpow_mul hT0.le ee r).symm
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hT hee0.le
  have hx0 : (0 : ℝ) < x := by linarith
  have hTx : T ≤ x := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le hT hee1.le
  set N : ℕ := ⌈x⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNcast : (N : ℝ) = (⌈x⌉₊ : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  have hxN : x ≤ (N : ℝ) := by
    have h := Nat.le_ceil x
    rw [hNcast]; linarith
  have hNx : (N : ℝ) ≤ x + 2 := by
    have h := (Nat.ceil_lt_add_one hx0.le).le
    rw [hNcast]; linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNT : σ + T ≤ (N : ℝ) := by
    have h := Nat.le_ceil x
    rw [hNcast]; linarith
  have hN3x : (N : ℝ) ≤ 3 * x := by linarith
  have hN4x : (N : ℝ) + 1 ≤ 4 * x := by linarith
  -- the power estimates
  have hxa : x ^ (2 - 2 * σ) = T ^ (1 - g1) := by
    rw [hpowT]; congr 1; rw [hg1def]; ring
  have hB1 : (N : ℝ) ^ (2 - 2 * σ) ≤ 9 * T ^ (1 - g1) := by
    have h := rpow_le_sq_mul' (c := 3) (r := 2 - 2 * σ) (by norm_num) hx0 hN0.le hN3x
      (by linarith) (by linarith)
    rw [hxa] at h
    linarith [h]
  have hB2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 16 * T ^ (1 - g1) := by
    have h := rpow_le_sq_mul' (c := 4) (y := (N : ℝ) + 1) (r := 2 - 2 * σ) (by norm_num) hx0
      (by linarith) hN4x (by linarith) (by linarith)
    rw [hxa] at h
    linarith [h]
  have hB3 : (N : ℝ) ^ (-(2 * σ)) ≤ T ^ (-g2) := by
    calc (N : ℝ) ^ (-(2 * σ)) ≤ x ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
      _ = T ^ (-g2) := by rw [hpowT]; congr 1; rw [hg2def]; ring
  have hB4 : (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ T ^ (-(2 * (m : ℝ) + g3)) := by
    calc (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ x ^ (2 - 2 * σ - 2 * (m : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
      _ = T ^ (-(2 * (m : ℝ) + g3)) := by rw [hpowT]; congr 1; rw [hg3def]; ring
  have hB5 : (N : ℝ) ^ (1 - 2 * σ) ≤ T ^ (-g4) := by
    calc (N : ℝ) ^ (1 - 2 * σ) ≤ x ^ (1 - 2 * σ) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
      _ = T ^ (-g4) := by rw [hpowT]; congr 1; rw [hg4def]; ring
  have hB6 : 1 + Real.log N ≤ (3 + ee) * C₃ * T ^ (g1 / 2) := by
    have hlogx : Real.log x = ee * Real.log T := by rw [hxdef]; exact Real.log_rpow hT0 ee
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hlogN : Real.log N ≤ Real.log 3 + Real.log x := by
      have h : Real.log (N : ℝ) ≤ Real.log (3 * x) := Real.log_le_log hN0 hN3x
      rwa [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h
    have hL := hlog T hT
    have hexpand : (3 + ee) * (1 + Real.log T)
        = 3 + 3 * Real.log T + ee + ee * Real.log T := by ring
    calc 1 + Real.log N ≤ 3 + ee * Real.log T := by rw [hlogx] at hlogN; linarith
      _ ≤ (3 + ee) * (1 + Real.log T) := by linarith [hexpand, hlogT, hee0]
      _ ≤ (3 + ee) * (C₃ * T ^ (g1 / 2)) := mul_le_mul_of_nonneg_left hL (by linarith)
      _ = (3 + ee) * C₃ * T ^ (g1 / 2) := by ring
  -- the four estimates
  have hD1 : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ CD * T ^ (1 - cs) := by
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
    have hstep := prod_le_rpow_of_bounds' (T := T) (A := (N : ℝ) ^ (2 - 2 * σ))
      (L := 1 + Real.log N) (a := 9) (b := (3 + ee) * C₃) (g := g1) hT0
      (Real.rpow_nonneg hN0.le _) (by linarith) hB1 hB6
    rw [show (9 : ℝ) * ((3 + ee) * C₃) = CD from hCDdef.symm] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_left (hmono cs (g1 / 2) hcs1) hCD.le)
  have hD2 : (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ C₂ * (1 + CD) * T := by
    have hle : T ^ (1 - cs) ≤ T := by
      calc T ^ (1 - cs) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
        _ = T := Real.rpow_one T
    have h2 : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ CD * T :=
      hD1.trans (mul_le_mul_of_nonneg_left hle hCD.le)
    calc (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)) := hpoly N hN1 T hT0.le
      _ ≤ C₂ * (T + CD * T) := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
      _ = C₂ * (1 + CD) * T := by ring
  have hD3 : offDiagSum (fun _ => 1) N σ ≤ C₁ * CD * T ^ (1 - cs) := by
    calc offDiagSum (fun _ => 1) N σ ≤ C₁ * (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) :=
          hoff N hN1
      _ = C₁ * ((N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)) := by ring
      _ ≤ C₁ * (CD * T ^ (1 - cs)) := mul_le_mul_of_nonneg_left hD1 hC₁.le
      _ = C₁ * CD * T ^ (1 - cs) := by ring
  have hD4 : (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ CE * T ^ (1 - cs) := by
    have hmain := integral_normSq_error_em_le (m := m) (C := Cem) hs0 h1 hCem.le hembd hN1
      hT0.le hNT
    rw [← hKdef] at hmain
    -- the three error terms
    have t1 : 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * K) ≤ 48 * K * T ^ (1 - cs) := by
      have hb : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 16 * T ^ (1 - cs) :=
        le_trans hB2 (by linarith [hmono cs g1 (le_trans hcs1 (by linarith))])
      have hstep := mul_le_mul_of_nonneg_right hb hK0.le
      linarith [hstep]
    have t2 : 3 * Cem ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T ≤ 3 * Cem ^ 2 * T ^ (1 - cs) := by
      have h1' : (N : ℝ) ^ (-(2 * σ)) * T ≤ T ^ (-g2) * T :=
        mul_le_mul_of_nonneg_right hB3 hT0.le
      rw [rpow_neg_mul_base' hT0] at h1'
      have h := hmono cs g2 hcs2
      have hkey : (N : ℝ) ^ (-(2 * σ)) * T ≤ T ^ (1 - cs) := by linarith
      have hc0 : (0 : ℝ) ≤ 3 * Cem ^ 2 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hkey hc0
      linarith [hstep]
    have t3 : 3 * Cem ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T
        ≤ 3 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 - cs) := by
      have hbase : σ + T + (m : ℝ) ≤ (2 + (m : ℝ)) * T := by
        have hmT : (m : ℝ) ≤ (m : ℝ) * T := le_mul_of_one_le_right (by positivity) hT
        have hexpand : (2 + (m : ℝ)) * T = T + T + (m : ℝ) * T := by ring
        linarith
      have hb0 : (0 : ℝ) ≤ σ + T + (m : ℝ) := by positivity
      have hnum : ((σ + T + (m : ℝ)) ^ m) ^ 2 ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * (T ^ m) ^ 2 := by
        have hstep : (σ + T + (m : ℝ)) ^ m ≤ ((2 + (m : ℝ)) * T) ^ m :=
          pow_le_pow_left₀ hb0 hbase m
        have hexp : ((2 + (m : ℝ)) * T) ^ m = (2 + (m : ℝ)) ^ m * T ^ m := mul_pow _ _ m
        have h0' : (0 : ℝ) ≤ (σ + T + (m : ℝ)) ^ m := by positivity
        rw [← mul_pow, ← hexp]
        exact pow_le_pow_left₀ h0' hstep 2
      have hTm : (T ^ m) ^ 2 = T ^ (2 * (m : ℝ)) := by
        rw [← pow_mul, ← Real.rpow_natCast T (m * 2)]
        congr 1
        push_cast
        ring
      have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
      have hprod : ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) * T
          ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ) + g3)) * T := by
        have hstep1 : ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))
            ≤ (((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ))) * T ^ (-(2 * (m : ℝ) + g3)) := by
          refine mul_le_mul ?_ hB4 hNpow (by positivity)
          rw [hTm] at hnum
          exact hnum
        exact mul_le_mul_of_nonneg_right (by linarith [hstep1]) hT0.le
      have hcollapse : T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ) + g3)) * T = T ^ (1 - g3) := by
        rw [← Real.rpow_add hT0, show 2 * (m : ℝ) + -(2 * (m : ℝ) + g3) = -g3 by ring,
          rpow_neg_mul_base' hT0]
      have hle : T ^ (1 - g3) ≤ T ^ (1 - cs) := hmono cs g3 hcs3
      have hfin : ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) * T
          ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 - cs) := by
        calc ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) * T
            ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ) + g3)) * T :=
              hprod
          _ = ((2 + (m : ℝ)) ^ m) ^ 2 * (T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ) + g3)) * T) := by
              ring
          _ = ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 - g3) := by rw [hcollapse]
          _ ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 - cs) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
      have hc0 : (0 : ℝ) ≤ 3 * Cem ^ 2 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hfin hc0
      linarith [hstep]
    rw [hCEdef]
    linarith [hmain, t1, t2, t3]
  -- the tail of the Dirichlet series
  have hD5 : |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S| ≤ T ^ (-g4) / (2 * σ - 1) := by
    have h := abs_sum_Icc_rpow_neg_sub_tsum_le (q := 2 * σ) h2σ hN1
    have hd : (0 : ℝ) < 2 * σ - 1 := by linarith
    have hle : (N : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) ≤ T ^ (-g4) / (2 * σ - 1) := by
      have hmul := mul_le_mul_of_nonneg_right hB5 (le_of_lt (inv_pos.mpr hd))
      simpa [div_eq_mul_inv] using hmul
    rw [hSdef]
    linarith [h, hle]
  -- assembling
  have hcomp := abs_integral_normSq_riemannZeta_sub_dirichletPoly_le h1 N hT0.le
    (ε := T ^ (-c)) (Real.rpow_pos_of_pos hT0 _)
  have hdiag := abs_integral_normSq_dirichletPoly_sub_diag_le (fun _ => 1) N σ T
  have hone : (∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
      = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (-2 * σ : ℝ) = -(2 * σ) by ring]
    simp
  rw [hone] at hdiag
  have hE3 : T ^ (1 - cs) ≤ T ^ (1 - c) := hmono c cs (by rw [hcdef]; linarith)
  have hstep1 : |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      - ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|
      ≤ (C₂ * (1 + CD) + 2 * CE) * T ^ (1 - c) := by
    refine comparison_bound' hT hc hCE.le hcomp hD2 ?_
    rw [show (1 : ℝ) - 2 * c = 1 - cs by rw [hcdef]; ring]
    exact hD4
  have hstep2 : |(∫ t in (0 : ℝ)..T,
      ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      - T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)))| ≤ C₁ * CD * T ^ (1 - c) := by
    refine hdiag.trans (hD3.trans ?_)
    exact mul_le_mul_of_nonneg_left hE3 (by positivity)
  have hstep3 : |T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S * T|
      ≤ 1 / (2 * σ - 1) * T ^ (1 - c) := by
    have heq : T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S * T
        = T * ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S) := by ring
    rw [heq, abs_mul, abs_of_pos hT0]
    have hstep : T * |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S|
        ≤ T * (T ^ (-g4) / (2 * σ - 1)) := mul_le_mul_of_nonneg_left hD5 hT0.le
    refine hstep.trans ?_
    have hTg4 : T ^ (-g4) * T = T ^ (1 - g4) := rpow_neg_mul_base' hT0 g4
    have hle : T ^ (1 - g4) ≤ T ^ (1 - c) := hmono c g4 (by rw [hcdef]; linarith)
    have heq2 : T * (T ^ (-g4) / (2 * σ - 1)) = T ^ (1 - g4) / (2 * σ - 1) := by
      rw [← hTg4]; ring
    have hd : (0 : ℝ) < 2 * σ - 1 := by linarith
    rw [heq2, div_le_iff₀ hd]
    have hfin : 1 / (2 * σ - 1) * T ^ (1 - c) * (2 * σ - 1) = T ^ (1 - c) := by
      field_simp
    rw [hfin]
    exact hle
  have htri := abs_sub_three' (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)))) (S * T)
  linarith [htri, hstep1, hstep2, hstep3]

/-- **The Bohr–Landau mean square in limit form**: for `1/2 < σ < 1`,
`(1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt → ζ(2σ)` as `T → ∞`.  The limit is written as the real series
`∑ (n+1)^(-2σ)`, which `ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta` identifies with
`ζ(2σ)`. -/
theorem tendsto_integral_normSq_riemannZeta_div_half {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
      Filter.atTop (nhds (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := exists_integral_normSq_riemannZeta_asymptotic_half h0 h1
  set S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) with hS
  refine tendsto_sub_nhds_zero_iff.mp ?_
  have hbound : ∀ᶠ T : ℝ in Filter.atTop,
      ‖(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T - S‖
        ≤ C * T ^ (-c) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := by linarith
    set J : ℝ := ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hJ
    have hsplit : J / T - S = (J - S * T) / T := by field_simp
    have hTc : T ^ (1 - c) = T * T ^ (-c) := by
      rw [show (1 : ℝ) - c = 1 + -c by ring, Real.rpow_add hT0, Real.rpow_one]
    rw [Real.norm_eq_abs, hsplit, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
    calc |J - S * T| ≤ C * T ^ (1 - c) := hbd T hT
      _ = C * T ^ (-c) * T := by rw [hTc]; ring
  refine squeeze_zero_norm' hbound ?_
  simpa using (tendsto_rpow_neg_atTop hc).const_mul C

end RiemannHypothesis
