/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquare

/-!
# The trapezoidal Euler–Maclaurin correction and the mean square of `ζ` for `σ > 3/5`

`RiemannHypothesis.StripMeanSquare` proves `∫₀ᵀ ‖ζ(σ + i t)‖² dt = O_σ(T)` for `2/3 < σ < 1`.
The exponent `2/3` is the balance point of the *zeroth order* Euler–Maclaurin expansion, whose
tail is `O(‖s‖ N^(-σ))`.  This file adds the *first order* (trapezoidal) correction:

`ζ(s) = ∑_{n ≤ N} n^(-s) + (N+1)^(1-s)/(s-1) + (N+1)^(-s)/2 + ∑_{n ≥ N} trapTerm n s`,

where `trapTerm n s` is the error of the trapezoid rule for `x ↦ x^(-s)` on `[n+1, n+2]`.
Because the trapezoid rule is exact on affine functions, `trapTerm` is controlled by the second
derivative of `x ↦ x^(-s)`:

`‖trapTerm n s‖ ≤ (1/8) ‖s‖ ‖s+1‖ (n+1)^(-(2 + re s))`,

so the tail is `O(‖s‖² N^(-1-σ))` instead of `O(‖s‖ N^(-σ))`.  One power of `N` is gained, the
Dirichlet polynomial may be taken of length `N ≍ T^(2/(1+σ))` instead of `T^(1/σ)`, and the
balance `(2/(1+σ)) (2 - 2σ) < 1` becomes `σ > 3/5`.

## Main results

* `trapTerm` : the trapezoidal Euler–Maclaurin term.
* `trapTerm_eq_integral` : `trapTerm n s = -∫ P(x) s (s+1) x^(-s-2) dx` over `[n+1, n+2]`, where
  `P(x) = ((x - n - 1)² - (x - n - 1))/2` is the Green's function of the trapezoid rule.
* `norm_trapTerm_le` : `‖trapTerm n s‖ ≤ (1/8) ‖s‖ ‖s+1‖ (n+1)^(-(2 + re s))`.
* `norm_riemannZeta_sub_dirichletPoly_le_trap` : the trapezoidal Euler–Maclaurin bound for `ζ`
  minus the truncated zeta sum on a vertical line inside the strip.
* `exists_integral_normSq_riemannZeta_le_three_fifths` : **the mean square bound**
  `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C_σ T` for `3/5 < σ < 1` and `T ≥ 1`.
* `exists_integral_norm_riemannZeta_le_three_fifths`,
  `exists_volume_norm_riemannZeta_ge_le_three_fifths` : the first moment and the large values
  estimate in the same range.

The classical theorem of Bohr and Landau gives the same bounds for every `σ > 1/2`; `k`
Bernoulli terms give `σ > (k+2)/(2k+3)`, and what is formalized here is the case `k = 1`.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace RiemannHypothesis

/-! ## The trapezoidal term and its size -/

/-- The Green's function of the trapezoid rule on `[a, a+1]`: `P a z = ((z - a)² - (z - a))/2`,
which vanishes at both endpoints and has `P'' = 1`. -/
def trapGreen (a : ℝ) (z : ℂ) : ℂ := ((z - (a : ℂ)) ^ 2 - (z - (a : ℂ))) / 2

/-- The primitive used in the integration by parts behind `trapTerm_eq_integral`:
`H = P f' - (x - a - 1/2) f` for `f x = x^(-s)`, so that `H' = P f'' - f`. -/
def trapPrimitive (a : ℝ) (s : ℂ) (z : ℂ) : ℂ :=
  trapGreen a z * (-s * z ^ (-s - 1)) - (z - (a : ℂ) - 1 / 2) * z ^ (-s)

/-- **The trapezoidal Euler–Maclaurin term**: the error of the trapezoid rule for `x ↦ x^(-s)`
on `[n+1, n+2]`, that is `(f(n+1) + f(n+2))/2 - ∫ f`. -/
def trapTerm (n : ℕ) (s : ℂ) : ℂ :=
  eulerTerm n s - (((n + 1 : ℝ) : ℂ) ^ (-s) - ((n + 2 : ℝ) : ℂ) ^ (-s)) / 2

/-- The derivative of the primitive: `H' = P f'' - f`. -/
theorem hasDerivAt_trapPrimitive (a : ℝ) {s : ℂ} (hs0 : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => trapPrimitive a s (y : ℂ))
      (trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)) - (x : ℂ) ^ (-s)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsne : -s ≠ 0 := by
    simp only [neg_ne_zero]; intro h; rw [h] at hs0; simp at hs0
  have hs1ne : -s - 1 ≠ 0 := by
    intro h
    have hre' : (-s - 1).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at hre'
    linarith
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1))
      ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x := hasDerivAt_ofReal_cpow_const hxne hs1ne
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const hxne hsne
  have hre : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 x := by
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 : ℂ)) ((1 : ℂ) * (x : ℂ) ^ ((1 : ℂ) - 1)) x :=
      hasDerivAt_ofReal_cpow_const hxne one_ne_zero
    simpa using h0
  have hb : HasDerivAt (fun y : ℝ => (y : ℂ) - (a : ℂ)) 1 x := hre.sub_const _
  have hG : HasDerivAt (fun y : ℝ => trapGreen a (y : ℂ)) ((x : ℂ) - (a : ℂ) - 1 / 2) x :=
    (((hb.pow 2).sub hb).div_const 2).congr_deriv (by simp; ring)
  have hQ : HasDerivAt (fun y : ℝ => (y : ℂ) - (a : ℂ) - 1 / 2) 1 x := hb.sub_const _
  have hmain := (hG.mul (h1.const_mul (-s))).sub (hQ.mul h2)
  have hpow : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  exact hmain.congr_deriv (by rw [hpow]; ring)

/-- The integrand of the trapezoid remainder is continuous on `[a, a+1]` for `0 < a`. -/
theorem continuousOn_trapIntegrand (a : ℝ) (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    ContinuousOn (fun x : ℝ =>
        trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)) - (x : ℂ) ^ (-s))
      (Set.uIcc a (a + 1)) := by
  have hab : a ≤ a + 1 := by linarith
  have hsne : -s ≠ 0 := by
    simp only [neg_ne_zero]; intro h; rw [h] at hs0; simp at hs0
  have hs2ne : -s - 2 ≠ 0 := by
    intro h
    have hre' : (-s - 2).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re] at hre'
    norm_num at hre'
    linarith
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have c1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-s - 2)) x :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hs2ne).continuousAt
  have c2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-s)) x :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hsne).continuousAt
  have c3 : ContinuousAt (fun y : ℝ => trapGreen a (y : ℂ)) x := by
    unfold trapGreen
    fun_prop
  exact ((c3.mul (c1.const_mul _)).sub c2).continuousWithinAt

/-- The integration by parts identity: `(f(a) + f(a+1))/2 - ∫ f = -∫ P f''`. -/
theorem integral_trapIntegrand (a : ℝ) (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    (∫ x in a..(a + 1), (trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))
        - (x : ℂ) ^ (-s)))
      = -(((a : ℝ) : ℂ) ^ (-s) + ((a + 1 : ℝ) : ℂ) ^ (-s)) / 2 := by
  have hab : a ≤ a + 1 := by linarith
  have hpos : ∀ x ∈ Set.uIcc a (a + 1), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => trapPrimitive a s (y : ℂ))
        (trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)) - (x : ℂ) ^ (-s)) x :=
    fun x hx => hasDerivAt_trapPrimitive a hs0 (hpos x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_trapIntegrand a ha hs0).intervalIntegrable]
  unfold trapPrimitive trapGreen
  push_cast
  ring_nf

/-- `x ↦ x^(-s)` is interval integrable on `[a, a+1]` for `0 < a` and `0 < re s`. -/
theorem intervalIntegrable_cpow_neg {a : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a (a + 1) := by
  have hab : a ≤ a + 1 := by linarith
  have hsne : -s ≠ 0 := by
    simp only [neg_ne_zero]; intro h; rw [h] at hs0; simp at hs0
  refine (ContinuousOn.intervalIntegrable ?_)
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  exact ((hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hsne).continuousAt).continuousWithinAt

/-- **The trapezoid remainder in integral form**: `trapTerm n s = -∫ P f''`. -/
theorem trapTerm_eq_integral (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    trapTerm n s = -∫ x in ((n : ℝ) + 1)..((n : ℝ) + 1 + 1),
      trapGreen ((n : ℝ) + 1) (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a + 1 = (n : ℝ) + 2 := by rw [ha]; ring
  have hF : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a (a + 1) :=
    intervalIntegrable_cpow_neg ha0 hs0
  have hG : IntervalIntegrable (fun x : ℝ =>
      trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) volume a (a + 1) := by
    have hdiff := (continuousOn_trapIntegrand a ha0 hs0).intervalIntegrable (μ := volume)
    have heq : (fun x : ℝ => trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2)))
        = (fun x : ℝ => (trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))
            - (x : ℂ) ^ (-s)) + (x : ℂ) ^ (-s)) := by funext x; ring
    rw [heq]
    exact hdiff.add hF
  have hconst : IntervalIntegrable (fun _ : ℝ => ((a : ℝ) : ℂ) ^ (-s)) volume a (a + 1) :=
    intervalIntegrable_const (μ := volume)
  have heuler : eulerTerm n s = ((a : ℂ) ^ (-s)) - ∫ x in a..(a + 1), (x : ℂ) ^ (-s) := by
    rw [eulerTerm_eq_integral n hs1, ← ha2]
    rw [intervalIntegral.integral_sub hconst hF]
    simp [ha]
  have hsplit := intervalIntegral.integral_sub hG hF
  have hkey := integral_trapIntegrand a ha0 hs0
  rw [hsplit] at hkey
  unfold trapTerm
  rw [heuler, ← ha2]
  linear_combination hkey

/-- The Green's function of the trapezoid rule is bounded by `1/8`. -/
theorem norm_trapGreen_le {a x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ a + 1) :
    ‖trapGreen a (x : ℂ)‖ ≤ 1 / 8 := by
  have hcast : (x : ℂ) - (a : ℂ) = ((x - a : ℝ) : ℂ) := by push_cast; ring
  have hre : trapGreen a (x : ℂ) = (((((x - a) ^ 2 - (x - a)) / 2 : ℝ)) : ℂ) := by
    unfold trapGreen
    rw [hcast]
    push_cast
    ring
  rw [hre, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ x - a := by linarith
  have h1 : x - a ≤ 1 := by linarith
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    div_le_div_iff₀ (by norm_num) (by norm_num)]
  have habs : |(x - a) ^ 2 - (x - a)| = (x - a) - (x - a) ^ 2 := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  rw [habs]
  nlinarith [sq_nonneg (x - a - 1 / 2)]

/-- **The size of the trapezoidal term**: `‖trapTerm n s‖ ≤ ‖s‖ ‖s+1‖ (n+1)^(-(2+σ))/8`. -/
theorem norm_trapTerm_le (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖trapTerm n s‖ ≤ 1 / 8 * ‖s‖ * ‖s + 1‖ * ((n : ℝ) + 1) ^ (-(2 + s.re)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  rw [trapTerm_eq_integral n hs0 hs1, norm_neg]
  have hbd : ∀ x ∈ Set.uIoc a (a + 1),
      ‖trapGreen a (x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))‖
        ≤ 1 / 8 * ‖s‖ * ‖s + 1‖ * a ^ (-(2 + s.re)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_trans ha0 hx1
    have hnorm : ‖(x : ℂ) ^ (-s - 2)‖ = x ^ (-(2 + s.re)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp [Complex.sub_re, Complex.neg_re]
      ring
    have hpow : x ^ (-(2 + s.re)) ≤ a ^ (-(2 + s.re)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hx1.le (by linarith)
    have hG := norm_trapGreen_le (a := a) hx1.le hx2
    rw [norm_mul, norm_mul, norm_mul, hnorm]
    have h1 : 0 ≤ ‖s‖ * ‖s + 1‖ := by positivity
    calc ‖trapGreen a (x : ℂ)‖ * (‖s‖ * ‖s + 1‖ * x ^ (-(2 + s.re)))
        ≤ (1 / 8) * (‖s‖ * ‖s + 1‖ * a ^ (-(2 + s.re))) := by
          refine mul_le_mul hG ?_ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hpow h1
      _ = 1 / 8 * ‖s‖ * ‖s + 1‖ * a ^ (-(2 + s.re)) := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-! ## The trapezoidal representation of `ζ` -/

/-- The tail of the trapezoidal terms is summable. -/
theorem summable_trapTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    Summable (fun n : ℕ => trapTerm (n + N) s) := by
  have hsum : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re))) :=
    (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (p := 2 + s.re) (by linarith))
  exact Summable.of_norm_bounded (hsum.mul_left (1 / 8 * ‖s‖ * ‖s + 1‖))
    fun n => norm_trapTerm_le (n + N) hs0 hs1

/-- `(m + N + 1)^(-s) → 0` for `0 < re s`. -/
theorem tendsto_cpow_shift_zero {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) :
    Filter.Tendsto (fun m : ℕ => ((((m + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm (a := fun m : ℕ => ((m : ℝ) + 1) ^ (-s.re)) (fun m => ?_) ?_
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hbase : ((m : ℝ) + 1) ≤ (((m + N : ℕ) : ℝ) + 1) := by
      have hm : (m : ℝ) ≤ ((m + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right m N
      linarith
    have hstep : (((m + N : ℕ) : ℝ) + 1) ^ (-s).re ≤ ((m : ℝ) + 1) ^ (-s).re := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) hbase ?_
      simp only [Complex.neg_re]
      linarith
    simpa using hstep
  · have h1 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hs0).comp h1

/-- The telescoping sum of the trapezoidal corrections. -/
theorem tsum_cpow_telescope {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    ∑' n : ℕ, (((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
        - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s))
      = (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  set g : ℕ → ℂ := fun m => ((((m + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hg
  have hterm : ∀ n : ℕ, ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
      - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s) = g n - g (n + 1) := by
    intro n
    have hcast : (((n + 1 + N : ℕ) : ℝ) + 1 : ℝ) = (((n + N : ℕ) : ℝ) + 2 : ℝ) := by
      push_cast
      ring
    rw [hg]
    simp only
    rw [hcast]
  have hsummable : Summable (fun n : ℕ => g n - g (n + 1)) := by
    have heuler : Summable (fun n : ℕ => eulerTerm (n + N) s) :=
      (summable_nat_add_iff N).2 (summable_eulerTerm hs0 hs1)
    have htrap : Summable (fun n : ℕ => trapTerm (n + N) s) := summable_trapTerm hs0 hs1 N
    have hdiff := (heuler.sub htrap).mul_left 2
    refine hdiff.congr fun n => ?_
    rw [← hterm n]
    unfold trapTerm
    push_cast
    ring
  have hzero : Filter.Tendsto g Filter.atTop (nhds 0) := tendsto_cpow_shift_zero hs0 N
  have hpartial : ∀ m : ℕ, ∑ i ∈ Finset.range m, (g i - g (i + 1)) = g 0 - g m :=
    fun m => Finset.sum_range_sub' g m
  have hlim : Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (g i - g (i + 1)))
      Filter.atTop (nhds (g 0)) := by
    have := (tendsto_const_nhds (x := g 0) (f := Filter.atTop (α := ℕ))).sub hzero
    simpa [hpartial] using this
  have hsum : HasSum (fun n : ℕ => g n - g (n + 1)) (g 0) :=
    (hsummable.hasSum_iff_tendsto_nat).2 hlim
  have := hsum.tsum_eq
  rw [tsum_congr hterm, this, hg]
  simp

/-- The Euler–Maclaurin tail, split into its trapezoidal correction and remainder. -/
theorem tsum_eulerTerm_eq_trapTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    ∑' n : ℕ, eulerTerm (n + N) s
      = (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) / 2 + ∑' n : ℕ, trapTerm (n + N) s := by
  have htrap : Summable (fun n : ℕ => trapTerm (n + N) s) := summable_trapTerm hs0 hs1 N
  have heuler : Summable (fun n : ℕ => eulerTerm (n + N) s) :=
    (summable_nat_add_iff N).2 (summable_eulerTerm hs0 hs1)
  have hhalf : Summable (fun n : ℕ => (((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
      - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) / 2) := by
    refine (heuler.sub htrap).congr fun n => ?_
    unfold trapTerm
    push_cast
    ring
  have hsplit : ∀ n : ℕ, eulerTerm (n + N) s
      = (((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
          - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) / 2 + trapTerm (n + N) s := by
    intro n
    unfold trapTerm
    push_cast
    ring
  rw [tsum_congr hsplit, hhalf.tsum_add htrap, tsum_div_const,
    tsum_cpow_telescope hs0 hs1 N]

/-- **The trapezoidal Euler–Maclaurin representation of `ζ`** on the punctured right
half-plane. -/
theorem riemannZeta_eq_trapApprox (N : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
        + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2
        + ∑' n : ℕ, trapTerm (n + N) s := by
  rw [riemannZeta_eq_zetaApprox_of_pos_re N hs0 hs1, zetaApprox,
    tsum_eulerTerm_eq_trapTerm hs0 hs1 N]
  push_cast
  ring

/-! ## The Euler–Maclaurin error, with the trapezoidal correction -/

/-- **The trapezoidal Euler–Maclaurin bound** for the difference between `ζ` and the truncated
zeta sum on a vertical line inside the strip.  Compared with
`norm_riemannZeta_sub_dirichletPoly_le` the last term is `O(‖s‖² N^(-1-σ))` in place of
`O(‖s‖ N^(-σ))`. -/
theorem norm_riemannZeta_sub_dirichletPoly_le_trap {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
        + ((N : ℝ) + 1) ^ (-σ) / 2
        + (σ + |t|) * (1 + σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [riemannZeta_eq_trapApprox N hs0 hs1, ← dirichletPoly_one N s]
  have hsplit : dirichletPoly (fun _ => 1) N s + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + (∑' n : ℕ, trapTerm (n + N) s)
      - dirichletPoly (fun _ => 1) N s
      = (((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2)
        + ∑' n : ℕ, trapTerm (n + N) s := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  · -- the trapezoidal tail
    have hbd : ∀ n : ℕ, ‖trapTerm (n + N) s‖
        ≤ 1 / 8 * ‖s‖ * ‖s + 1‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re)) :=
      fun n => norm_trapTerm_le (n + N) hs0 hs1
    have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by rw [hre]; linarith))
    have hsummable := hsh.mul_left (1 / 8 * ‖s‖ * ‖s + 1‖)
    have hnorms : Summable (fun n : ℕ => ‖trapTerm (n + N) s‖) :=
      hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
    have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re))
        ≤ (N : ℝ) ^ (1 - (2 + s.re)) / ((2 + s.re) - 1) :=
      tsum_shift_rpow_neg_le_rpow (by rw [hre]; linarith) hN
    have hnorm_s : ‖s‖ ≤ σ + |t| := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [hre, him, abs_of_pos h0] at h
      exact h
    have hnorm_s1 : ‖s + 1‖ ≤ 1 + σ + |t| := by
      have h := Complex.norm_le_abs_re_add_abs_im (s + 1)
      have hre1 : (s + 1).re = σ + 1 := by rw [Complex.add_re, hre]; simp
      have him1 : (s + 1).im = t := by rw [Complex.add_im, him]; simp
      rw [hre1, him1, abs_of_pos (by linarith)] at h
      linarith
    have hpos : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re)) :=
      tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
    have hprod : 1 / 8 * ‖s‖ * ‖s + 1‖ ≤ 1 / 8 * (σ + |t|) * (1 + σ + |t|) := by
      have hs00 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
      have hs10 : (0 : ℝ) ≤ ‖s + 1‖ := norm_nonneg _
      have h1' : (0 : ℝ) ≤ σ + |t| := by positivity
      nlinarith
    calc ‖∑' n : ℕ, trapTerm (n + N) s‖
        ≤ ∑' n : ℕ, ‖trapTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, 1 / 8 * ‖s‖ * ‖s + 1‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re)) :=
          hnorms.tsum_le_tsum hbd hsummable
      _ = 1 / 8 * ‖s‖ * ‖s + 1‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(2 + s.re)) :=
          tsum_mul_left
      _ ≤ 1 / 8 * (σ + |t|) * (1 + σ + |t|)
            * ((N : ℝ) ^ (1 - (2 + s.re)) / ((2 + s.re) - 1)) := by
          refine mul_le_mul hprod htail hpos (by positivity)
      _ = (σ + |t|) * (1 + σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ)) := by
          rw [hre, show (1 : ℝ) - (2 + σ) = -(1 + σ) by ring, show (2 + σ) - 1 = 1 + σ by ring]
          field_simp

/-! ## The mean square of `ζ` for `σ > 3/5` -/

/-- The pointwise bound behind the mean square estimate, with the trapezoidal error term. -/
theorem normSq_riemannZeta_le_pointwise_trap {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 4 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 4 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)))
        + 1
        + 4 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set P : ℂ := dirichletPoly (fun _ => 1) N s with hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    simp [Complex.normSq_apply]
    ring
  have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
    have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
    nlinarith [norm_nonneg (s - 1), hnormsq]
  have hbd := norm_riemannZeta_sub_dirichletPoly_le_trap h0 h1 hN t
  set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
  set E2 : ℝ := ((N : ℝ) + 1) ^ (-σ) / 2 with hE2
  set E3 : ℝ := (σ + |t|) * (1 + σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ)) with hE3
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
  have hE30 : 0 ≤ E3 := by rw [hE3]; positivity
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + E1 + E2 + E3 := by
    have := norm_sub_norm_le (riemannZeta s) P
    linarith [hbd]
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ 4 * (‖P‖ ^ 2 + E1 ^ 2 + E2 ^ 2 + E3 ^ 2) := by
    nlinarith [norm_nonneg (riemannZeta s), norm_nonneg P, hE10, hE20, hE30, htri,
      sq_nonneg (‖P‖ - E1), sq_nonneg (‖P‖ - E2), sq_nonneg (‖P‖ - E3), sq_nonneg (E1 - E2),
      sq_nonneg (E1 - E3), sq_nonneg (E2 - E3)]
  have hE1sq : E1 ^ 2 = ((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    rw [hE1, div_pow, hnormsq, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hE2sq : E2 ^ 2 ≤ 1 / 4 := by
    rw [hE2, div_pow]
    have hle : ((N : ℝ) + 1) ^ (-σ) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := (N : ℝ) + 1) (by norm_num)
        (by linarith) (by linarith : -σ ≤ 0)
      simpa using this
    have h0' : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    nlinarith
  have hE3sq : E3 ^ 2
      ≤ (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2) := by
    have hpow : ((N : ℝ) ^ (-(1 + σ))) ^ 2 = (N : ℝ) ^ (-(2 + 2 * σ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 + σ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have habs : |t| = t := abs_of_nonneg ht0
    have hC : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 + σ)) := Real.rpow_nonneg hN0.le _
    have hA : (0 : ℝ) ≤ σ + t := by linarith
    have hB : (0 : ℝ) ≤ 1 + σ + t := by linarith
    have hAT : σ + t ≤ σ + T := by linarith
    have hBT : 1 + σ + t ≤ 1 + σ + T := by linarith
    rw [hE3, habs]
    calc ((σ + t) * (1 + σ + t) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ))) ^ 2
        = (σ + t) ^ 2 * (1 + σ + t) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / (64 * (1 + σ) ^ 2) := by
          rw [div_pow]
          ring_nf
      _ ≤ (σ + T) ^ 2 * (1 + σ + T) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / (64 * (1 + σ) ^ 2) := by
          gcongr
      _ = (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2) := by
          rw [hpow]
  linarith [hsq, hE1sq, hE2sq, hE3sq]

/-- The mean square of `ζ` on `[0, T]`, in terms of the length `N` of the Dirichlet polynomial,
with the trapezoidal error term. -/
theorem integral_normSq_riemannZeta_le_aux_trap {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 4 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 4 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2)
        + T
        + 4 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ))
            / (64 * (1 + σ) ^ 2)) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set B : ℝ := (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2)
    with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hzetaC := continuous_normSq_riemannZeta_line_of_lt_one (σ := σ) h1
  have hPC := continuous_normSq_dirichletPoly_line (σ := σ) N
  have hcont1 : Continuous (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    have hs : (0 : ℝ) < 1 - σ := by linarith
    exact ne_of_gt (by nlinarith [sq_nonneg t])
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 4 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    ((hPC.const_smul (4 : ℝ)).congr fun t => by simp [smul_eq_mul]).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t : ℝ => 4 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) volume 0 T :=
    (by fun_prop : Continuous
      (fun t : ℝ => 4 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))))).intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T := intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun _ : ℝ => 4 * B) volume 0 T := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hzetaC.intervalIntegrable 0 T)
    (((hi1.add hi2).add hi3).add hi4)
    (fun t ht => normSq_riemannZeta_le_pointwise_trap h0 h1 hN ht.1 ht.2)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  have hφ : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero, mul_one]
  nlinarith [hφ, hA0]

/-- The trapezoidal error factor is bounded by `1` once `x ≤ T⁻⁴`; this is the choice
`N ≍ T^(2/(1+σ))`, for which `N^(-(2+2σ)) ≤ T^(-4)`. -/
private lemma trap_error_factor_le {σ T x : ℝ} (hs0 : 0 < σ) (h1 : σ < 1) (hT : 1 ≤ T)
    (hx0 : 0 ≤ x) (hx : x ≤ (T ^ 4)⁻¹) :
    (σ + T) ^ 2 * (1 + σ + T) ^ 2 * x / (64 * (1 + σ) ^ 2) ≤ 1 := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have hnum : (σ + T) ^ 2 * (1 + σ + T) ^ 2 ≤ 36 * T ^ 4 := by
    have hle1 : σ + T ≤ 2 * T := by linarith
    have hle2 : 1 + σ + T ≤ 3 * T := by linarith
    have hsq1 : (σ + T) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
    have hsq2 : (1 + σ + T) ^ 2 ≤ 9 * T ^ 2 := by nlinarith
    calc (σ + T) ^ 2 * (1 + σ + T) ^ 2 ≤ (4 * T ^ 2) * (9 * T ^ 2) :=
          mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
      _ = 36 * T ^ 4 := by ring
  have hstep : (σ + T) ^ 2 * (1 + σ + T) ^ 2 * x ≤ 36 * T ^ 4 * (T ^ 4)⁻¹ :=
    mul_le_mul hnum hx hx0 (by positivity)
  have heq : 36 * T ^ 4 * (T ^ 4)⁻¹ = 36 := by field_simp
  rw [heq] at hstep
  rw [div_le_one (by positivity)]
  nlinarith

/-! ## The mean square of `ζ` for `3/5 < σ < 1` -/

/-- **The mean square of `ζ` on a vertical line with `3/5 < σ < 1` is `O(T)`.**

This improves `exists_integral_normSq_riemannZeta_le`, which requires `2/3 < σ`.  The gain comes
from the trapezoidal Euler–Maclaurin correction: the tail of the expansion is `O(‖s‖² N^(-1-σ))`
instead of `O(‖s‖ N^(-σ))`, so the Dirichlet polynomial may be taken of length `N ≍ T^(2/(1+σ))`
and the balance condition `(2/(1+σ)) (2 - 2σ) < 1` reads `σ > 3/5`. -/
theorem exists_integral_normSq_riemannZeta_le_three_fifths {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have h1s : (0 : ℝ) < 1 - σ := by linarith
  have hσ1 : (0 : ℝ) < 1 + σ := by linarith
  have ha1 : (4 - 4 * σ) / (1 + σ) < 1 := by rw [div_lt_one hσ1]; linarith
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le (by linarith) h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  have hC₄ : (0 : ℝ) < Real.pi / 2 / (1 - σ) ^ 2 := div_pos (by positivity) (pow_pos h1s 2)
  refine ⟨4 * C₂ * (1 + 8 * C₃) + 36 * (Real.pi / 2 / (1 - σ) ^ 2) + 5, by nlinarith,
    fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hx1 : (1 : ℝ) ≤ T ^ (2 / (1 + σ)) := Real.one_le_rpow hT (by positivity)
  have hx0 : (0 : ℝ) < T ^ (2 / (1 + σ)) := by linarith
  obtain ⟨N, hN1, hxN, hNx⟩ : ∃ N : ℕ, 1 ≤ N ∧ T ^ (2 / (1 + σ)) ≤ (N : ℝ) ∧
      (N : ℝ) ≤ T ^ (2 / (1 + σ)) + 1 := by
    refine ⟨⌈T ^ (2 / (1 + σ))⌉₊, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one hx0.le).le⟩
    have h := le_trans hx1 (Nat.le_ceil (T ^ (2 / (1 + σ))))
    exact_mod_cast h
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- the two exponent identities
  have hxa : (T ^ (2 / (1 + σ))) ^ (2 - 2 * σ) = T ^ ((4 - 4 * σ) / (1 + σ)) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    field_simp
    ring
  have hxd : (T ^ (2 / (1 + σ))) ^ (-(2 + 2 * σ)) = (T ^ 4)⁻¹ := by
    rw [← Real.rpow_mul hT0.le, show 2 / (1 + σ) * -(2 + 2 * σ) = -(4 : ℝ) by
      field_simp; ring, Real.rpow_neg hT0.le]
    norm_num
  have hTa0 : (0 : ℝ) ≤ T ^ ((4 - 4 * σ) / (1 + σ)) := Real.rpow_nonneg hT0.le _
  have hTa : T ^ ((4 - 4 * σ) / (1 + σ)) ≤ T := by
    calc T ^ ((4 - 4 * σ) / (1 + σ)) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha1.le
      _ = T := Real.rpow_one T
  -- the length of the Dirichlet polynomial
  have hNa : (N : ℝ) ^ (2 - 2 * σ) ≤ 4 * T ^ ((4 - 4 * σ) / (1 + σ)) := by
    have h2 : (N : ℝ) ^ (2 - 2 * σ) ≤ (2 * T ^ (2 / (1 + σ))) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (2 : ℝ) ^ (2 - 2 * σ) ≤ 4 := by
      calc (2 : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    nlinarith
  have hNa' : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 9 * T := by
    have h2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ (3 * T ^ (2 / (1 + σ))) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (3 : ℝ) ^ (2 - 2 * σ) ≤ 9 := by
      calc (3 : ℝ) ^ (2 - 2 * σ) ≤ (3 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9 := by norm_num
    nlinarith
  have hNlog : Real.log N ≤ 1 + 2 * Real.log T := by
    have hle : Real.log N ≤ Real.log (2 * T ^ (2 / (1 + σ))) :=
      Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), Real.log_rpow hT0] at hle
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hinv : 2 / (1 + σ) ≤ 2 := by
      rw [div_le_iff₀ hσ1]; linarith
    nlinarith
  have hNneg : (N : ℝ) ^ (-(2 + 2 * σ)) ≤ (T ^ 4)⁻¹ := by
    have h2 : (N : ℝ) ^ (-(2 + 2 * σ)) ≤ (T ^ (2 / (1 + σ))) ^ (-(2 + 2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
    rwa [hxd] at h2
  -- the four contributions
  have hprod : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ 8 * (C₃ * T) := by
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
    have hNpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)
        ≤ 4 * T ^ ((4 - 4 * σ) / (1 + σ)) * (2 * (1 + Real.log T)) :=
          mul_le_mul hNa (by linarith) (by linarith) (by linarith)
      _ = 8 * (T ^ ((4 - 4 * σ) / (1 + σ)) * (1 + Real.log T)) := by ring
      _ ≤ 8 * (C₃ * T) := by linarith [hlog T hT]
  have hb1 : 4 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 4 * C₂ * (1 + 8 * C₃) * T := by
    calc 4 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 4 * (C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N))) := by
          linarith [hpoly N hN1 T hT0.le]
      _ ≤ 4 * (C₂ * (T + 8 * (C₃ * T))) := by
          linarith only [mul_le_mul_of_nonneg_left hprod hC₂.le]
      _ = 4 * C₂ * (1 + 8 * C₃) * T := by ring
  have hb2 : 4 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * (Real.pi / 2 / (1 - σ) ^ 2)
      ≤ 36 * (Real.pi / 2 / (1 - σ) ^ 2) * T := by
    linarith only [mul_le_mul_of_nonneg_right hNa' hC₄.le]
  have hb3 : 4 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ))
      / (64 * (1 + σ) ^ 2)) * T ≤ 4 * T := by
    have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 + 2 * σ)) := Real.rpow_nonneg hN0.le _
    have hB := trap_error_factor_le hs0 h1 hT hpow0 hNneg
    linarith only [mul_le_mul_of_nonneg_right hB hT0.le]
  have hmain := integral_normSq_riemannZeta_le_aux_trap hs0 h1 hN1 hT0.le
  have hexp : (4 * C₂ * (1 + 8 * C₃) + 36 * (Real.pi / 2 / (1 - σ) ^ 2) + 5) * T
      = 4 * C₂ * (1 + 8 * C₃) * T + 36 * (Real.pi / 2 / (1 - σ) ^ 2) * T + T + 4 * T := by ring
  rw [hexp]
  linarith only [hmain, hb1, hb2, hb3]

/-! ## Two consequences: the first moment, and a large values estimate -/

/-- **The first moment of `ζ` on a vertical line with `3/5 < σ < 1` is `O(T)`.**

Immediate from the mean square and `x ≤ (1 + x²)/2`. -/
theorem exists_integral_norm_riemannZeta_le_three_fifths {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) ≤ C * T := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_three_fifths h0 h1
  refine ⟨(1 + C) / 2, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hc := continuous_riemannZeta_line_of_lt_one (σ := σ) h1
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
      volume 0 T := hc.norm.intervalIntegrable 0 T
  have hisq : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume 0 T := (continuous_normSq_riemannZeta_line_of_lt_one h1).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2) volume 0 T :=
    ((continuous_const.add (continuous_normSq_riemannZeta_line_of_lt_one h1)).div_const
      2).intervalIntegrable 0 T
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    intro t _
    nlinarith [sq_nonneg (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ - 1)]
  refine (intervalIntegral.integral_mono_on hT0 hi1 hi2 hle).trans ?_
  have hsplit : (∫ t in (0 : ℝ)..T, (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2)
      = (T + ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hisq,
      intervalIntegral.integral_const]
    simp
  rw [hsplit]
  linarith [hmean T hT]

/-- **A large values estimate for `3/5 < σ < 1`.**  The set of `t ∈ (0, T]` at which
`‖ζ(σ + i t)‖ ≥ V` has measure `O(T / V²)`. -/
theorem exists_volume_norm_riemannZeta_ge_le_three_fifths {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal ≤ C * T / V ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_three_fifths h0 h1
  refine ⟨C, hC, fun T hT V hV => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set f : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf
  have hcont : Continuous f := continuous_normSq_riemannZeta_line_of_lt_one h1
  have hint : IntegrableOn f (Set.Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 (hcont.intervalIntegrable 0 T)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] f :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (V ^ 2)
  have hset : {t : ℝ | V ^ 2 ≤ f t} ∩ Set.Ioc (0 : ℝ) T
      = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧ V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hf]
    constructor
    · rintro ⟨hle, ht⟩
      exact ⟨ht, by nlinarith [norm_nonneg (riemannZeta ((σ : ℂ) + (t : ℂ) * I))]⟩
    · rintro ⟨ht, hle⟩
      exact ⟨by nlinarith, ht⟩
  have hmeas : MeasurableSet {t : ℝ | V ^ 2 ≤ f t} :=
    measurableSet_le measurable_const hcont.measurable
  have hrestrict : (volume.restrict (Set.Ioc (0 : ℝ) T)).real {t : ℝ | V ^ 2 ≤ f t}
      = (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply hmeas, hset]
  have hintegral : ∫ t in Set.Ioc (0 : ℝ) T, f t ≤ C * T := by
    rw [← intervalIntegral.integral_of_le hT0]
    exact hmean T hT
  rw [hrestrict] at hmarkov
  rw [le_div_iff₀ (by positivity)]
  calc (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal * V ^ 2
      = V ^ 2 * (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by ring
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, f t := hmarkov
    _ ≤ C * T := hintegral

end RiemannHypothesis
