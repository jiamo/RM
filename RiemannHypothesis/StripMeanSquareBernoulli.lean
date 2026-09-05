/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareTrapezoid

/-!
# The second Euler–Maclaurin correction and the mean square of `ζ` for `σ > 4/7`

`RiemannHypothesis.StripMeanSquare` proves `∫₀ᵀ ‖ζ(σ + i t)‖² dt = O_σ(T)` for `2/3 < σ < 1`,
and `RiemannHypothesis.StripMeanSquareTrapezoid` improves the range to `3/5 < σ < 1` by adding
the trapezoidal (first Bernoulli) correction.  This file adds the *second* correction, the one
carrying the Bernoulli number `B₂ = 1/6`:

`ζ(s) = ∑_{n ≤ N} n^(-s) + (N+1)^(1-s)/(s-1) + (N+1)^(-s)/2 + s (N+1)^(-s-1)/12 + R_N(s)`,

whose remainder is controlled by the *third* derivative of `x ↦ x^(-s)`,

`‖R_N(s)‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ N^(-(2+σ)) / (48 (2+σ))`.

One further power of `N` is gained over the trapezoidal expansion, the Dirichlet polynomial may
be taken of length `N ≍ T^(3/(2+σ))`, and the balance `(3/(2+σ)) (2 - 2σ) < 1` becomes `σ > 4/7`.

## Main results

* `bern3Green` : the Green's function `B₃(x - a)/6` of the second correction, where
  `B₃(u) = u(u - 1/2)(u - 1)` is the third Bernoulli polynomial.
* `bernTerm` : the second-order Euler–Maclaurin term, the trapezoidal term with its
  `B₂`-correction removed.
* `bernTerm_eq_integral` : `bernTerm n s = ∫ B₃(x - n - 1)/6 · f'''(x) dx` over `[n+1, n+2]`.
* `norm_bernTerm_le` : `‖bernTerm n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ (n+1)^(-(3 + re s)) / 48`.
* `riemannZeta_eq_bernApprox`, `norm_riemannZeta_sub_dirichletPoly_le_bern` : the second-order
  Euler–Maclaurin representation of `ζ` and the resulting bound on a vertical line.
* `exists_integral_normSq_riemannZeta_le_four_sevenths` : **the mean square bound**
  `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C_σ T` for `4/7 < σ < 1` and `T ≥ 1`.
* `exists_integral_norm_riemannZeta_le_four_sevenths`,
  `exists_volume_norm_riemannZeta_ge_le_four_sevenths` : the first moment and the large values
  estimate in the same range.

The classical theorem of Bohr and Landau gives the same bounds for every `σ > 1/2`; `k`
Bernoulli terms give `σ > (k+2)/(2k+3)`, and what is formalized here is the case `k = 2`.
Nothing below is an asymptotic, and nothing below bears on the location of the zeroes.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace RiemannHypothesis

/-! ## The second Green's function and its derivatives -/

/-- The Green's function of the second Euler–Maclaurin correction on `[a, a+1]`:
`bern3Green a z = B₃(z - a)/6` with `B₃(u) = u³ - (3/2) u² + (1/2) u = u (u - 1/2) (u - 1)`.
It vanishes at both endpoints and has third derivative `1`. -/
def bern3Green (a : ℝ) (z : ℂ) : ℂ :=
  ((z - (a : ℂ)) ^ 3 - 3 / 2 * (z - (a : ℂ)) ^ 2 + 1 / 2 * (z - (a : ℂ))) / 6

/-- The derivative of `bern3Green a`. -/
def bern3GreenD (a : ℝ) (z : ℂ) : ℂ := ((z - (a : ℂ)) ^ 2 - (z - (a : ℂ))) / 2 + 1 / 12

/-- The second derivative of `bern3Green a`. -/
def bern3GreenDD (a : ℝ) (z : ℂ) : ℂ := (z - (a : ℂ)) - 1 / 2

/-- The primitive used in the integration by parts behind `bernTerm_eq_integral`:
`H = Q f'' - Q' f' + Q'' f` for `f x = x^(-s)`, so that `H' = Q f''' + f`. -/
def bernPrimitive (a : ℝ) (s : ℂ) (z : ℂ) : ℂ :=
  bern3Green a z * (s * (s + 1) * z ^ (-s - 2)) + bern3GreenD a z * (s * z ^ (-s - 1))
    + bern3GreenDD a z * z ^ (-s)

/-- **The second-order Euler–Maclaurin term**: the trapezoidal term with its `B₂`-correction
`(1/12)(f'(n+2) - f'(n+1))` removed. -/
def bernTerm (n : ℕ) (s : ℂ) : ℂ :=
  trapTerm n s - (s * ((n + 1 : ℝ) : ℂ) ^ (-s - 1) - s * ((n + 2 : ℝ) : ℂ) ^ (-s - 1)) / 12

/-- The derivative of the primitive: `H' = Q f''' + f`. -/
theorem hasDerivAt_bernPrimitive (a : ℝ) {s : ℂ} (hs0 : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => bernPrimitive a s (y : ℂ))
      (bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))
        + (x : ℂ) ^ (-s)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsne : -s ≠ 0 := by
    simp only [neg_ne_zero]; intro h; rw [h] at hs0; simp at hs0
  have hs1ne : -s - 1 ≠ 0 := by
    intro h
    have hre' : (-s - 1).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at hre'
    linarith
  have hs2ne : -s - 2 ≠ 0 := by
    intro h
    have hre' : (-s - 2).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re] at hre'
    norm_num at hre'
    linarith
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 2))
      ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x := hasDerivAt_ofReal_cpow_const hxne hs2ne
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1))
      ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x := hasDerivAt_ofReal_cpow_const hxne hs1ne
  have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const hxne hsne
  have hre : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 x := by
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 : ℂ)) ((1 : ℂ) * (x : ℂ) ^ ((1 : ℂ) - 1)) x :=
      hasDerivAt_ofReal_cpow_const hxne one_ne_zero
    simpa using h0
  have hb : HasDerivAt (fun y : ℝ => (y : ℂ) - (a : ℂ)) 1 x := hre.sub_const _
  have hQ : HasDerivAt (fun y : ℝ => bern3Green a (y : ℂ)) (bern3GreenD a (x : ℂ)) x := by
    have h := ((((hb.pow 3).sub (((hb.pow 2)).const_mul (3 / 2 : ℂ))).add
      (hb.const_mul (1 / 2 : ℂ))).div_const 6)
    refine h.congr_deriv ?_
    unfold bern3GreenD
    simp
    ring
  have hQD : HasDerivAt (fun y : ℝ => bern3GreenD a (y : ℂ)) (bern3GreenDD a (x : ℂ)) x := by
    have h := (((hb.pow 2).sub hb).div_const 2).add_const (1 / 12 : ℂ)
    refine h.congr_deriv ?_
    unfold bern3GreenDD
    simp
    ring
  have hQDD : HasDerivAt (fun y : ℝ => bern3GreenDD a (y : ℂ)) 1 x := hb.sub_const _
  have hmain := ((hQ.mul (h1.const_mul (s * (s + 1)))).add
    (hQD.mul (h2.const_mul s))).add (hQDD.mul h3)
  have hpow1 : (x : ℂ) ^ (-s - 2 - 1) = (x : ℂ) ^ (-s - 3) := by congr 1; ring
  have hpow2 : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  refine hmain.congr_deriv ?_
  rw [hpow1, hpow2]
  ring

/-- The integrand `Q f''' + f` of the second correction is continuous on `[a, a+1]`. -/
theorem continuousOn_bernIntegrand (a : ℝ) (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    ContinuousOn (fun x : ℝ =>
        bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)) + (x : ℂ) ^ (-s))
      (Set.uIcc a (a + 1)) := by
  have hab : a ≤ a + 1 := by linarith
  have hsne : -s ≠ 0 := by
    simp only [neg_ne_zero]; intro h; rw [h] at hs0; simp at hs0
  have hs3ne : -s - 3 ≠ 0 := by
    intro h
    have hre' : (-s - 3).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re] at hre'
    norm_num at hre'
    linarith
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have c1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-s - 3)) x :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hs3ne).continuousAt
  have c2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-s)) x :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hsne).continuousAt
  have c3 : ContinuousAt (fun y : ℝ => bern3Green a (y : ℂ)) x := by
    unfold bern3Green
    fun_prop
  exact ((c3.mul (c1.const_mul _)).add c2).continuousWithinAt

/-- The integration by parts identity `∫ (Q f''' + f) = (f(a) + f(a+1))/2 - (1/12)(f'(a+1) -
f'(a))`, written out for `f x = x^(-s)`. -/
theorem integral_bernIntegrand (a : ℝ) (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) :
    (∫ x in a..(a + 1), (bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))
        + (x : ℂ) ^ (-s)))
      = (((a : ℝ) : ℂ) ^ (-s) + ((a + 1 : ℝ) : ℂ) ^ (-s)) / 2
        + s * (((a + 1 : ℝ) : ℂ) ^ (-s - 1) - ((a : ℝ) : ℂ) ^ (-s - 1)) / 12 := by
  have hab : a ≤ a + 1 := by linarith
  have hpos : ∀ x ∈ Set.uIcc a (a + 1), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => bernPrimitive a s (y : ℂ))
        (bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))
          + (x : ℂ) ^ (-s)) x :=
    fun x hx => hasDerivAt_bernPrimitive a hs0 (hpos x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_bernIntegrand a ha hs0).intervalIntegrable]
  unfold bernPrimitive bern3Green bern3GreenD bern3GreenDD
  push_cast
  ring_nf

/-- **The second-order remainder in integral form**: `bernTerm n s = ∫ Q f'''`. -/
theorem bernTerm_eq_integral (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    bernTerm n s = ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 1 + 1),
      bern3Green ((n : ℝ) + 1) (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a + 1 = (n : ℝ) + 2 := by rw [ha]; ring
  have hF : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a (a + 1) :=
    intervalIntegrable_cpow_neg ha0 hs0
  have hG : IntervalIntegrable (fun x : ℝ =>
      bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))) volume a (a + 1) := by
    have hsum := (continuousOn_bernIntegrand a ha0 hs0).intervalIntegrable (μ := volume)
    have heq : (fun x : ℝ => bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)))
        = (fun x : ℝ => (bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))
            + (x : ℂ) ^ (-s)) - (x : ℂ) ^ (-s)) := by funext x; ring
    rw [heq]
    exact hsum.sub hF
  have hconst : IntervalIntegrable (fun _ : ℝ => ((a : ℝ) : ℂ) ^ (-s)) volume a (a + 1) :=
    intervalIntegrable_const (μ := volume)
  have heuler : eulerTerm n s = ((a : ℂ) ^ (-s)) - ∫ x in a..(a + 1), (x : ℂ) ^ (-s) := by
    rw [eulerTerm_eq_integral n hs1, ← ha2]
    rw [intervalIntegral.integral_sub hconst hF]
    simp [ha]
  have hsplit := intervalIntegral.integral_add hG hF
  have hkey := integral_bernIntegrand a ha0 hs0
  rw [hsplit] at hkey
  unfold bernTerm trapTerm
  rw [heuler, ← ha2]
  rw [ha] at hkey ⊢
  push_cast at hkey ⊢
  linear_combination -hkey

/-! ## The size of the second-order term -/

/-- The Green's function of the second correction is bounded by `1/48`. -/
theorem norm_bern3Green_le {a x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ a + 1) :
    ‖bern3Green a (x : ℂ)‖ ≤ 1 / 48 := by
  have hcast : (x : ℂ) - (a : ℂ) = ((x - a : ℝ) : ℂ) := by push_cast; ring
  have hre : bern3Green a (x : ℂ)
      = ((((x - a) ^ 3 - 3 / 2 * (x - a) ^ 2 + 1 / 2 * (x - a)) / 6 : ℝ) : ℂ) := by
    unfold bern3Green
    rw [hcast]
    push_cast
    ring
  rw [hre, Complex.norm_real, Real.norm_eq_abs]
  set u : ℝ := x - a with hu
  have h0 : 0 ≤ u := by rw [hu]; linarith
  have h1 : u ≤ 1 := by rw [hu]; linarith
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6),
    div_le_div_iff₀ (by norm_num) (by norm_num)]
  have hkey : |u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u| ≤ 1 / 8 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg u, mul_nonneg h0 (sub_nonneg.2 h1),
        sq_nonneg (u * (1 - u))]
    · nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg u, mul_nonneg h0 (sub_nonneg.2 h1),
        sq_nonneg (u * (1 - u))]
  linarith

/-- **The size of the second-order term**:
`‖bernTerm n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ (n+1)^(-(3+σ))/48`. -/
theorem norm_bernTerm_le (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖bernTerm n s‖ ≤ 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  rw [bernTerm_eq_integral n hs0 hs1]
  have hbd : ∀ x ∈ Set.uIoc a (a + 1),
      ‖bern3Green a (x : ℂ) * (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3))‖
        ≤ 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * a ^ (-(3 + s.re)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_trans ha0 hx1
    have hnorm : ‖(x : ℂ) ^ (-s - 3)‖ = x ^ (-(3 + s.re)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp [Complex.sub_re, Complex.neg_re]
      ring
    have hpow : x ^ (-(3 + s.re)) ≤ a ^ (-(3 + s.re)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hx1.le (by linarith)
    have hG := norm_bern3Green_le (a := a) hx1.le hx2
    rw [norm_mul, norm_mul, hnorm, norm_neg, norm_mul, norm_mul]
    have h1 : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by positivity
    calc ‖bern3Green a (x : ℂ)‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * x ^ (-(3 + s.re)))
        ≤ (1 / 48) * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * a ^ (-(3 + s.re))) := by
          refine mul_le_mul hG ?_ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hpow h1
      _ = 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * a ^ (-(3 + s.re)) := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-! ## The second-order representation of `ζ` -/

/-- The tail of the second-order terms is summable. -/
theorem summable_bernTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    Summable (fun n : ℕ => bernTerm (n + N) s) := by
  have hsum : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re))) :=
    (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (p := 3 + s.re) (by linarith))
  exact Summable.of_norm_bounded (hsum.mul_left (1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖))
    fun n => norm_bernTerm_le (n + N) hs0 hs1

/-- The telescoping sum of the `B₂`-corrections. -/
theorem tsum_bern_correction {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) :
    ∑' n : ℕ, (s * ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
        - s * ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) / 12
      = s * ((((N : ℝ) + 1 : ℝ)) : ℂ) ^ (-s - 1) / 12 := by
  have hs0' : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hs1' : s + 1 ≠ 1 := by
    intro h
    have : s = 0 := by linear_combination h
    rw [this] at hs0
    simp at hs0
  have hbase := tsum_cpow_telescope hs0' hs1' N
  have hexp : ∀ z : ℂ, z ^ (-(s + 1)) = z ^ (-s - 1) := by
    intro z; congr 1; ring
  simp only [hexp] at hbase
  calc ∑' n : ℕ, (s * ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
        - s * ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) / 12
      = ∑' n : ℕ, (s / 12) * (((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
          - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) := by
        refine tsum_congr fun n => ?_; ring
    _ = (s / 12) * ∑' n : ℕ, (((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
          - ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) := tsum_mul_left
    _ = s * ((((N : ℝ) + 1 : ℝ)) : ℂ) ^ (-s - 1) / 12 := by rw [hbase]; ring

/-- The trapezoidal tail, split into its `B₂`-correction and the second-order remainder. -/
theorem tsum_trapTerm_eq_bernTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    ∑' n : ℕ, trapTerm (n + N) s
      = s * ((((N : ℝ) + 1 : ℝ)) : ℂ) ^ (-s - 1) / 12 + ∑' n : ℕ, bernTerm (n + N) s := by
  have hbern : Summable (fun n : ℕ => bernTerm (n + N) s) := summable_bernTerm hs0 hs1 N
  have htrap : Summable (fun n : ℕ => trapTerm (n + N) s) := summable_trapTerm hs0 hs1 N
  have hcorr : Summable (fun n : ℕ => (s * ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
      - s * ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) / 12) := by
    refine (htrap.sub hbern).congr fun n => ?_
    unfold bernTerm
    push_cast
    ring
  have hsplit : ∀ n : ℕ, trapTerm (n + N) s
      = (s * ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)
          - s * ((((n + N : ℕ) : ℝ) + 2 : ℝ) : ℂ) ^ (-s - 1)) / 12 + bernTerm (n + N) s := by
    intro n
    unfold bernTerm
    push_cast
    ring
  rw [tsum_congr hsplit, hcorr.tsum_add hbern, tsum_bern_correction hs0 N]

/-- **The second-order Euler–Maclaurin representation of `ζ`** on the punctured right
half-plane. -/
theorem riemannZeta_eq_bernApprox (N : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
        + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2
        + s * ((N + 1 : ℝ) : ℂ) ^ (-s - 1) / 12
        + ∑' n : ℕ, bernTerm (n + N) s := by
  rw [riemannZeta_eq_trapApprox N hs0 hs1, tsum_trapTerm_eq_bernTerm hs0 hs1 N]
  push_cast
  ring

/-- **The second-order Euler–Maclaurin bound** for the difference between `ζ` and the truncated
zeta sum on a vertical line inside the strip.  Compared with
`norm_riemannZeta_sub_dirichletPoly_le_trap` the tail is `O(‖s‖³ N^(-2-σ))` in place of
`O(‖s‖² N^(-1-σ))`, at the cost of one extra explicit term. -/
theorem norm_riemannZeta_sub_dirichletPoly_le_bern {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
        + ((N : ℝ) + 1) ^ (-σ) / 2
        + (σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / 12
        + (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) * (N : ℝ) ^ (-(2 + σ))
            / (48 * (2 + σ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
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
  have hnorm_s2 : ‖s + 2‖ ≤ 2 + σ + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre2 : (s + 2).re = σ + 2 := by
      rw [Complex.add_re, hre]; simp
    have him2 : (s + 2).im = t := by
      rw [Complex.add_im, him]; simp
    rw [hre2, him2, abs_of_pos (by linarith)] at h
    linarith
  rw [riemannZeta_eq_bernApprox N hs0 hs1, ← dirichletPoly_one N s]
  have hsplit : dirichletPoly (fun _ => 1) N s + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + s * ((N + 1 : ℝ) : ℂ) ^ (-s - 1) / 12
      + (∑' n : ℕ, bernTerm (n + N) s)
      - dirichletPoly (fun _ => 1) N s
      = ((((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2)
        + s * ((N + 1 : ℝ) : ℂ) ^ (-s - 1) / 12)
        + ∑' n : ℕ, bernTerm (n + N) s := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  · -- the explicit `B₂`-term
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hexp : (-s - 1).re = -(1 + σ) := by
      simp [Complex.sub_re, Complex.neg_re, hre]; ring
    rw [hexp]
    have hmono : ((N : ℝ) + 1) ^ (-(1 + σ)) ≤ (N : ℝ) ^ (-(1 + σ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    have hpos : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (-(1 + σ)) := Real.rpow_nonneg (by positivity) _
    have : ‖s‖ * ((N : ℝ) + 1) ^ (-(1 + σ)) ≤ (σ + |t|) * (N : ℝ) ^ (-(1 + σ)) := by
      have h1' : (0 : ℝ) ≤ σ + |t| := by positivity
      calc ‖s‖ * ((N : ℝ) + 1) ^ (-(1 + σ)) ≤ (σ + |t|) * ((N : ℝ) + 1) ^ (-(1 + σ)) :=
            mul_le_mul_of_nonneg_right hnorm_s hpos
        _ ≤ (σ + |t|) * (N : ℝ) ^ (-(1 + σ)) := mul_le_mul_of_nonneg_left hmono h1'
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    linarith [this]
  · -- the second-order tail
    have hbd : ∀ n : ℕ, ‖bernTerm (n + N) s‖
        ≤ 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re)) :=
      fun n => norm_bernTerm_le (n + N) hs0 hs1
    have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by rw [hre]; linarith))
    have hsummable := hsh.mul_left (1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
    have hnorms : Summable (fun n : ℕ => ‖bernTerm (n + N) s‖) :=
      hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
    have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re))
        ≤ (N : ℝ) ^ (1 - (3 + s.re)) / ((3 + s.re) - 1) :=
      tsum_shift_rpow_neg_le_rpow (by rw [hre]; linarith) hN
    have hpos : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re)) :=
      tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
    have hprod : 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖
        ≤ 1 / 48 * (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) := by
      have h1' : (0 : ℝ) ≤ σ + |t| := by positivity
      have hA : ‖s‖ * ‖s + 1‖ ≤ (σ + |t|) * (1 + σ + |t|) :=
        mul_le_mul hnorm_s hnorm_s1 (norm_nonneg _) h1'
      have hB : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) :=
        mul_le_mul hA hnorm_s2 (norm_nonneg _) (by positivity)
      linarith
    calc ‖∑' n : ℕ, bernTerm (n + N) s‖
        ≤ ∑' n : ℕ, ‖bernTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖
            * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re)) := hnorms.tsum_le_tsum hbd hsummable
      _ = 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖
            * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(3 + s.re)) := tsum_mul_left
      _ ≤ 1 / 48 * (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|)
            * ((N : ℝ) ^ (1 - (3 + s.re)) / ((3 + s.re) - 1)) := by
          refine mul_le_mul hprod htail hpos (by positivity)
      _ = (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) * (N : ℝ) ^ (-(2 + σ))
            / (48 * (2 + σ)) := by
          rw [hre, show (1 : ℝ) - (3 + σ) = -(2 + σ) by ring, show (3 + σ) - 1 = 2 + σ by ring]
          field_simp

/-! ## The mean square of `ζ` for `σ > 4/7` -/

set_option maxHeartbeats 1000000 in
-- the pointwise bound combines several estimates and needs a long arithmetic normalisation
/-- The pointwise bound behind the mean square estimate, with the second-order error term. -/
theorem normSq_riemannZeta_le_pointwise_bern {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 5 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 5 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)))
        + 5 / 4
        + 5 * ((σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144)
        + 5 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * (N : ℝ) ^ (-(4 + 2 * σ))
            / (2304 * (2 + σ) ^ 2)) := by
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
  have hbd := norm_riemannZeta_sub_dirichletPoly_le_bern h0 h1 hN t
  set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
  set E2 : ℝ := ((N : ℝ) + 1) ^ (-σ) / 2 with hE2
  set E3 : ℝ := (σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / 12 with hE3
  set E4 : ℝ := (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) * (N : ℝ) ^ (-(2 + σ))
    / (48 * (2 + σ)) with hE4
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
  have hE30 : 0 ≤ E3 := by rw [hE3]; positivity
  have hE40 : 0 ≤ E4 := by rw [hE4]; positivity
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + E1 + E2 + E3 + E4 := by
    have := norm_sub_norm_le (riemannZeta s) P
    linarith [hbd]
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ 5 * (‖P‖ ^ 2 + E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) := by
    nlinarith [norm_nonneg (riemannZeta s), norm_nonneg P, hE10, hE20, hE30, hE40, htri,
      sq_nonneg (‖P‖ - E1), sq_nonneg (‖P‖ - E2), sq_nonneg (‖P‖ - E3), sq_nonneg (‖P‖ - E4),
      sq_nonneg (E1 - E2), sq_nonneg (E1 - E3), sq_nonneg (E1 - E4), sq_nonneg (E2 - E3),
      sq_nonneg (E2 - E4), sq_nonneg (E3 - E4)]
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
  have habs : |t| = t := abs_of_nonneg ht0
  have hE3sq : E3 ^ 2 ≤ (σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144 := by
    have hpow : ((N : ℝ) ^ (-(1 + σ))) ^ 2 = (N : ℝ) ^ (-(2 + 2 * σ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 + σ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have hC : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 + σ)) := Real.rpow_nonneg hN0.le _
    have hA : (0 : ℝ) ≤ σ + t := by linarith
    have hAT : σ + t ≤ σ + T := by linarith
    rw [hE3, habs]
    calc ((σ + t) * (N : ℝ) ^ (-(1 + σ)) / 12) ^ 2
        = (σ + t) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / 144 := by rw [div_pow]; ring_nf
      _ ≤ (σ + T) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / 144 := by gcongr
      _ = (σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144 := by rw [hpow]
  have hE4sq : E4 ^ 2 ≤ (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2
      * (N : ℝ) ^ (-(4 + 2 * σ)) / (2304 * (2 + σ) ^ 2) := by
    have hpow : ((N : ℝ) ^ (-(2 + σ))) ^ 2 = (N : ℝ) ^ (-(4 + 2 * σ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (-(2 + σ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have hC : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 + σ)) := Real.rpow_nonneg hN0.le _
    have hA : (0 : ℝ) ≤ σ + t := by linarith
    have hB : (0 : ℝ) ≤ 1 + σ + t := by linarith
    have hD : (0 : ℝ) ≤ 2 + σ + t := by linarith
    have hAT : σ + t ≤ σ + T := by linarith
    have hBT : 1 + σ + t ≤ 1 + σ + T := by linarith
    have hDT : 2 + σ + t ≤ 2 + σ + T := by linarith
    rw [hE4, habs]
    calc ((σ + t) * (1 + σ + t) * (2 + σ + t) * (N : ℝ) ^ (-(2 + σ)) / (48 * (2 + σ))) ^ 2
        = (σ + t) ^ 2 * (1 + σ + t) ^ 2 * (2 + σ + t) ^ 2 * ((N : ℝ) ^ (-(2 + σ))) ^ 2
            / (2304 * (2 + σ) ^ 2) := by rw [div_pow]; ring_nf
      _ ≤ (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * ((N : ℝ) ^ (-(2 + σ))) ^ 2
            / (2304 * (2 + σ) ^ 2) := by gcongr
      _ = (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * (N : ℝ) ^ (-(4 + 2 * σ))
            / (2304 * (2 + σ) ^ 2) := by rw [hpow]
  linarith [hsq, hE1sq, hE2sq, hE3sq, hE4sq]

/-- The mean square of `ζ` on `[0, T]`, in terms of the length `N` of the Dirichlet polynomial,
with the second-order error terms. -/
theorem integral_normSq_riemannZeta_le_aux_bern {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 5 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 5 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2)
        + 5 / 4 * T
        + 5 * ((σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144) * T
        + 5 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * (N : ℝ) ^ (-(4 + 2 * σ))
            / (2304 * (2 + σ) ^ 2)) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set B : ℝ := (σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144 with hB
  set D : ℝ := (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * (N : ℝ) ^ (-(4 + 2 * σ))
    / (2304 * (2 + σ) ^ 2) with hD
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hzetaC := continuous_normSq_riemannZeta_line_of_lt_one (σ := σ) h1
  have hPC := continuous_normSq_dirichletPoly_line (σ := σ) N
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 5 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    ((hPC.const_smul (5 : ℝ)).congr fun t => by simp [smul_eq_mul]).intervalIntegrable 0 T
  have hcont2 : Continuous (fun t : ℝ => 5 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) :=
    continuous_const.mul (continuous_const.mul
      (Continuous.div continuous_const (by fun_prop) fun t => by
        have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by
          have : (0 : ℝ) < (1 - σ) ^ 2 := pow_pos (by linarith) 2
          nlinarith [sq_nonneg t]
        exact ne_of_gt hpos))
  have hi2 : IntervalIntegrable (fun t : ℝ => 5 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) volume 0 T :=
    hcont2.intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => (5 / 4 : ℝ)) volume 0 T := intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun _ : ℝ => 5 * B) volume 0 T := intervalIntegrable_const
  have hi5 : IntervalIntegrable (fun _ : ℝ => 5 * D) volume 0 T := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hzetaC.intervalIntegrable 0 T)
    ((((hi1.add hi2).add hi3).add hi4).add hi5)
    (fun t ht => normSq_riemannZeta_le_pointwise_bern h0 h1 hN ht.1 ht.2)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add (((hi1.add hi2).add hi3).add hi4) hi5,
    intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hφ : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero]
  nlinarith [hφ, hA0]

/-- The second-order error factor is bounded by `1` once `x ≤ (T^6)⁻¹`; this is the choice
`N ≍ T^(3/(2+σ))`, for which `N^(-(4+2σ)) ≤ T^(-6)`. -/
private lemma bern_error_factor_le {σ T x : ℝ} (hs0 : 0 < σ) (h1 : σ < 1) (hT : 1 ≤ T)
    (hx0 : 0 ≤ x) (hx : x ≤ (T ^ 6)⁻¹) :
    (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * x / (2304 * (2 + σ) ^ 2) ≤ 1 := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have hnum : (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 ≤ 576 * T ^ 6 := by
    have hsq1 : (σ + T) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
    have hsq2 : (1 + σ + T) ^ 2 ≤ 9 * T ^ 2 := by nlinarith
    have hsq3 : (2 + σ + T) ^ 2 ≤ 16 * T ^ 2 := by nlinarith
    calc (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2
        ≤ (4 * T ^ 2) * (9 * T ^ 2) * (16 * T ^ 2) := by
          have h12 : (σ + T) ^ 2 * (1 + σ + T) ^ 2 ≤ (4 * T ^ 2) * (9 * T ^ 2) :=
            mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
          exact mul_le_mul h12 hsq3 (by positivity) (by positivity)
      _ = 576 * T ^ 6 := by ring
  have hstep : (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * x ≤ 576 * T ^ 6 * (T ^ 6)⁻¹ :=
    mul_le_mul hnum hx hx0 (by positivity)
  have heq : 576 * T ^ 6 * (T ^ 6)⁻¹ = 576 := by field_simp
  rw [heq] at hstep
  rw [div_le_one (by positivity)]
  nlinarith

/-- The explicit `B₂`-term factor is bounded by `1` once `x ≤ (T^2)⁻¹`. -/
private lemma bern_b2_factor_le {σ T x : ℝ} (hs0 : 0 < σ) (h1 : σ < 1) (hT : 1 ≤ T)
    (hx0 : 0 ≤ x) (hx : x ≤ (T ^ 2)⁻¹) :
    (σ + T) ^ 2 * x / 144 ≤ 1 := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have hnum : (σ + T) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
  have hstep : (σ + T) ^ 2 * x ≤ 4 * T ^ 2 * (T ^ 2)⁻¹ := mul_le_mul hnum hx hx0 (by positivity)
  have heq : 4 * T ^ 2 * (T ^ 2)⁻¹ = 4 := by field_simp
  rw [heq] at hstep
  rw [div_le_one (by norm_num)]
  linarith

/-- **The mean square of `ζ` on a vertical line with `4/7 < σ < 1` is `O(T)`.**

This improves `exists_integral_normSq_riemannZeta_le_three_fifths`, which requires `3/5 < σ`.
The gain comes from the second Euler–Maclaurin correction: the tail of the expansion is
`O(‖s‖³ N^(-2-σ))` instead of `O(‖s‖² N^(-1-σ))`, so the Dirichlet polynomial may be taken of
length `N ≍ T^(3/(2+σ))` and the balance condition `(3/(2+σ)) (2 - 2σ) < 1` reads `σ > 4/7`. -/
theorem exists_integral_normSq_riemannZeta_le_four_sevenths {σ : ℝ} (h0 : 4 / 7 < σ)
    (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have h1s : (0 : ℝ) < 1 - σ := by linarith
  have hσ2 : (0 : ℝ) < 2 + σ := by linarith
  have ha1 : (6 - 6 * σ) / (2 + σ) < 1 := by rw [div_lt_one hσ2]; linarith
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le (by linarith) h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  have hC₄ : (0 : ℝ) < Real.pi / 2 / (1 - σ) ^ 2 := div_pos (by positivity) (pow_pos h1s 2)
  refine ⟨5 * C₂ * (1 + 8 * C₃) + 45 * (Real.pi / 2 / (1 - σ) ^ 2) + 45 / 4, by nlinarith,
    fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hx1 : (1 : ℝ) ≤ T ^ (3 / (2 + σ)) := Real.one_le_rpow hT (by positivity)
  have hx0 : (0 : ℝ) < T ^ (3 / (2 + σ)) := by linarith
  obtain ⟨N, hN1, hxN, hNx⟩ : ∃ N : ℕ, 1 ≤ N ∧ T ^ (3 / (2 + σ)) ≤ (N : ℝ) ∧
      (N : ℝ) ≤ T ^ (3 / (2 + σ)) + 1 := by
    refine ⟨⌈T ^ (3 / (2 + σ))⌉₊, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one hx0.le).le⟩
    have h := le_trans hx1 (Nat.le_ceil (T ^ (3 / (2 + σ))))
    exact_mod_cast h
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- the exponent identities
  have hxa : (T ^ (3 / (2 + σ))) ^ (2 - 2 * σ) = T ^ ((6 - 6 * σ) / (2 + σ)) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    field_simp
    ring
  have hxd : (T ^ (3 / (2 + σ))) ^ (-(4 + 2 * σ)) = (T ^ 6)⁻¹ := by
    rw [← Real.rpow_mul hT0.le, show 3 / (2 + σ) * -(4 + 2 * σ) = -(6 : ℝ) by
      field_simp; ring, Real.rpow_neg hT0.le]
    norm_num
  have hxe : (T ^ (3 / (2 + σ))) ^ (-(2 + 2 * σ)) ≤ (T ^ 2)⁻¹ := by
    rw [← Real.rpow_mul hT0.le]
    have hexp : (2 : ℝ) ≤ 3 / (2 + σ) * (2 + 2 * σ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hσ2]
      nlinarith
    have hle : T ^ (3 / (2 + σ) * -(2 + 2 * σ)) ≤ T ^ (-2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hT ?_
      have hneg : 3 / (2 + σ) * -(2 + 2 * σ) = -(3 / (2 + σ) * (2 + 2 * σ)) := by ring
      rw [hneg]
      linarith
    calc T ^ (3 / (2 + σ) * -(2 + 2 * σ)) ≤ T ^ (-2 : ℝ) := hle
      _ = (T ^ 2)⁻¹ := by
          rw [Real.rpow_neg hT0.le]
          norm_num
  have hTa0 : (0 : ℝ) ≤ T ^ ((6 - 6 * σ) / (2 + σ)) := Real.rpow_nonneg hT0.le _
  have hTa : T ^ ((6 - 6 * σ) / (2 + σ)) ≤ T := by
    calc T ^ ((6 - 6 * σ) / (2 + σ)) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha1.le
      _ = T := Real.rpow_one T
  -- the length of the Dirichlet polynomial
  have hNa : (N : ℝ) ^ (2 - 2 * σ) ≤ 4 * T ^ ((6 - 6 * σ) / (2 + σ)) := by
    have h2 : (N : ℝ) ^ (2 - 2 * σ) ≤ (2 * T ^ (3 / (2 + σ))) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (2 : ℝ) ^ (2 - 2 * σ) ≤ 4 := by
      calc (2 : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    nlinarith
  have hNa' : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 9 * T := by
    have h2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ (3 * T ^ (3 / (2 + σ))) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (3 : ℝ) ^ (2 - 2 * σ) ≤ 9 := by
      calc (3 : ℝ) ^ (2 - 2 * σ) ≤ (3 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9 := by norm_num
    nlinarith
  have hNlog : Real.log N ≤ 1 + 2 * Real.log T := by
    have hle : Real.log N ≤ Real.log (2 * T ^ (3 / (2 + σ))) :=
      Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), Real.log_rpow hT0] at hle
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hinv : 3 / (2 + σ) ≤ 2 := by
      rw [div_le_iff₀ hσ2]; linarith
    nlinarith
  have hNneg : (N : ℝ) ^ (-(4 + 2 * σ)) ≤ (T ^ 6)⁻¹ := by
    have h2 : (N : ℝ) ^ (-(4 + 2 * σ)) ≤ (T ^ (3 / (2 + σ))) ^ (-(4 + 2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
    rwa [hxd] at h2
  have hNneg2 : (N : ℝ) ^ (-(2 + 2 * σ)) ≤ (T ^ 2)⁻¹ := by
    have h2 : (N : ℝ) ^ (-(2 + 2 * σ)) ≤ (T ^ (3 / (2 + σ))) ^ (-(2 + 2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
    linarith [hxe]
  -- the contributions
  have hprod : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ 8 * (C₃ * T) := by
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
    have hNpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)
        ≤ 4 * T ^ ((6 - 6 * σ) / (2 + σ)) * (2 * (1 + Real.log T)) :=
          mul_le_mul hNa (by linarith) (by linarith) (by linarith)
      _ = 8 * (T ^ ((6 - 6 * σ) / (2 + σ)) * (1 + Real.log T)) := by ring
      _ ≤ 8 * (C₃ * T) := by linarith [hlog T hT]
  have hb1 : 5 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 5 * C₂ * (1 + 8 * C₃) * T := by
    calc 5 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 5 * (C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N))) := by
          linarith [hpoly N hN1 T hT0.le]
      _ ≤ 5 * (C₂ * (T + 8 * (C₃ * T))) := by
          linarith only [mul_le_mul_of_nonneg_left hprod hC₂.le]
      _ = 5 * C₂ * (1 + 8 * C₃) * T := by ring
  have hb2 : 5 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * (Real.pi / 2 / (1 - σ) ^ 2)
      ≤ 45 * (Real.pi / 2 / (1 - σ) ^ 2) * T := by
    linarith only [mul_le_mul_of_nonneg_right hNa' hC₄.le]
  have hb3 : 5 * ((σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / 144) * T ≤ 5 * T := by
    have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 + 2 * σ)) := Real.rpow_nonneg hN0.le _
    have hB := bern_b2_factor_le hs0 h1 hT hpow0 hNneg2
    linarith only [mul_le_mul_of_nonneg_right hB hT0.le]
  have hb4 : 5 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (2 + σ + T) ^ 2 * (N : ℝ) ^ (-(4 + 2 * σ))
      / (2304 * (2 + σ) ^ 2)) * T ≤ 5 * T := by
    have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(4 + 2 * σ)) := Real.rpow_nonneg hN0.le _
    have hB := bern_error_factor_le hs0 h1 hT hpow0 hNneg
    linarith only [mul_le_mul_of_nonneg_right hB hT0.le]
  have hmain := integral_normSq_riemannZeta_le_aux_bern hs0 h1 hN1 hT0.le
  have hexp : (5 * C₂ * (1 + 8 * C₃) + 45 * (Real.pi / 2 / (1 - σ) ^ 2) + 45 / 4) * T
      = 5 * C₂ * (1 + 8 * C₃) * T + 45 * (Real.pi / 2 / (1 - σ) ^ 2) * T + 5 / 4 * T
        + 5 * T + 5 * T := by ring
  rw [hexp]
  linarith only [hmain, hb1, hb2, hb3, hb4]

/-! ## Two consequences: the first moment, and a large values estimate -/

/-- **The first moment of `ζ` on a vertical line with `4/7 < σ < 1` is `O(T)`.** -/
theorem exists_integral_norm_riemannZeta_le_four_sevenths {σ : ℝ} (h0 : 4 / 7 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) ≤ C * T := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_four_sevenths h0 h1
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

/-- **A large values estimate for `4/7 < σ < 1`.**  The set of `t ∈ (0, T]` at which
`‖ζ(σ + i t)‖ ≥ V` has measure `O(T / V²)`. -/
theorem exists_volume_norm_riemannZeta_ge_le_four_sevenths {σ : ℝ} (h0 : 4 / 7 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal ≤ C * T / V ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_four_sevenths h0 h1
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
