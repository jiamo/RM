/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareTrapezoid
import Mathlib.NumberTheory.ZetaValues

/-!
# The Euler–Maclaurin expansion to every order, and the mean square of `ζ` for `σ > 1/2`

`RiemannHypothesis.StripMeanSquare`, `RiemannHypothesis.StripMeanSquareTrapezoid` and
`RiemannHypothesis.StripMeanSquareBernoulli` prove `∫₀ᵀ ‖ζ(σ + i t)‖² dt = O_σ(T)` for
`σ > 2/3`, `σ > 3/5` and `σ > 4/7`: the balance points of the Euler–Maclaurin expansion carried
to order `0`, `1` and `2`.  This file carries the expansion to *every* order, and therefore
reaches the classical range of Bohr and Landau, `σ > 1/2`.

The engine is a single integration by parts, iterated.  With `bq m u = Bₘ(u)/m!` the scaled
Bernoulli polynomial, so that `bq (m+1)' = bq m`, and with `dfun m s` the `m`-th derivative of
`x ↦ x^(-s)`, the unit-interval remainder

`emTerm m a s = ∫_a^(a+1) bq m (x - a) · dfun m s x dx`

satisfies `emTerm m a s + emTerm (m+1) a s = bq (m+1) 1 · dfun m s (a+1) - bq (m+1) 0 · dfun m s a`
(`emTerm_add_emTerm_succ`).  For `m = 0` this identifies `emTerm 1 a s` with the error of the
trapezoid rule, and for `m ≥ 1` the two endpoint values of `bq (m+1)` agree, so summing over
`a = N+1, N+2, …` telescopes and expresses the tail of order `m` by the tail of order `m+1` plus
one explicit term (`emTail_succ`).  Since `‖emTerm m a s‖ = O_m(‖s‖^m a^(-σ-m))`, the tail of
order `m` is `O_m(‖s‖^m N^(1-σ-m))`, which for `N ≥ ‖s‖` beats every fixed power of `N`.

Balancing that against the off-diagonal term `N^(2-2σ)` of the mean value theorem for Dirichlet
polynomials, with `N ≍ T^(m/(σ+m-1))`, gives the mean square for `σ > (m+1)/(2m+1)`; letting
`m → ∞` gives every `σ > 1/2`.

## Main results

* `emTerm`, `emTail` : the unit-interval Euler–Maclaurin remainder of order `m`, and its tail.
* `emTerm_add_emTerm_succ` : the integration by parts step.
* `emTail_succ` : the recursion between consecutive orders.
* `exists_norm_riemannZeta_sub_dirichletPoly_le_em` : the Euler–Maclaurin bound of order `m` for
  `ζ` minus the truncated zeta sum on a vertical line inside the strip.
* `exists_integral_normSq_riemannZeta_le_half` : **the mean square theorem of Bohr and Landau**,
  `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C_σ T` for every `1/2 < σ < 1` and every `T ≥ 1`.
* `exists_integral_norm_riemannZeta_le_half`, `exists_volume_norm_riemannZeta_ge_le_half` : the
  first moment and the large values estimate in the same range.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace RiemannHypothesis

/-! ## The scaled Bernoulli polynomials -/

/-- The scaled Bernoulli polynomial `bq m u = Bₘ(u)/m!`, the Green's function of the
Euler–Maclaurin expansion of order `m`.  It satisfies `bq (m+1)' = bq m`. -/
def bq (m : ℕ) (u : ℝ) : ℝ := bernoulliFun m u / (Nat.factorial m : ℝ)

theorem bq_zero_eq (u : ℝ) : bq 0 u = 1 := by simp [bq]

theorem bq_one_eq (u : ℝ) : bq 1 u = u - 1 / 2 := by simp [bq]

/-- `bq (m+1)` is a primitive of `bq m`. -/
theorem hasDerivAt_bq (m : ℕ) (u : ℝ) : HasDerivAt (bq (m + 1)) (bq m u) u := by
  have h := (hasDerivAt_bernoulliFun (m + 1) u).div_const (((m + 1).factorial : ℝ))
  have heq : ((m + 1 : ℕ) : ℝ) * bernoulliFun ((m + 1) - 1) u / (((m + 1).factorial : ℝ))
      = bq m u := by
    have hfac : (((m + 1).factorial : ℝ)) = ((m : ℝ) + 1) * ((m.factorial : ℝ)) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfac0 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    simp only [Nat.add_sub_cancel, bq, hfac]
    push_cast
    field_simp
  rw [← heq]
  exact h

/-- Away from `m = 1` the scaled Bernoulli polynomial takes the same value at both endpoints of
the unit interval; this is what makes the Euler–Maclaurin boundary terms telescope. -/
theorem bq_endpoints {m : ℕ} (hm : m ≠ 1) : bq m 1 = bq m 0 := by
  simp [bq, bernoulliFun_endpoints_eq_of_ne_one hm]

theorem continuous_bq (m : ℕ) : Continuous (bq m) :=
  (Differentiable.continuous fun x => (hasDerivAt_bernoulliFun m x).differentiableAt).div_const _

/-- `bq m` is bounded on the unit interval. -/
theorem exists_bq_bound (m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, |bq m u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((continuous_bq m).continuousOn)
  refine ⟨|C| + 1, by positivity, fun u hu => ?_⟩
  have h := hC u hu
  simp only [Real.norm_eq_abs] at h
  linarith [le_abs_self C]

/-! ## The derivatives of `x ↦ x^(-s)` -/

/-- The rising factorial `s (s+1) ⋯ (s+m-1)`. -/
def poch (m : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.range m, (s + i)

theorem poch_succ (m : ℕ) (s : ℂ) : poch (m + 1) s = poch m s * (s + m) := by
  simp [poch, Finset.prod_range_succ]

theorem norm_poch_le (m : ℕ) (s : ℂ) : ‖poch m s‖ ≤ (‖s‖ + m) ^ m := by
  rw [poch, norm_prod]
  calc ∏ i ∈ Finset.range m, ‖s + (i : ℂ)‖
      ≤ ∏ _i ∈ Finset.range m, (‖s‖ + m) := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
        refine (norm_add_le _ _).trans ?_
        have : (i : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hi).le
        simp only [Complex.norm_natCast]
        linarith
    _ = (‖s‖ + m) ^ m := by simp

/-- The `m`-th derivative of `x ↦ x^(-s)`, namely `(-1)^m s(s+1)⋯(s+m-1) x^(-s-m)`. -/
def dfun (m : ℕ) (s : ℂ) (x : ℝ) : ℂ := (-1) ^ m * poch m s * (x : ℂ) ^ (-s - m)

theorem dfun_zero (s : ℂ) (x : ℝ) : dfun 0 s x = (x : ℂ) ^ (-s) := by simp [dfun, poch]

theorem hasDerivAt_dfun (m : ℕ) {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => dfun m s y) (dfun (m + 1) s x) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hrne : -s - (m : ℂ) ≠ 0 := by
    intro h
    have h2 : (-s - (m : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at h2
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h2 := (hasDerivAt_ofReal_cpow_const hxne hrne).const_mul ((-1 : ℂ) ^ m * poch m s)
  have key : dfun (m + 1) s x
      = (-1) ^ m * poch m s * ((-s - (m : ℂ)) * (x : ℂ) ^ (-s - (m : ℂ) - 1)) := by
    simp only [dfun, poch_succ]
    push_cast
    rw [show -s - ((m : ℂ) + 1) = -s - (m : ℂ) - 1 by ring]
    ring
  rw [key]
  exact h2

theorem norm_dfun (m : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖dfun m s x‖ = ‖poch m s‖ * x ^ (-s.re - m) := by
  simp only [dfun, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-! ## The unit-interval remainder and the integration by parts step -/

/-- The Euler–Maclaurin remainder of order `m` on the unit interval `[a, a+1]`. -/
def emTerm (m : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∫ x in a..(a + 1), (bq m (x - a) : ℂ) * dfun m s x

theorem continuousOn_emIntegrand (m : ℕ) {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => (bq m (x - a) : ℂ) * dfun m s x) (Set.uIcc a (a + 1)) := by
  rw [Set.uIcc_of_le (by linarith)]
  refine ContinuousOn.mul ?_ fun x hx => ?_
  · exact (Complex.continuous_ofReal.comp
      ((continuous_bq m).comp (continuous_id.sub continuous_const))).continuousOn
  · exact ((hasDerivAt_dfun m hs (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt

/-- **The integration by parts step of the Euler–Maclaurin expansion.** -/
theorem emTerm_add_emTerm_succ (m : ℕ) {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    emTerm m a s + emTerm (m + 1) a s
      = (bq (m + 1) 1 : ℂ) * dfun m s (a + 1) - (bq (m + 1) 0 : ℂ) * dfun m s a := by
  have hderiv : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => (bq (m + 1) (y - a) : ℂ) * dfun m s y)
        ((bq m (x - a) : ℂ) * dfun m s x + (bq (m + 1) (x - a) : ℂ) * dfun (m + 1) s x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 : HasDerivAt (fun y : ℝ => bq (m + 1) (y - a)) (bq m (x - a)) x :=
      HasDerivAt.comp_sub_const x a (hasDerivAt_bq m (x - a))
    exact h1.ofReal_comp.mul (hasDerivAt_dfun m hs hx0)
  have hi1 : IntervalIntegrable (fun x : ℝ => (bq m (x - a) : ℂ) * dfun m s x) volume a (a + 1) :=
    (continuousOn_emIntegrand m hs ha).intervalIntegrable
  have hi2 : IntervalIntegrable
      (fun x : ℝ => (bq (m + 1) (x - a) : ℂ) * dfun (m + 1) s x) volume a (a + 1) :=
    (continuousOn_emIntegrand (m + 1) hs ha).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hftc
  simpa [emTerm, sub_self] using hftc

/-- The remainder of order `0` is the integral itself. -/
theorem emTerm_zero_eq (a : ℝ) (ha : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    emTerm 0 a s = (((a + 1 : ℝ) : ℂ) ^ (1 - s) - ((a : ℝ) : ℂ) ^ (1 - s)) / (1 - s) := by
  have h : emTerm 0 a s = ∫ x in a..(a + 1), (x : ℂ) ^ (-s) := by
    simp [emTerm, bq_zero_eq, dfun_zero]
  rw [h, integral_cpow_neg ha (by linarith) hs1]

/-- The remainder of order `1` is the error of the trapezoid rule. -/
theorem emTerm_one_eq_trapTerm (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    emTerm 1 ((n : ℝ) + 1) s = trapTerm n s := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hstep := emTerm_add_emTerm_succ 0 hs0 ha
  rw [emTerm_zero_eq _ ha hs1] at hstep
  have hb1 : bq 1 1 = 1 / 2 := by rw [bq_one_eq]; norm_num
  have hb0 : bq 1 0 = -(1 / 2) := by rw [bq_one_eq]; norm_num
  rw [hb1, hb0, dfun_zero, dfun_zero] at hstep
  have hcast : (((n : ℝ) + 1 + 1 : ℝ) : ℂ) = ((n + 2 : ℝ) : ℂ) := by push_cast; ring
  have hcast2 : (((n : ℝ) + 1 : ℝ) : ℂ) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, hcast2] at hstep
  have hne : (1 - s : ℂ) ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hne' : (s - 1 : ℂ) ≠ 0 := fun h => hs1 (by linear_combination h)
  rw [trapTerm, eulerTerm]
  push_cast at hstep ⊢
  field_simp at hstep ⊢
  linear_combination -hstep

/-- The size of the remainder of order `m`. -/
theorem norm_emTerm_le (m : ℕ) {C : ℝ} (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, |bq m u| ≤ C)
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖emTerm m a s‖ ≤ C * ‖poch m s‖ * a ^ (-s.re - (m : ℝ)) := by
  have hbd : ∀ x ∈ Set.uIoc a (a + 1),
      ‖(bq m (x - a) : ℂ) * dfun m s x‖ ≤ C * ‖poch m s‖ * a ^ (-s.re - (m : ℝ)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1.le
    have hmem : x - a ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hb : ‖(bq m (x - a) : ℂ)‖ ≤ C := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC _ hmem
    have hd : ‖dfun m s x‖ ≤ ‖poch m s‖ * a ^ (-s.re - (m : ℝ)) := by
      rw [norm_dfun m s hx0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine Real.rpow_le_rpow_of_nonpos ha hx.1.le ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [norm_mul]
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hb
    calc ‖(bq m (x - a) : ℂ)‖ * ‖dfun m s x‖
        ≤ C * (‖poch m s‖ * a ^ (-s.re - (m : ℝ))) :=
          mul_le_mul hb hd (norm_nonneg _) hC0
      _ = C * ‖poch m s‖ * a ^ (-s.re - (m : ℝ)) := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |a + 1 - a| = 1 by rw [show a + 1 - a = (1 : ℝ) by ring]; norm_num, mul_one] at h
  exact h

/-! ## The tail of the expansion -/

/-- The tail of the Euler–Maclaurin expansion of order `m`, over the unit intervals
`[N+1, N+2], [N+2, N+3], …`. -/
def emTail (m N : ℕ) (s : ℂ) : ℂ := ∑' n : ℕ, emTerm m (((n + N : ℕ) : ℝ) + 1) s

theorem norm_emTerm_shift_le (m : ℕ) {C : ℝ} (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, |bq m u| ≤ C)
    {s : ℂ} (hs0 : 0 < s.re) (N n : ℕ) :
    ‖emTerm m (((n + N : ℕ) : ℝ) + 1) s‖
      ≤ C * ‖poch m s‖ * ((((n + N : ℕ) : ℝ) + 1) ^ (-(s.re + (m : ℝ)))) := by
  have h := norm_emTerm_le m hC hs0 (a := ((n + N : ℕ) : ℝ) + 1) (by positivity)
  rwa [show -s.re - (m : ℝ) = -(s.re + (m : ℝ)) by ring] at h

theorem summable_emTerm_shift (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) :
    Summable fun n : ℕ => emTerm m (((n + N : ℕ) : ℝ) + 1) s := by
  obtain ⟨C, _, hC⟩ := exists_bq_bound m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsum : Summable fun n : ℕ => ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) :=
    (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (p := s.re + (m : ℝ)) (by linarith))
  exact Summable.of_norm_bounded (hsum.mul_left (C * ‖poch m s‖))
    fun n => norm_emTerm_shift_le m hC hs0 N n

/-- The size of the tail of order `m`. -/
theorem norm_emTail_le (m : ℕ) (hm : 1 ≤ m) {C : ℝ} (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, |bq m u| ≤ C)
    {s : ℂ} (hs0 : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖emTail m N s‖
      ≤ C * ‖poch m s‖ * ((N : ℝ) ^ (1 - (s.re + (m : ℝ))) / ((s.re + (m : ℝ)) - 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 (by norm_num))
  have hsum : Summable fun n : ℕ => ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) :=
    (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (p := s.re + (m : ℝ)) (by linarith))
  have hbd := fun n : ℕ => norm_emTerm_shift_le m hC hs0 N n
  have hnorms : Summable fun n : ℕ => ‖emTerm m (((n + N : ℕ) : ℝ) + 1) s‖ :=
    (hsum.mul_left (C * ‖poch m s‖)).of_nonneg_of_le (fun n => norm_nonneg _) hbd
  have htail : ∑' n : ℕ, ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ)))
      ≤ (N : ℝ) ^ (1 - (s.re + (m : ℝ))) / ((s.re + (m : ℝ)) - 1) :=
    tsum_shift_rpow_neg_le_rpow (by linarith) hN
  have hpos : (0 : ℝ) ≤ ∑' n : ℕ, ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  calc ‖emTail m N s‖ ≤ ∑' n : ℕ, ‖emTerm m (((n + N : ℕ) : ℝ) + 1) s‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, C * ‖poch m s‖ * ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) :=
        hnorms.tsum_le_tsum hbd (hsum.mul_left _)
    _ = C * ‖poch m s‖ * ∑' n : ℕ, ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) := tsum_mul_left
    _ ≤ C * ‖poch m s‖ * ((N : ℝ) ^ (1 - (s.re + (m : ℝ))) / ((s.re + (m : ℝ)) - 1)) := by
        refine mul_le_mul_of_nonneg_left htail (by positivity)

/-- **The recursion between consecutive orders**: the tail of order `m` is one explicit term
plus the tail of order `m + 1`. -/
theorem emTail_succ (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) :
    emTail m N s = -(bq (m + 1) 0 : ℂ) * dfun m s ((N : ℝ) + 1) - emTail (m + 1) N s := by
  set g : ℕ → ℂ := fun n => dfun m s (((n + N : ℕ) : ℝ) + 1) with hg
  have hb : bq (m + 1) 1 = bq (m + 1) 0 := bq_endpoints (by omega)
  have hstep : ∀ n : ℕ, emTerm m (((n + N : ℕ) : ℝ) + 1) s
      + emTerm (m + 1) (((n + N : ℕ) : ℝ) + 1) s = (bq (m + 1) 0 : ℂ) * (g (n + 1) - g n) := by
    intro n
    have h := emTerm_add_emTerm_succ m hs0 (a := ((n + N : ℕ) : ℝ) + 1) (by positivity)
    have hcast : (((n + N : ℕ) : ℝ) + 1 + 1) = (((n + 1 + N : ℕ) : ℝ) + 1) := by push_cast; ring
    rw [hb, hcast] at h
    rw [h, hg]
    ring
  have hsg : Summable g := by
    obtain ⟨C, _, hC⟩ := exists_bq_bound m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hsum : Summable fun n : ℕ => ((((n + N : ℕ)) : ℝ) + 1) ^ (-(s.re + (m : ℝ))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (p := s.re + (m : ℝ)) (by linarith))
    refine Summable.of_norm_bounded (hsum.mul_left ‖poch m s‖) fun n => ?_
    rw [hg]
    simp only
    rw [norm_dfun m s (by positivity), show -s.re - (m : ℝ) = -(s.re + (m : ℝ)) by ring]
  have hgs : Summable fun n : ℕ => g (n + 1) := (summable_nat_add_iff 1).2 hsg
  have hsub : Summable fun n : ℕ => g n - g (n + 1) := hsg.sub hgs
  have hzero : Filter.Tendsto g Filter.atTop (nhds 0) := hsg.tendsto_atTop_zero
  have hpartial : ∀ k : ℕ, ∑ i ∈ Finset.range k, (g i - g (i + 1)) = g 0 - g k :=
    fun k => Finset.sum_range_sub' g k
  have hlim : Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, (g i - g (i + 1)))
      Filter.atTop (nhds (g 0)) := by
    have := (tendsto_const_nhds (x := g 0) (f := Filter.atTop (α := ℕ))).sub hzero
    simpa [hpartial] using this
  have htel : ∑' n : ℕ, (g n - g (n + 1)) = g 0 :=
    ((hsub.hasSum_iff_tendsto_nat).2 hlim).tsum_eq
  have hsum1 := summable_emTerm_shift m hm hs0 N
  have hsum2 := summable_emTerm_shift (m + 1) (by omega) hs0 N
  have hadd : emTail m N s + emTail (m + 1) N s
      = ∑' n : ℕ, (bq (m + 1) 0 : ℂ) * (g (n + 1) - g n) := by
    rw [emTail, emTail, ← hsum1.tsum_add hsum2]
    exact tsum_congr hstep
  have hneg : ∑' n : ℕ, (bq (m + 1) 0 : ℂ) * (g (n + 1) - g n)
      = -((bq (m + 1) 0 : ℂ) * g 0) := by
    have : ∑' n : ℕ, (bq (m + 1) 0 : ℂ) * (g (n + 1) - g n)
        = (bq (m + 1) 0 : ℂ) * ∑' n : ℕ, (g (n + 1) - g n) := tsum_mul_left
    rw [this]
    have hneg2 : ∑' n : ℕ, (g (n + 1) - g n) = -∑' n : ℕ, (g n - g (n + 1)) := by
      rw [← tsum_neg]
      exact tsum_congr fun n => by ring
    rw [hneg2, htel]
    ring
  have hg0 : g 0 = dfun m s ((N : ℝ) + 1) := by rw [hg]; norm_num
  rw [hneg, hg0] at hadd
  linear_combination hadd

/-! ## The Euler–Maclaurin bound of order `m` -/

/-- For `N` at least `‖s‖` the explicit term of the recursion is `O_m(N^(-σ))`, uniformly in the
order `m`’s dependence on `s`. -/
theorem norm_dfun_shift_le (m : ℕ) {s : ℂ} (hs0 : 0 < s.re) {N : ℕ} (hN : 1 ≤ N)
    (hsN : ‖s‖ ≤ (N : ℝ)) :
    ‖dfun m s ((N : ℝ) + 1)‖ ≤ ((1 : ℝ) + m) ^ m * (N : ℝ) ^ (-s.re) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [norm_dfun m s (by positivity)]
  have hp : ‖poch m s‖ ≤ (N : ℝ) ^ m * ((1 : ℝ) + m) ^ m := by
    refine (norm_poch_le m s).trans ?_
    have hstep : ‖s‖ + (m : ℝ) ≤ (N : ℝ) * (1 + m) := by
      have : (m : ℝ) ≤ (N : ℝ) * (m : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      nlinarith
    calc (‖s‖ + (m : ℝ)) ^ m ≤ ((N : ℝ) * (1 + m)) ^ m :=
          pow_le_pow_left₀ (by positivity) hstep m
      _ = (N : ℝ) ^ m * ((1 : ℝ) + m) ^ m := by rw [mul_pow]
  have hr : ((N : ℝ) + 1) ^ (-s.re - (m : ℝ)) ≤ (N : ℝ) ^ (-s.re - (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos hN0 (by linarith) ?_
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrpos : (0 : ℝ) < ((N : ℝ) + 1) ^ (-s.re - (m : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hcomb : ‖poch m s‖ * ((N : ℝ) + 1) ^ (-s.re - (m : ℝ))
      ≤ ((N : ℝ) ^ m * ((1 : ℝ) + m) ^ m) * (N : ℝ) ^ (-s.re - (m : ℝ)) :=
    mul_le_mul hp hr hrpos.le (by positivity)
  refine hcomb.trans_eq ?_
  have hnpow : (N : ℝ) ^ m = (N : ℝ) ^ (m : ℝ) := (Real.rpow_natCast (N : ℝ) m).symm
  rw [hnpow, mul_comm ((N : ℝ) ^ (m : ℝ)) (((1 : ℝ) + m) ^ m), mul_assoc,
    ← Real.rpow_add hN0]
  ring_nf

/-- **Iterating the recursion.**  Up to `O_m(N^(-σ))` the tail of order `1` is the tail of order
`m`, provided the length `N` is at least `‖s‖`. -/
theorem exists_norm_emTail_one_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N → ‖s‖ ≤ (N : ℝ) →
      ‖emTail 1 N s‖ ≤ C * (N : ℝ) ^ (-s.re) + ‖emTail m N s‖ := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨1, one_pos, fun s hs N hN hsN => ?_⟩
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have : (0 : ℝ) < (N : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hN0 _
    linarith
  | succ k hk ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨C + |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k, by positivity, fun s hs N hN hsN => ?_⟩
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hrpos : (0 : ℝ) < (N : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hN0 _
    have h1 := hC s hs N hN hsN
    have hterm : ‖-(bq (k + 1) 0 : ℂ) * dfun k s ((N : ℝ) + 1)‖
        ≤ |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k * (N : ℝ) ^ (-s.re) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      calc |bq (k + 1) 0| * ‖dfun k s ((N : ℝ) + 1)‖
          ≤ |bq (k + 1) 0| * (((1 : ℝ) + k) ^ k * (N : ℝ) ^ (-s.re)) :=
            mul_le_mul_of_nonneg_left (norm_dfun_shift_le k hs hN hsN) (abs_nonneg _)
        _ = |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k * (N : ℝ) ^ (-s.re) := by ring
    have h2 : ‖emTail k N s‖
        ≤ |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k * (N : ℝ) ^ (-s.re) + ‖emTail (k + 1) N s‖ := by
      rw [emTail_succ k hk hs N]
      have := norm_sub_le (-(bq (k + 1) 0 : ℂ) * dfun k s ((N : ℝ) + 1)) (emTail (k + 1) N s)
      linarith
    have hring : (C + |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k) * (N : ℝ) ^ (-s.re)
        = C * (N : ℝ) ^ (-s.re) + |bq (k + 1) 0| * ((1 : ℝ) + k) ^ k * (N : ℝ) ^ (-s.re) := by
      ring
    rw [hring]
    linarith

/-- The tail of order `1` is the tail of the trapezoidal expansion of
`RiemannHypothesis.StripMeanSquareTrapezoid`. -/
theorem emTail_one_eq_tsum_trapTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    emTail 1 N s = ∑' n : ℕ, trapTerm (n + N) s := by
  refine tsum_congr fun n => ?_
  have h := emTerm_one_eq_trapTerm (n + N) hs0 hs1
  exact h

/-- **The Euler–Maclaurin bound of order `m`** for the difference between `ζ` and the truncated
zeta sum on a vertical line inside the strip.  Compared with the expansions of order `0`, `1`
and `2`, the last term is `O_m(‖s‖^m N^(1-σ-m))`: an arbitrary power of `N` is gained. -/
theorem exists_norm_riemannZeta_sub_dirichletPoly_le_em (m : ℕ) (hm : 1 ≤ m) {σ : ℝ}
    (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨C₁, hC₁, hC₁bd⟩ := exists_norm_emTail_one_le m hm
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bq_bound m
  refine ⟨max (C₁ + 1) (Cb / (σ + (m : ℝ) - 1)), lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun N hN t htN => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hnorm_s : ‖s‖ ≤ σ + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_pos h0] at h
    exact h
  have hsN : ‖s‖ ≤ (N : ℝ) := le_trans hnorm_s htN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [riemannZeta_eq_trapApprox N hs0 hs1, ← dirichletPoly_one N s,
    ← emTail_one_eq_tsum_trapTerm hs0 hs1 N]
  have hsplit : dirichletPoly (fun _ => 1) N s + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s - dirichletPoly (fun _ => 1) N s
      = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        + (((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s) := by ring
  rw [hsplit]
  -- the three pieces
  have hpole : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ = ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  have hhalf : ‖((N + 1 : ℝ) : ℂ) ^ (-s) / 2‖ ≤ (N : ℝ) ^ (-σ) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hmono : ((N : ℝ) + 1) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
    simp only [hre, Complex.neg_re, Complex.norm_ofNat]
    linarith
  have htailm : ‖emTail m N s‖
      ≤ Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
    have h := norm_emTail_le m hm hCb hs0 hN
    rw [hre] at h
    refine h.trans ?_
    have hpoch : ‖poch m s‖ ≤ (σ + |t| + m) ^ m := by
      refine (norm_poch_le m s).trans ?_
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hexp : (N : ℝ) ^ (1 - (σ + (m : ℝ))) = (N : ℝ) ^ (1 - σ - (m : ℝ)) := by ring_nf
    have hden : (0 : ℝ) < σ + (m : ℝ) - 1 := by linarith
    have hrp : (0 : ℝ) < (N : ℝ) ^ (1 - σ - (m : ℝ)) := Real.rpow_pos_of_pos hN0 _
    rw [hexp]
    have hRD : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1) := by positivity
    have hstep1 : Cb * ‖poch m s‖ * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1))
        ≤ Cb * (σ + |t| + m) ^ m * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoch hCb0.le) hRD
    have hstep2 : Cb * (σ + |t| + m) ^ m * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1))
        = Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
      field_simp
    linarith
  have htail1 : ‖emTail 1 N s‖
      ≤ C₁ * (N : ℝ) ^ (-σ)
        + Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
    have h := hC₁bd s hs0 N hN hsN
    rw [hre] at h
    linarith
  have hA : (0 : ℝ) < (N : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hN0 _
  have hB : (0 : ℝ) ≤ (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)) := by positivity
  have hmax1 : C₁ + 1 ≤ max (C₁ + 1) (Cb / (σ + (m : ℝ) - 1)) := le_max_left _ _
  have hmax2 : Cb / (σ + (m : ℝ) - 1) ≤ max (C₁ + 1) (Cb / (σ + (m : ℝ) - 1)) := le_max_right _ _
  have hfinal := norm_add_le (((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1))
    (((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s)
  have hsecond : ‖((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s‖
      ≤ (N : ℝ) ^ (-σ) + (C₁ * (N : ℝ) ^ (-σ)
        + Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)))) :=
    (norm_add_le _ _).trans (add_le_add hhalf htail1)
  rw [hpole] at hfinal
  nlinarith [hfinal, hsecond, hA, hB, hmax1, hmax2]

/-! ## The mean square of `ζ` for every `σ > 1/2` -/

/-- The pointwise bound behind the Bohr–Landau mean square estimate: the Euler–Maclaurin
error of order `m`, squared. -/
theorem normSq_riemannZeta_le_pointwise_em {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)))
        + 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ))
        + 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set P : ℂ := dirichletPoly (fun _ => 1) N s with hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have habs : |t| = t := abs_of_nonneg ht0
  have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    simp [Complex.normSq_apply]
    ring
  have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
    have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
    nlinarith [norm_nonneg (s - 1), hnormsq]
  have hbdt := hbd N hN t (by rw [habs]; linarith)
  set A : ℝ := (N : ℝ) ^ (-σ) with hA
  set B : ℝ := (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)) with hB
  set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
  have hA0 : 0 ≤ A := Real.rpow_nonneg hN0.le _
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : (0 : ℝ) ≤ σ + |t| + m := by positivity
    positivity
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + E1 + C * (A + B) := by
    have := norm_sub_norm_le (riemannZeta s) P
    linarith [hbdt]
  have hCAB : 0 ≤ C * (A + B) := by positivity
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ 3 * (‖P‖ ^ 2 + E1 ^ 2 + (C * (A + B)) ^ 2) := by
    nlinarith [norm_nonneg (riemannZeta s), norm_nonneg P, hE10, hCAB, htri,
      sq_nonneg (‖P‖ - E1), sq_nonneg (‖P‖ - C * (A + B)), sq_nonneg (E1 - C * (A + B))]
  have hE1sq : E1 ^ 2 = ((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    rw [hE1, div_pow, hnormsq, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hAsq : A ^ 2 = (N : ℝ) ^ (-(2 * σ)) := by
    rw [hA, ← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hBsq : B ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
    have hpow : ((N : ℝ) ^ (1 - σ - (m : ℝ))) ^ 2 = (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 - σ - (m : ℝ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have hbase : σ + |t| + m ≤ σ + T + m := by rw [habs]; linarith
    have hb0 : (0 : ℝ) ≤ σ + |t| + m := by positivity
    have hmono : ((σ + |t| + m) ^ m) ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hb0 hbase m) 2
    rw [hB, mul_pow, hpow]
    have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
    exact mul_le_mul_of_nonneg_right hmono hrp
  have hprod : (C * (A + B)) ^ 2 ≤ 2 * C ^ 2 * (A ^ 2 + B ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg (A - B))]
  have h6 : (0 : ℝ) ≤ 6 * C ^ 2 := by positivity
  have hA2 : 6 * C ^ 2 * A ^ 2 = 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) := by rw [hAsq]
  have hB2 : 6 * C ^ 2 * B ^ 2
      ≤ 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left hBsq h6
  linarith [hsq, hE1sq, hprod, hA2, hB2]

/-- The mean square of `ζ` on `[0, T]`, in terms of the length `N` of the Dirichlet polynomial,
with the Euler–Maclaurin error of order `m`. -/
theorem integral_normSq_riemannZeta_le_aux_em {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2)
        + 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T
        + 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set D : ℝ := 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) with hD
  set E : ℝ := 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) with hE
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hzetaC := continuous_normSq_riemannZeta_line_of_lt_one (σ := σ) h1
  have hPC := continuous_normSq_dirichletPoly_line (σ := σ) N
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    ((hPC.const_smul (3 : ℝ)).congr fun t => by simp [smul_eq_mul]).intervalIntegrable 0 T
  have hcont2 : Continuous (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) :=
    continuous_const.mul (continuous_const.mul
      (Continuous.div continuous_const (by fun_prop) fun t => by
        have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by
          have : (0 : ℝ) < (1 - σ) ^ 2 := pow_pos (by linarith) 2
          nlinarith [sq_nonneg t]
        exact ne_of_gt hpos))
  have hi2 : IntervalIntegrable (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) volume 0 T :=
    hcont2.intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => D) volume 0 T := intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun _ : ℝ => E) volume 0 T := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hzetaC.intervalIntegrable 0 T)
    (((hi1.add hi2).add hi3).add hi4)
    (fun t ht => normSq_riemannZeta_le_pointwise_em h0 h1 hC hbd hN ht.1 ht.2 hTN)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hφ : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero]
  nlinarith [hφ, hA0]

set_option maxHeartbeats 1000000 in
-- the proof is a long chain of `calc` estimates and needs more than the default budget
/-- **The Bohr–Landau mean square: for every `1/2 < σ < 1` the mean square of `ζ` on the
vertical line of abscissa `σ` is `O(T)`.**

This is the limit of the family `exists_integral_normSq_riemannZeta_le_three_fifths`,
`exists_integral_normSq_riemannZeta_le_four_sevenths`: taking the Euler–Maclaurin expansion to
order `m` the tail is `O_m(‖s‖^m N^(1-σ-m))`, so the Dirichlet polynomial may be taken of length
`N ≍ T^e` with `e = m/(σ+m-1)`, and the balance condition `e (2-2σ) < 1` reads
`σ > (m+1)/(2m+1)`, which is satisfied by some `m` as soon as `σ > 1/2`. -/
theorem exists_integral_normSq_riemannZeta_le_half {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have h1s : (0 : ℝ) < 1 - σ := by linarith
  have h2s : (0 : ℝ) < 2 * σ - 1 := by linarith
  -- the order of the expansion
  set m : ℕ := ⌈(1 - σ) / (2 * σ - 1)⌉₊ + 1 with hm_def
  have hm : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmgt : (1 - σ) / (2 * σ - 1) < (m : ℝ) := by
    have h := Nat.le_ceil ((1 - σ) / (2 * σ - 1))
    have hcast : ((⌈(1 - σ) / (2 * σ - 1)⌉₊ : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [hm_def]; push_cast; ring
    linarith
  have hkey0 : 1 - σ < (m : ℝ) * (2 * σ - 1) := by
    rw [div_lt_iff₀ h2s] at hmgt
    linarith
  -- the exponent
  have hden : (0 : ℝ) < σ + (m : ℝ) - 1 := by linarith
  set e : ℝ := (m : ℝ) / (σ + (m : ℝ) - 1) with he_def
  have he1 : (1 : ℝ) ≤ e := by
    rw [he_def, le_div_iff₀ hden]; linarith
  have he0 : (0 : ℝ) < e := by linarith
  set a : ℝ := e * (2 - 2 * σ) with ha_def
  have ha1 : a < 1 := by
    rw [ha_def, he_def, div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  have ha0 : (0 : ℝ) < a := by rw [ha_def]; exact mul_pos he0 (by linarith)
  have hkey : e * (2 - 2 * σ - 2 * (m : ℝ)) = -(2 * (m : ℝ)) := by
    rw [he_def]
    field_simp
    ring
  -- the ingredients
  obtain ⟨Cem, hCem, hembd⟩ := exists_norm_riemannZeta_sub_dirichletPoly_le_em m hm hs0 h1
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le h0 h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  have hC₄ : (0 : ℝ) < Real.pi / 2 / (1 - σ) ^ 2 := div_pos (by positivity) (pow_pos h1s 2)
  set L : ℝ := Real.log 6 with hL_def
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by norm_num)
  set K : ℝ := 36 * (1 + L + e) * C₃ with hK_def
  have hK0 : (0 : ℝ) ≤ K :=
    mul_nonneg (by nlinarith) hC₃.le
  refine ⟨3 * C₂ * (1 + K) + 108 * (Real.pi / 2 / (1 - σ) ^ 2) + 6 * Cem ^ 2
      + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2, ?_, fun T hT => ?_⟩
  · have h1 : (0 : ℝ) < 3 * C₂ * (1 + K) := by nlinarith
    have h2 : (0 : ℝ) < 108 * (Real.pi / 2 / (1 - σ) ^ 2) := by linarith
    have h3 : (0 : ℝ) < 6 * Cem ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 := by positivity
    linarith
  -- fix `T`
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  set x : ℝ := T ^ e with hx_def
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hT he0.le
  have hx0 : (0 : ℝ) < x := by linarith
  have hTx : T ≤ x := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le hT he1
  set N : ℕ := ⌈x⌉₊ + ⌈T⌉₊ + 1 with hN_def
  have hN1 : 1 ≤ N := by omega
  have hNcast : (N : ℝ) = (⌈x⌉₊ : ℝ) + (⌈T⌉₊ : ℝ) + 1 := by rw [hN_def]; push_cast; ring
  have hNx : x ≤ (N : ℝ) := by
    have h := Nat.le_ceil x
    have hpos : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hNT : σ + T ≤ (N : ℝ) := by
    have h := Nat.le_ceil T
    have hpos : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hN5 : (N : ℝ) + 1 ≤ 6 * x := by
    have h1' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have h2' : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    rw [hNcast]
    nlinarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- powers of `N`
  have hxa : x ^ (2 - 2 * σ) = T ^ a := by
    rw [hx_def, ← Real.rpow_mul hT0.le, ha_def]
  have h6pow : (6 : ℝ) ^ (2 - 2 * σ) ≤ 36 := by
    calc (6 : ℝ) ^ (2 - 2 * σ) ≤ (6 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 36 := by norm_num
  have hTa : T ^ a ≤ T := by
    calc T ^ a ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha1.le
      _ = T := Real.rpow_one T
  have hTa0 : (0 : ℝ) ≤ T ^ a := Real.rpow_nonneg hT0.le _
  have hNp1a : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 36 * T ^ a := by
    have h2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ (6 * x) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by linarith) hN5 (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    linarith only [h2, mul_le_mul_of_nonneg_right h6pow hTa0]
  have hNa : (N : ℝ) ^ (2 - 2 * σ) ≤ 36 * T ^ a := by
    have h2 : (N : ℝ) ^ (2 - 2 * σ) ≤ ((N : ℝ) + 1) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
    linarith only [h2, hNp1a]
  have hNlog : Real.log N ≤ L + e * Real.log T := by
    have hle : Real.log N ≤ Real.log (6 * x) := Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), hx_def, Real.log_rpow hT0] at hle
    linarith only [hle]
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
  have hNprod : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ K * T := by
    have hLlog : (0 : ℝ) ≤ L * Real.log T := mul_nonneg hL0 hlogT
    have hexpand : (1 + L + e) * (1 + Real.log T)
        = 1 + Real.log T + L + L * Real.log T + e + e * Real.log T := by ring
    have hstep : 1 + Real.log N ≤ (1 + L + e) * (1 + Real.log T) := by
      rw [hexpand]
      linarith only [hNlog, hLlog, hlogT, he0]
    have hNpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)
        ≤ 36 * T ^ a * ((1 + L + e) * (1 + Real.log T)) :=
          mul_le_mul hNa hstep (by linarith) (by linarith [hTa0])
      _ = 36 * (1 + L + e) * (T ^ a * (1 + Real.log T)) := by ring
      _ ≤ 36 * (1 + L + e) * (C₃ * T) :=
          mul_le_mul_of_nonneg_left (hlog T hT) (by linarith)
      _ = K * T := by rw [hK_def]; ring
  -- the negative powers of `N`
  have hNneg : (N : ℝ) ^ (-(2 * σ)) ≤ 1 := by
    have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := (N : ℝ)) (by norm_num) hN1'
      (by linarith : -(2 * σ) ≤ 0)
    simpa using this
  have hNm : (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ T ^ (-(2 * (m : ℝ))) := by
    have hexp : 2 - 2 * σ - 2 * (m : ℝ) ≤ 0 := by linarith
    have h2 : (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ x ^ (2 - 2 * σ - 2 * (m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hNx hexp
    rwa [hx_def, ← Real.rpow_mul hT0.le, hkey] at h2
  have hTm2 : ((T : ℝ) ^ m) ^ 2 = T ^ (2 * (m : ℝ)) := by
    rw [← Real.rpow_natCast T m, ← Real.rpow_natCast (T ^ (m : ℝ)) 2, ← Real.rpow_mul hT0.le]
    ring_nf
  have hbig : ((σ + T + (m : ℝ)) ^ m) ^ 2 ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ)) := by
    have hbase : σ + T + (m : ℝ) ≤ (2 + (m : ℝ)) * T := by
      nlinarith [mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ (m : ℝ) by linarith)]
    have hb0 : (0 : ℝ) ≤ σ + T + (m : ℝ) := by positivity
    have hp := pow_le_pow_left₀ hb0 hbase m
    rw [mul_pow] at hp
    have hsq : ((σ + T + (m : ℝ)) ^ m) ^ 2 ≤ ((2 + (m : ℝ)) ^ m * T ^ m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp 2
    rw [mul_pow, hTm2] at hsq
    exact hsq
  have herr : ((σ + T + (m : ℝ)) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))
      ≤ ((2 + (m : ℝ)) ^ m) ^ 2 := by
    have hnn1 : (0 : ℝ) ≤ ((σ + T + (m : ℝ)) ^ m) ^ 2 := sq_nonneg _
    have hnn2 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
    have hTmpos : (0 : ℝ) < T ^ (2 * (m : ℝ)) := Real.rpow_pos_of_pos hT0 _
    have hcancel : T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ))) = 1 := by
      rw [← Real.rpow_add hT0]
      norm_num
    calc ((σ + T + (m : ℝ)) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))
        ≤ (((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ))) * T ^ (-(2 * (m : ℝ))) :=
          mul_le_mul hbig hNm hnn2 (by positivity)
      _ = ((2 + (m : ℝ)) ^ m) ^ 2 * (T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ)))) := by ring
      _ = ((2 + (m : ℝ)) ^ m) ^ 2 := by rw [hcancel, mul_one]
  -- assemble
  have hmain := integral_normSq_riemannZeta_le_aux_em (m := m) (C := Cem) hs0 h1 hCem.le hembd
    hN1 hT0.le hNT
  have hb1 : 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * C₂ * (1 + K) * T := by
    calc 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 3 * (C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N))) := by
          linarith only [hpoly N hN1 T hT0.le]
      _ ≤ 3 * (C₂ * (T + K * T)) := by
          linarith only [mul_le_mul_of_nonneg_left hNprod hC₂.le]
      _ = 3 * C₂ * (1 + K) * T := by ring
  have hb2 : 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * (Real.pi / 2 / (1 - σ) ^ 2)
      ≤ 108 * (Real.pi / 2 / (1 - σ) ^ 2) * T := by
    have h36 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 36 * T := by linarith only [hNp1a, hTa]
    linarith only [mul_le_mul_of_nonneg_right h36 hC₄.le]
  have hb3 : 6 * Cem ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T ≤ 6 * Cem ^ 2 * T := by
    have hnn : (0 : ℝ) ≤ 6 * Cem ^ 2 * T := by positivity
    linarith only [mul_le_mul_of_nonneg_left hNneg hnn]
  have hb4 : 6 * Cem ^ 2 * (((σ + T + (m : ℝ)) ^ m) ^ 2
        * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T
      ≤ 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T := by
    have hnn : (0 : ℝ) ≤ 6 * Cem ^ 2 * T := by positivity
    linarith only [mul_le_mul_of_nonneg_left herr hnn]
  have hexp : (3 * C₂ * (1 + K) + 108 * (Real.pi / 2 / (1 - σ) ^ 2) + 6 * Cem ^ 2
      + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2) * T
      = 3 * C₂ * (1 + K) * T + 108 * (Real.pi / 2 / (1 - σ) ^ 2) * T + 6 * Cem ^ 2 * T
        + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T := by ring
  rw [hexp]
  linarith only [hmain, hb1, hb2, hb3, hb4]

/-! ## Two consequences: the first moment, and a large values estimate -/

/-- **The first moment of `ζ` on a vertical line with `1/2 < σ < 1` is `O(T)`.** -/
theorem exists_integral_norm_riemannZeta_le_half {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) ≤ C * T := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_half h0 h1
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

/-- **A large values estimate for every `1/2 < σ < 1`.**  The set of `t ∈ (0, T]` at which
`‖ζ(σ + i t)‖ ≥ V` has measure `O(T / V²)`. -/
theorem exists_volume_norm_riemannZeta_ge_le_half {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal ≤ C * T / V ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_half h0 h1
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
