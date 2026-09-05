/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDifferenceTheorem
import RiemannHypothesis.WeylLinear

/-!
# Weyl's theorem for an arbitrary polynomial

`RiemannHypothesis.WeylLinear` proves that `α n` is equidistributed modulo one for `α`
irrational, and `RiemannHypothesis.WeylCriterion` proves it for `α n²`.  This file proves the
general statement, **Weyl's theorem**: if `p` is a real polynomial of degree `d ≥ 1` whose
leading coefficient is irrational, then the fractional parts of `p(n)` are equidistributed.

The induction is on the degree, and the inductive step is van der Corput's difference theorem
(`RiemannHypothesis.WeylDifferenceTheorem`): the difference `p(X + k) − p(X)` is a polynomial of
degree `d − 1` whose leading coefficient is `d · a_d · k`, again irrational for `k ≥ 1`.

## Main results

* `coeff_diffPoly_pred`, `natDegree_diffPoly` — the forward difference `p(X + k) − p(X)` has
  degree `d − 1` and leading coefficient `d · a_d · k`.
* `equidistributedMod1_polyEval` — **Weyl's theorem**: `n ↦ p(n)` is equidistributed modulo one
  whenever `deg p ≥ 1` and the leading coefficient of `p` is irrational.
* `tendsto_countIn_div_polyEval` — its counting form: the proportion of `n < N` with
  `Int.fract (p n) ∈ [a, b) ⊆ [0, 1)` tends to `b − a`.
* `equidistributedMod1_monomial`, `tendsto_countIn_div_monomial` — the special case `α n^d`.

## Scope

No rate of convergence is claimed: the estimates behind Weyl's criterion here are ineffective in
the diophantine nature of the leading coefficient.  Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology Polynomial

namespace RiemannHypothesis

namespace WeylPolynomial

open WeylCriterion WeylCount WeylDifference

/-- The forward difference `p(X + k) − p(X)` of a real polynomial. -/
def diffPoly (p : ℝ[X]) (k : ℕ) : ℝ[X] := Polynomial.taylor (k : ℝ) p - p

/-- The forward difference evaluates to the difference of the values. -/
theorem eval_diffPoly (p : ℝ[X]) (k n : ℕ) :
    (diffPoly p k).eval (n : ℝ) = p.eval ((n + k : ℕ) : ℝ) - p.eval (n : ℝ) := by
  simp [diffPoly, taylor_eval]

/-- The Hasse derivatives above the degree vanish. -/
theorem hasseDeriv_eq_zero_of_lt {p : ℝ[X]} {i : ℕ} (hi : p.natDegree < i) :
    hasseDeriv i p = 0 := by
  ext m
  rw [hasseDeriv_coeff, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- Differencing kills every coefficient from the degree upwards. -/
theorem coeff_diffPoly_of_le (p : ℝ[X]) (k : ℕ) {i : ℕ} (hi : p.natDegree ≤ i) :
    (diffPoly p k).coeff i = 0 := by
  rcases eq_or_lt_of_le hi with heq | hlt
  · have hdeg : (hasseDeriv i p).natDegree < 1 := by
      have h := natDegree_hasseDeriv_le p i; omega
    rw [diffPoly, coeff_sub, taylor_coeff, eval_eq_sum_range' hdeg]
    simp [hasseDeriv_coeff, ← heq]
  · rw [diffPoly, coeff_sub, taylor_coeff, hasseDeriv_eq_zero_of_lt hlt, eval_zero,
      coeff_eq_zero_of_natDegree_lt hlt, sub_zero]

/-- The coefficient of `X^{d−1}` in `p(X + k) − p(X)` is `d · a_d · k`. -/
theorem coeff_diffPoly_pred (p : ℝ[X]) (k : ℕ) (hd : 1 ≤ p.natDegree) :
    (diffPoly p k).coeff (p.natDegree - 1) = (p.natDegree : ℝ) * p.coeff p.natDegree * k := by
  have hdeg : (hasseDeriv (p.natDegree - 1) p).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le p (p.natDegree - 1); omega
  rw [diffPoly, coeff_sub, taylor_coeff, eval_eq_sum_range' hdeg]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [hasseDeriv_coeff, zero_add, pow_zero, pow_one, mul_one]
  have h1 : (1 + (p.natDegree - 1)) = p.natDegree := by omega
  rw [h1]
  have hc0 : Nat.choose (p.natDegree - 1) (p.natDegree - 1) = 1 := Nat.choose_self _
  have hc1 : Nat.choose p.natDegree (p.natDegree - 1) = p.natDegree := by
    have hsym := Nat.choose_symm (Nat.sub_le p.natDegree 1)
    have h2 : p.natDegree - (p.natDegree - 1) = 1 := by omega
    rw [h2] at hsym
    rw [← hsym, Nat.choose_one_right]
  rw [hc0, hc1]
  push_cast
  ring

/-- The forward difference of a polynomial of degree `d ≥ 1` by a nonzero shift has degree
exactly `d − 1`, provided the leading coefficient does not vanish. -/
theorem natDegree_diffPoly (p : ℝ[X]) {k : ℕ} (hk : 0 < k) (hd : 1 ≤ p.natDegree)
    (hlead : p.coeff p.natDegree ≠ 0) : (diffPoly p k).natDegree = p.natDegree - 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_diffPoly_of_le p k (by omega)
  · rw [coeff_diffPoly_pred p k hd]
    have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hD : (p.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact mul_ne_zero (mul_ne_zero hD hlead) hk'

/-- The induction on the degree behind Weyl's theorem. -/
theorem equidistributedMod1_polyEval_aux :
    ∀ d : ℕ, ∀ p : ℝ[X], p.natDegree = d → 1 ≤ d → Irrational (p.coeff d) →
      EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ) := by
  intro d
  induction d with
  | zero => intro p _ hd _; omega
  | succ d ih =>
    intro p hp _ hirr
    have hlead : p.coeff (d + 1) ≠ 0 := hirr.ne_zero
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · -- degree one: a linear sequence with an irrational slope
      have hlin : (fun n : ℕ => p.eval (n : ℝ))
          = fun n : ℕ => p.coeff 1 * (n : ℝ) + p.coeff 0 := by
        funext n
        have hdeg : p.natDegree < 2 := by omega
        rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        ring
      rw [hlin]
      exact equidistributedMod1_add_const (equidistributedMod1_linear hirr) _
    · -- degree at least two: difference and induct
      refine equidistributedMod1_of_diff ?_
      intro k hk
      have hq : diffSeq (fun n : ℕ => p.eval (n : ℝ)) k
          = fun n : ℕ => (diffPoly p k).eval (n : ℝ) := by
        funext n
        rw [eval_diffPoly]
        rfl
      rw [hq]
      have hnd : (diffPoly p k).natDegree = d := by
        rw [natDegree_diffPoly p hk (by omega) (by rw [hp]; exact hlead), hp]
        omega
      refine ih (diffPoly p k) hnd hdpos ?_
      have hcoeff : (diffPoly p k).coeff d = ((d + 1 : ℕ) : ℝ) * p.coeff (d + 1) * k := by
        have hpred := coeff_diffPoly_pred p k (by omega)
        rw [hp] at hpred
        simpa using hpred
      rw [hcoeff]
      have hne : ((d + 1) * k : ℕ) ≠ 0 := by positivity
      have hmul := hirr.natCast_mul hne
      convert hmul using 1
      push_cast
      ring

/-- **Weyl's theorem.**  If `p` is a real polynomial of degree at least one whose leading
coefficient is irrational, then the fractional parts of `p(n)` are equidistributed modulo one. -/
theorem equidistributedMod1_polyEval {p : ℝ[X]} (hd : 1 ≤ p.natDegree)
    (hirr : Irrational (p.coeff p.natDegree)) :
    EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ) :=
  equidistributedMod1_polyEval_aux p.natDegree p rfl hd hirr

/-- **Weyl's theorem in its counting form.**  For `0 ≤ a < b ≤ 1`, the proportion of `n < N`
with `Int.fract (p n) ∈ [a, b)` tends to `b − a`. -/
theorem tendsto_countIn_div_polyEval {p : ℝ[X]} (hd : 1 ≤ p.natDegree)
    (hirr : Irrational (p.coeff p.natDegree)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn (fun n : ℕ => p.eval (n : ℝ)) a b N : ℝ) / N) atTop
      (𝓝 (b - a)) :=
  tendsto_countIn_div_of_le (equidistributedMod1_polyEval hd hirr) ha hab hb

/-- The fractional parts of `α n^d` are equidistributed for every irrational `α` and `d ≥ 1`. -/
theorem equidistributedMod1_monomial {α : ℝ} (hα : Irrational α) {d : ℕ} (hd : 1 ≤ d) :
    EquidistributedMod1 fun n : ℕ => α * (n : ℝ) ^ d := by
  have hα0 : α ≠ 0 := hα.ne_zero
  set p : ℝ[X] := C α * X ^ d with hp
  have hnd : p.natDegree = d := by simp [hp, hα0]
  have hco : p.coeff p.natDegree = α := by rw [hnd]; simp [hp]
  have heval : (fun n : ℕ => p.eval (n : ℝ)) = fun n : ℕ => α * (n : ℝ) ^ d := by
    funext n; simp [hp]
  have hmain := equidistributedMod1_polyEval (p := p) (by omega) (by rw [hco]; exact hα)
  rwa [heval] at hmain

/-- The counting form for `α n^d`. -/
theorem tendsto_countIn_div_monomial {α : ℝ} (hα : Irrational α) {d : ℕ} (hd : 1 ≤ d) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn (fun n : ℕ => α * (n : ℝ) ^ d) a b N : ℝ) / N) atTop
      (𝓝 (b - a)) :=
  tendsto_countIn_div_of_le (equidistributedMod1_monomial hα hd) ha hab hb

end WeylPolynomial

end RiemannHypothesis
