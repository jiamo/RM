/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.FourthMoment

/-!
# All even moments of `ζ` on a line of absolute convergence

The `k`-fold divisor function `d_k(n)`, the number of ordered factorizations of `n` into `k`
factors, is the `k`-th convolution power of the constant-one arithmetic function, so
`ζ(s)^k = ∑ d_k(n) n^(-s)` for `re s > 1`.  Feeding this into the mean value theorem of
`RiemannHypothesis.MeanSquare` gives every even moment of `ζ` on a line of absolute
convergence:

`(1/T) ∫₀ᵀ |ζ(σ + i t)|^{2k} dt → ∑ d_k(n)² n^(-2σ)`  as  `T → ∞`.

For `k = 1` this is the second moment of `RiemannHypothesis.MeanSquare` and for `k = 2` the
fourth moment of `RiemannHypothesis.FourthMoment`.

## Main results

* `lseries_divisorCountK` : `∑ d_k(n) n^(-s) = ζ(s)^k` for `re s > 1`.
* `momentAvg_tendsto_tsum_divisorCountK` : the `2k`-th moment of `ζ` for `σ > 1`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology ArithmeticFunction

namespace RiemannHypothesis

/-- The `k`-fold divisor function: the number of ordered factorizations of `n` into `k`
factors, i.e. the `k`-th convolution power of the constant-one arithmetic function. -/
def divisorCountK (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n

lemma natCoe_zeta_pow (k : ℕ) :
    ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      = (ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ← ih, ArithmeticFunction.natCoe_mul]

lemma divisorCountK_apply_complex (k n : ℕ) :
    ((divisorCountK k n : ℕ) : ℂ) = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ k) n := by
  rw [divisorCountK, ← natCoe_zeta_pow]
  simp

@[simp] lemma divisorCountK_zero (n : ℕ) : divisorCountK 0 n = if n = 1 then 1 else 0 := by
  simp [divisorCountK, ArithmeticFunction.one_apply]

@[simp] lemma divisorCountK_one (n : ℕ) : divisorCountK 1 n = if n = 0 then 0 else 1 := by
  simp [divisorCountK, ArithmeticFunction.zeta_apply]

/-- The `2`-fold divisor function is the number of divisors. -/
lemma divisorCountK_two (n : ℕ) : divisorCountK 2 n = divisorCount n := by
  have h := divisorCountK_apply_complex 2 n
  have h2 : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ 2) n
      = LSeries.convolution (fun m => (ArithmeticFunction.zeta m : ℂ))
        (fun m => (ArithmeticFunction.zeta m : ℂ)) n := by
    rw [sq, ← ArithmeticFunction.coe_mul]
    rfl
  rw [h2, convolution_zeta_zeta_eq_divisorCount] at h
  exact_mod_cast h

/-- One step of the convolution recursion for the `k`-fold divisor function. -/
lemma convolution_zeta_divisorCountK (k n : ℕ) :
    LSeries.convolution (fun m => (ArithmeticFunction.zeta m : ℂ))
      (fun m => (divisorCountK k m : ℂ)) n = (divisorCountK (k + 1) n : ℂ) := by
  have hcoe : (fun m => (divisorCountK k m : ℂ))
      = ⇑((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ^ k) :=
    funext fun m => divisorCountK_apply_complex k m
  have hzeta : (fun m => (ArithmeticFunction.zeta m : ℂ))
      = ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) := rfl
  rw [hcoe, hzeta, ArithmeticFunction.coe_mul, ← pow_succ']
  exact (divisorCountK_apply_complex (k + 1) n).symm

/-- The Dirichlet series of the `k`-fold divisor function converges absolutely for
`re s > 1`. -/
lemma lseriesSummable_divisorCountK (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorCountK k n : ℂ)) s := by
  induction k with
  | zero =>
      have hsummable : Summable (LSeries.term LSeries.delta s) := by
        refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
        rw [LSeries.term_delta, if_neg (by simpa using hn)]
      rw [show (fun n => (divisorCountK 0 n : ℂ)) = LSeries.delta from
        funext fun n => by simp [LSeries.delta]]
      exact hsummable
  | succ k ih =>
      have h := (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs).convolution ih
      exact (LSeriesSummable_congr s fun {n} _ => convolution_zeta_divisorCountK k n).mp h

/-- `∑ d_k(n) n^(-s) = ζ(s)^k` for `re s > 1`. -/
theorem lseries_divisorCountK (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (divisorCountK k n : ℂ)) s = riemannZeta s ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, show (fun n => (divisorCountK 0 n : ℂ)) = LSeries.delta from
        funext fun n => by simp [LSeries.delta]]
      exact congrFun LSeries_delta s
  | succ k ih =>
      have hz := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
      have h := LSeries_convolution' hz (lseriesSummable_divisorCountK k hs)
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ih] at h
      rw [pow_succ', ← h]
      exact LSeries_congr (fun {n} _ => (convolution_zeta_divisorCountK k n).symm) s

lemma summable_dirichletWeight_divisorCountK (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (dirichletWeight (fun n => ((divisorCountK k (n + 1) : ℕ) : ℂ)) σ) := by
  have hre : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have h := summable_shift_rpow_of_lseriesSummable (a := fun n => (divisorCountK k n : ℝ))
    ((lseriesSummable_divisorCountK k hre).congr fun n => by push_cast; ring)
  refine h.congr fun n => ?_
  rw [dirichletWeight, Complex.norm_natCast]

/-- On the line of real part `σ > 1`, the Dirichlet series of the `k`-fold divisor function
is `ζ^k`. -/
lemma dirichletLineSum_divisorCountK (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    dirichletLineSum (fun n => ((divisorCountK k (n + 1) : ℕ) : ℂ)) σ t
      = riemannZeta (linePoint σ t) ^ k := by
  have hre : 1 < (linePoint σ t).re := by simpa using hσ
  have h := lseries_eq_dirichletLineSum (fun n => (divisorCountK k n : ℂ)) σ t
    (lseriesSummable_divisorCountK k hre)
  rw [lseries_divisorCountK k hre] at h
  exact h.symm

/-- **The even moments of `ζ` on a line of absolute convergence.**  For `σ > 1` and every
`k`, `(1/T) ∫₀ᵀ |ζ(σ + i t)|^{2k} dt → ∑_{n ≥ 1} d_k(n)² n^(-2σ)`, where `d_k(n)` is the
number of ordered factorizations of `n` into `k` factors. -/
theorem momentAvg_tendsto_tsum_divisorCountK (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ (2 * k)) / T)
      atTop
      (𝓝 (∑' n : ℕ, ((divisorCountK k (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  have h := meanSquareAvg_tendsto_tsum_of_summable (summable_dirichletWeight_divisorCountK k hσ)
  simp_rw [dirichletLineSum_divisorCountK k hσ, norm_pow] at h
  have hpow : ∀ t : ℝ, (‖riemannZeta (linePoint σ t)‖ ^ k) ^ 2
      = ‖riemannZeta (linePoint σ t)‖ ^ (2 * k) := by
    intro t; rw [← pow_mul, mul_comm]
  have hcoeff : ∀ n : ℕ,
      dirichletWeight (fun n => ((divisorCountK k (n + 1) : ℕ) : ℂ)) σ n ^ 2
        = ((divisorCountK k (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [dirichletWeight_sq, Complex.norm_natCast]
  simp_rw [hpow, hcoeff] at h
  exact h

end RiemannHypothesis
