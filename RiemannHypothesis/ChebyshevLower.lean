/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannHypothesis.PrimeCounting

/-!
# Chebyshev's lower bound

Mathlib provides Chebyshev's *upper* bounds `θ x ≤ x log 4` and `ψ x ≤ (log 4 + 4) x`
(`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_le_const_mul_self`) and lists the matching
lower bound as a TODO.  This file proves the lower bound, by the classical central-binomial
argument of Chebyshev (1852):

* every prime power `p ^ ν_p` occurring in the factorization of `C(2n, n)` is at most `2n`,
  so `log C(2n, n) ≤ ψ(2n)`;
* `4 ^ n < n * C(2n, n)` for `n ≥ 4`, so `log C(2n, n) > 2n log 2 - log n`.

## Main results

* `log_le_psi_of_pow_factorization_le` : if every prime power occurring in the factorization
  of `m` is at most `N`, then `log m ≤ ψ N`.
* `psi_lower_bound` : `(x - 2) log 2 - log x ≤ ψ x` for `8 ≤ x`.
* `psi_ge_half_log_two_mul` : `(log 2 / 2) * x ≤ ψ x` for `12 ≤ x`.
* `theta_ge_eventually`, `primeCounting_ge_eventually` : the corresponding lower bounds for
  `θ` and for the prime counting function `π`, the latter in the Chebyshev form
  `π(⌊x⌋) ≥ c · x / log x`.
-/

noncomputable section

open Filter Finset Real
open ArithmeticFunction hiding log

namespace RiemannHypothesis

/-- The logarithm of a positive natural number is the sum of `ν_p log p` over its prime
factorization. -/
lemma log_eq_sum_factorization_mul_log {m : ℕ} (hm : m ≠ 0) :
    Real.log m = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  push_cast
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
  · intro p hp
    have := Nat.pos_of_mem_primeFactors hp
    positivity

/-- The sum of `ν_p log p` over the prime factorization of `m` is at most `ψ N`, provided every
prime power `p ^ ν_p` is at most `N`.  Indeed the prime powers `p ^ j` with `1 ≤ j ≤ ν_p` are
then distinct integers in `(0, N]`, and each contributes `Λ(p ^ j) = log p` to `ψ N`. -/
lemma sum_factorization_mul_log_le_psi {m N : ℕ}
    (h : ∀ p ∈ m.primeFactors, p ^ m.factorization p ≤ N) :
    ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p ≤ Chebyshev.psi N := by
  classical
  set T : Finset ℕ :=
    m.primeFactors.biUnion (fun p => (Finset.Icc 1 (m.factorization p)).image (fun j => p ^ j))
    with hT
  have hTsub : T ⊆ Finset.Ioc 0 N := by
    intro k hk
    simp only [hT, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc] at hk
    obtain ⟨p, hp, j, ⟨_, hj2⟩, rfl⟩ := hk
    have hp2 := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_Ioc.2 ⟨Nat.pow_pos hp2.pos,
      le_trans (Nat.pow_le_pow_right hp2.one_lt.le hj2) (h p hp)⟩
  have hpsi : ∑ k ∈ T, Λ k ≤ Chebyshev.psi N := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => vonMangoldt_nonneg)
  have hsum : ∑ k ∈ T, Λ k = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
    rw [hT, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp2 := Nat.prime_of_mem_primeFactors hp
      rw [Finset.sum_image]
      · rw [Finset.sum_congr rfl (g := fun _ => Real.log p) ?_]
        · simp [Nat.card_Icc, mul_comm]
        · intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp2]
      · intro a _ b _ hab
        exact Nat.pow_right_injective hp2.two_le hab
    · intro p hp q hq hpq
      simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Icc]
      rintro a ⟨i, ⟨hi1, _⟩, rfl⟩ ⟨j, ⟨hj1, _⟩, hji⟩
      have hp2 := Nat.prime_of_mem_primeFactors hp
      have hq2 := Nat.prime_of_mem_primeFactors hq
      obtain ⟨hqp, -⟩ := Nat.Prime.pow_inj' hq2 hp2 (by omega) (by omega) hji
      exact hpq hqp.symm
  rw [← hsum]
  exact hpsi

/-- If every prime power occurring in the factorization of `m` is at most `N`, then
`log m ≤ ψ N`.  This is the arithmetic heart of Chebyshev's lower bound. -/
lemma log_le_psi_of_pow_factorization_le {m N : ℕ} (hm : m ≠ 0)
    (h : ∀ p ∈ m.primeFactors, p ^ m.factorization p ≤ N) :
    Real.log m ≤ Chebyshev.psi N := by
  rw [log_eq_sum_factorization_mul_log hm]
  exact sum_factorization_mul_log_le_psi h

/-- `log C(2n, n) ≤ ψ(2n)`: every prime power occurring in the central binomial coefficient is
at most `2n` (Kummer's bound). -/
lemma log_centralBinom_le_psi {n : ℕ} (hn : 0 < n) :
    Real.log (Nat.centralBinom n) ≤ Chebyshev.psi (2 * n : ℕ) := by
  refine log_le_psi_of_pow_factorization_le (Nat.centralBinom_ne_zero n) fun p _ => ?_
  exact Nat.pow_factorization_choose_le (by omega)

/-- Chebyshev's lower bound at even integers: `2n log 2 - log n ≤ ψ(2n)` for `n ≥ 4`. -/
lemma psi_two_mul_ge {n : ℕ} (hn : 4 ≤ n) :
    (2 * n : ℝ) * Real.log 2 - Real.log n ≤ Chebyshev.psi (2 * n : ℕ) := by
  have h4 : (4 : ℕ) ^ n < n * Nat.centralBinom n := Nat.four_pow_lt_mul_centralBinom n hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hc : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hcast : ((4 : ℝ)) ^ n ≤ (n : ℝ) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h4.le
  have hlog := Real.log_le_log (by positivity) hcast
  rw [Real.log_pow, Real.log_mul (ne_of_gt hn0) (ne_of_gt hc)] at hlog
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hcb := log_centralBinom_le_psi (show 0 < n by omega)
  rw [h42] at hlog
  linarith

/-- **Chebyshev's lower bound.** `(x - 2) log 2 - log x ≤ ψ x` for `x ≥ 8`. -/
theorem psi_lower_bound {x : ℝ} (hx : 8 ≤ x) :
    (x - 2) * Real.log 2 - Real.log x ≤ Chebyshev.psi x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set n : ℕ := ⌊x / 2⌋₊ with hn
  have hn4 : 4 ≤ n := Nat.le_floor (by push_cast; linarith)
  have hnle : (n : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hnlt : x / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmono : Chebyshev.psi ((2 * n : ℕ) : ℝ) ≤ Chebyshev.psi x :=
    Chebyshev.psi_mono (by push_cast; linarith)
  have hlog : Real.log n ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn4) (by linarith)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpt := psi_two_mul_ge hn4
  push_cast at hpt hmono
  nlinarith [hpt, hmono, hlog]

/-- **Chebyshev's lower bound, constant form.** `(log 2 / 2) x ≤ ψ x` for `x ≥ 12`. -/
theorem psi_ge_half_log_two_mul {x : ℝ} (hx : 12 ≤ x) :
    Real.log 2 / 2 * x ≤ Chebyshev.psi x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hmain := psi_lower_bound (by linarith : (8 : ℝ) ≤ x)
  have hlogx : Real.log x ≤ 4 * Real.log 2 + x / 16 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x / 16 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [h, h16.le, h16.ge]
  have hl1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  nlinarith [hmain, hlogx, hl1, hl2]

/-- **Chebyshev's lower bound for `θ`.**  Since `ψ - θ = O(√x log x)`, the lower bound for `ψ`
transfers to `θ` with a smaller constant, for all large `x`. -/
theorem theta_ge_eventually :
    ∀ᶠ x : ℝ in atTop, Real.log 2 / 4 * x ≤ Chebyshev.theta x := by
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x / Real.sqrt x < Real.log 2 / 8 :=
    tendsto_log_div_sqrt_atTop.eventually_lt_const (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (12 : ℝ)] with x hxs hx12
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hpsi := psi_ge_half_log_two_mul hx12
  have hdiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1 : ℝ) ≤ x)
  have hdiff' : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
    le_trans (le_abs_self _) hdiff
  have hrw : 2 * Real.sqrt x * Real.log x = 2 * (Real.log x / Real.sqrt x) * x := by
    field_simp
    rw [Real.sq_sqrt hx0.le]
    ring
  have hbound : 2 * Real.sqrt x * Real.log x ≤ Real.log 2 / 4 * x := by
    rw [hrw]
    have : 2 * (Real.log x / Real.sqrt x) ≤ Real.log 2 / 4 := by linarith
    nlinarith
  linarith

/-- **Chebyshev's lower bound for the prime counting function**: `π(⌊x⌋) ≥ c · x / log x` for
all large `x`, with `c = log 2 / 4`. -/
theorem primeCounting_ge_eventually :
    ∀ᶠ x : ℝ in atTop, Real.log 2 / 4 * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  filter_upwards [theta_ge_eventually, eventually_ge_atTop (2 : ℝ)] with x hth hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hint : 0 ≤ ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    refine intervalIntegral.integral_nonneg hx2 fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    exact div_nonneg (Chebyshev.theta_nonneg t) (by positivity)
  have heq := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  have hdiv : Real.log 2 / 4 * (x / Real.log x) ≤ Chebyshev.theta x / Real.log x := by
    calc Real.log 2 / 4 * (x / Real.log x)
        = (Real.log 2 / 4 * x) / Real.log x := by ring
      _ ≤ Chebyshev.theta x / Real.log x := by gcongr
  rw [heq]
  linarith

/-- **Chebyshev's bounds for `ψ`**: `ψ(x) ≍ x`. -/
theorem psi_asymptotic_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      c * x ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ C * x := by
  refine ⟨Real.log 2 / 2, Real.log 4 + 4, by positivity, ?_, ?_⟩
  · have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · filter_upwards [eventually_ge_atTop (12 : ℝ)] with x hx
    exact ⟨psi_ge_half_log_two_mul hx, Chebyshev.psi_le_const_mul_self (by linarith)⟩

/-- **Chebyshev's bounds for `θ`**: `θ(x) ≍ x`. -/
theorem theta_asymptotic_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      c * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ C * x := by
  refine ⟨Real.log 2 / 4, Real.log 4, by positivity, Real.log_pos (by norm_num), ?_⟩
  filter_upwards [theta_ge_eventually, eventually_ge_atTop (0 : ℝ)] with x h1 h2
  exact ⟨h1, Chebyshev.theta_le_log4_mul_x h2⟩

/-- **Chebyshev's theorem**: `π(⌊x⌋)` is bounded above and below by constant multiples of
`x / log x`.  The upper bound is Mathlib's `Chebyshev.eventually_primeCounting_le`; the lower
bound is `primeCounting_ge_eventually`, proved here. -/
theorem primeCounting_asymptotic_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      c * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
        (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * (x / Real.log x) := by
  refine ⟨Real.log 2 / 4, Real.log 4 + 1, by positivity, ?_, ?_⟩
  · have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · filter_upwards [primeCounting_ge_eventually,
      Chebyshev.eventually_primeCounting_le (ε := 1) one_pos] with x h1 h2
    exact ⟨h1, by rw [mul_div_assoc] at h2; exact h2⟩

end RiemannHypothesis
