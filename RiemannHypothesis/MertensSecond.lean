/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Mertens

/-!
# Mertens' second theorem

`∑_{p ≤ x} 1/p = log log x + O(1)`, with an explicit constant.  Mathlib knows that the sum of
the prime reciprocals diverges (`Nat.Primes.not_summable_one_div`), but not the rate.

The proof is summation by parts applied to Mertens' first theorem in its prime form
(`RiemannHypothesis.mertens_first_prime`): writing `A(n) = ∑_{p ≤ n} log p / p = log n + O(1)`
and `f(n) = 1/log n`,

`∑_{p ≤ N} 1/p = A(N) f(N) + ∑_{n < N} A(n) (f(n) − f(n+1))`,

where the main term `∑_n log n (f(n) − f(n+1))` telescopes against
`log log(n+1) − log log n` up to an error `O(1/n²)`, and the error term is controlled by
`∑_n (f(n) − f(n+1)) = f(2) − f(N)`.

## Main results

* `sum_by_parts_Ioc` : the discrete summation-by-parts identity used.
* `mertens_second_nat` : `|∑_{p ≤ N} 1/p − log log N| ≤ 50` for `N ≥ 2`.
* `mertens_second` : `|∑_{p ≤ x} 1/p − log log x| ≤ 52` for real `x ≥ 4`.
-/

noncomputable section

open Filter Finset Real
open ArithmeticFunction hiding log

namespace RiemannHypothesis

/-- The summatory function `∑_{p ≤ x} 1/p` over primes. -/
def primeRecipSum (x : ℝ) : ℝ := ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, (1 : ℝ) / p

/-- Discrete summation by parts on `Ioc 0 (N+1)`. -/
lemma sum_by_parts_Ioc (b f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 (N + 1), b n * f n
      = (∑ m ∈ Finset.Ioc 0 (N + 1), b m) * f (N + 1)
        + ∑ n ∈ Finset.Ioc 0 N, (∑ m ∈ Finset.Ioc 0 n, b m) * (f n - f (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : ∑ n ∈ Finset.Ioc 0 (N + 2), b n * f n
        = (∑ n ∈ Finset.Ioc 0 (N + 1), b n * f n) + b (N + 2) * f (N + 2) :=
      Finset.sum_Ioc_succ_top (by omega) _
    have e2 : ∑ m ∈ Finset.Ioc 0 (N + 2), b m = (∑ m ∈ Finset.Ioc 0 (N + 1), b m) + b (N + 2) :=
      Finset.sum_Ioc_succ_top (by omega) _
    have e3 : ∑ n ∈ Finset.Ioc 0 (N + 1), (∑ m ∈ Finset.Ioc 0 n, b m) * (f n - f (n + 1))
        = (∑ n ∈ Finset.Ioc 0 N, (∑ m ∈ Finset.Ioc 0 n, b m) * (f n - f (n + 1)))
          + (∑ m ∈ Finset.Ioc 0 (N + 1), b m) * (f (N + 1) - f (N + 2)) :=
      Finset.sum_Ioc_succ_top (by omega) _
    rw [e1, e2, e3, ih]
    ring

/-- The weight `Λ`-free prime weight `log p / p`, extended by zero. -/
private def bwt (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

/-- The Abel weight `1 / log n`. -/
private def fwt (n : ℕ) : ℝ := 1 / Real.log n

private lemma sum_bwt (n : ℕ) : ∑ m ∈ Finset.Ioc 0 n, bwt m = primeLogSum n := by
  unfold bwt primeLogSum
  rw [Nat.floor_natCast, Finset.sum_filter]

private lemma sum_bwt_mul_fwt (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, bwt n * fwt n = primeRecipSum N := by
  unfold bwt fwt primeRecipSum
  rw [Nat.floor_natCast, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hlog : Real.log n ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
    simp only [hp, if_pos]
    field_simp
  · simp [hp]

/-- `1/log` is antitone from `2` on. -/
private lemma fwt_antitone {n : ℕ} (hn : 2 ≤ n) : fwt (n + 1) ≤ fwt n := by
  unfold fwt
  have h2 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hmono : Real.log n ≤ Real.log (n + 1) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  have h3 : (0 : ℝ) < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le h2 hmono
  rw [div_le_div_iff₀ (by push_cast at h3 ⊢; exact h3) h2]
  push_cast at hmono ⊢
  linarith

/-- The telescoping sum of `f(n) − f(n+1)`. -/
private lemma sum_fwt_telescope (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, (fwt n - fwt (n + 1)) = fwt 2 - fwt (M + 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) by decide]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- Upper bound for the main term: `log n (f(n) − f(n+1)) ≤ log log (n+1) − log log n`. -/
private lemma main_term_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log n * (fwt n - fwt (n + 1))
      ≤ Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have ha : 0 < Real.log n := Real.log_pos (by linarith)
  have hab : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hb : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le ha hab
  have hfwt : fwt n - fwt (n + 1) = 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
    unfold fwt; rw [hcast]
  rw [hfwt]
  have hlhs : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))
      = 1 - Real.log n / Real.log ((n : ℝ) + 1) := by
    field_simp
  rw [hlhs]
  have hkey : Real.log (Real.log n / Real.log ((n : ℝ) + 1))
      ≤ Real.log n / Real.log ((n : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hkey
  linarith

/-- Lower bound for the main term, with an error `O(1/n²)`. -/
private lemma main_term_ge {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)
        - 1 / (Real.log 2 ^ 2 * (n : ℝ) ^ 2)
      ≤ Real.log n * (fwt n - fwt (n + 1)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have ha0 : 0 < Real.log n := lt_of_lt_of_le hL ha
  have hab : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hb0 : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le ha0 hab
  have hd1 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / (n : ℝ)) (by positivity)
    rw [Real.log_div (by linarith) (ne_of_gt hn0)] at h
    have he : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
    rw [he] at h
    exact h
  set a := Real.log n with hadef
  set b := Real.log ((n : ℝ) + 1) with hbdef
  have hfwt : fwt n - fwt (n + 1) = 1 / a - 1 / b := by
    unfold fwt; rw [hcast]
  rw [hfwt]
  have hlhs : a * (1 / a - 1 / b) = 1 - a / b := by field_simp
  rw [hlhs]
  have hkey : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hb0) (ne_of_gt ha0)] at hkey
  have hd0 : 0 ≤ b - a := by linarith
  have hd1' : (b - a) * (n : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hd1 hn0.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hn0)] at h
  have hL2 : Real.log 2 ^ 2 ≤ a * b := by nlinarith
  have hdn : (b - a) ^ 2 * (n : ℝ) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hd0 hn0.le]
  have hstep : (b - a) / a - (b - a) / b = (b - a) ^ 2 / (a * b) := by
    field_simp
  have hbound : (b - a) ^ 2 / (a * b) ≤ 1 / (Real.log 2 ^ 2 * (n : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hdn (le_of_lt (pow_pos hL 2))]
  have hba : (b - a) / b = 1 - a / b := by field_simp
  have hba' : b / a - 1 = (b - a) / a := by field_simp
  linarith

/-- `∑_{n = 2}^{M} 1/n² ≤ 1`, by telescoping `1/n² ≤ 1/(n−1) − 1/n`. -/
lemma sum_inv_sq_le (M : ℕ) : ∑ n ∈ Finset.Icc 2 M, 1 / (n : ℝ) ^ 2 ≤ 1 := by
  have key : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Finset.Icc 2 M, 1 / (n : ℝ) ^ 2 ≤ 1 - 1 / (M : ℝ) := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with rfl | hM0
      · rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
        norm_num
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
      have hih := ih (by omega)
      have hstep : 1 / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hMr) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [show Finset.Icc 2 0 = (∅ : Finset ℕ) by decide]
    norm_num
  have h := key M hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have : 0 ≤ 1 / (M : ℝ) := by positivity
  linarith

/-- The telescoping sum `∑_{n=2}^{M} (log log (n+1) − log log n) = log log (M+1) − log log 2`. -/
private lemma sum_loglog_telescope (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M,
        (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n))
      = Real.log (Real.log ((M : ℝ) + 1)) - Real.log (Real.log 2) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) by decide]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The telescoping bound for the main term over `[2, M]`. -/
private lemma sum_main_term_bounds (M : ℕ) (hM : 1 ≤ M) :
    Real.log (Real.log ((M : ℝ) + 1)) - Real.log (Real.log 2) - 1 / Real.log 2 ^ 2
        ≤ ∑ n ∈ Finset.Icc 2 M, Real.log n * (fwt n - fwt (n + 1)) ∧
      ∑ n ∈ Finset.Icc 2 M, Real.log n * (fwt n - fwt (n + 1))
        ≤ Real.log (Real.log ((M : ℝ) + 1)) - Real.log (Real.log 2) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htel := sum_loglog_telescope M hM
  constructor
  · have h1 : ∑ n ∈ Finset.Icc 2 M,
        ((Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n))
          - 1 / Real.log 2 ^ 2 * (1 / (n : ℝ) ^ 2))
        ≤ ∑ n ∈ Finset.Icc 2 M, Real.log n * (fwt n - fwt (n + 1)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
      have heq : 1 / Real.log 2 ^ 2 * (1 / (n : ℝ) ^ 2)
          = 1 / (Real.log 2 ^ 2 * (n : ℝ) ^ 2) := by
        rw [div_mul_div_comm]; norm_num
      rw [heq]
      exact main_term_ge hn2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htel] at h1
    have h2 : ∑ n ∈ Finset.Icc 2 M, 1 / (n : ℝ) ^ 2 ≤ 1 := sum_inv_sq_le M
    have h3 : (0 : ℝ) ≤ 1 / Real.log 2 ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · have h1 : ∑ n ∈ Finset.Icc 2 M, Real.log n * (fwt n - fwt (n + 1))
        ≤ ∑ n ∈ Finset.Icc 2 M,
            (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)) :=
      Finset.sum_le_sum fun n hn => main_term_le (Finset.mem_Icc.1 hn).1
    rwa [htel] at h1

/-- The Abel error term is bounded by `C₀ (f(2) − f(M+1))`, where `C₀` is the constant in
Mertens' first theorem in prime form. -/
private lemma sum_error_bounds (M : ℕ) (hM : 1 ≤ M) :
    |∑ n ∈ Finset.Icc 2 M, primeLogSum n * (fwt n - fwt (n + 1))
        - ∑ n ∈ Finset.Icc 2 M, Real.log n * (fwt n - fwt (n + 1))|
      ≤ (Real.log 4 + 12 + Real.log 2) * (fwt 2 - fwt (M + 1)) := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ n ∈ Finset.Icc 2 M,
          (primeLogSum n * (fwt n - fwt (n + 1)) - Real.log n * (fwt n - fwt (n + 1)))|
      ≤ ∑ n ∈ Finset.Icc 2 M,
          |primeLogSum n * (fwt n - fwt (n + 1)) - Real.log n * (fwt n - fwt (n + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 M, (Real.log 4 + 12 + Real.log 2) * (fwt n - fwt (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
        have hnn : 0 ≤ fwt n - fwt (n + 1) := by linarith [fwt_antitone hn2]
        have hb := mertens_first_prime (x := (n : ℝ)) (by exact_mod_cast (by omega : 1 ≤ n))
        rw [← sub_mul, abs_mul, abs_of_nonneg hnn]
        exact mul_le_mul_of_nonneg_right hb hnn
    _ = (Real.log 4 + 12 + Real.log 2) * (fwt 2 - fwt (M + 1)) := by
        rw [← Finset.mul_sum, sum_fwt_telescope M hM]

/-- `∑_{p ≤ 1} log p / p = 0`. -/
private lemma primeLogSum_one : primeLogSum ((1 : ℕ) : ℝ) = 0 := by
  unfold primeLogSum
  rw [Nat.floor_natCast]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hp0, hp1⟩, hpp⟩ := hp
  have : p = 1 := by omega
  subst this
  exact absurd hpp Nat.not_prime_one

/-- **Mertens' second theorem**, at integer arguments. -/
theorem mertens_second_nat {N : ℕ} (hN : 2 ≤ N) :
    |primeRecipSum N - Real.log (Real.log N)| ≤ 50 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  have hMcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (2 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := Real.log 4 + 12 + Real.log 2 with hCdef
  have hCnn : 0 ≤ C := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hCdef]; linarith
  -- summation by parts
  have hparts := sum_by_parts_Ioc bwt fwt M
  rw [sum_bwt_mul_fwt] at hparts
  simp only [sum_bwt] at hparts
  have hset : Finset.Ioc 1 M = Finset.Icc 2 M := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hsplit : ∑ n ∈ Finset.Ioc (0 : ℕ) M, primeLogSum n * (fwt n - fwt (n + 1))
      = ∑ n ∈ Finset.Icc (2 : ℕ) M, primeLogSum n * (fwt n - fwt (n + 1)) := by
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hM, hset]
    have h1 : ∑ n ∈ Finset.Ioc (0 : ℕ) 1, primeLogSum n * (fwt n - fwt (n + 1)) = 0 := by
      rw [show Finset.Ioc 0 1 = ({1} : Finset ℕ) by decide, Finset.sum_singleton,
        primeLogSum_one, zero_mul]
    rw [h1, zero_add]
  rw [hsplit, hMcast] at hparts
  rw [hMcast]
  -- numeric facts about log 2
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have hCle : C ≤ 14.08 := by rw [hCdef, hl4]; linarith
  have hinv : 1 / Real.log 2 ≤ 1.4429 := by
    rw [div_le_iff₀ hL]; nlinarith
  have hCdiv : C / Real.log 2 ≤ 20.4 := by
    rw [div_le_iff₀ hL]; nlinarith
  have hinvsq : 1 / Real.log 2 ^ 2 ≤ 2.09 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hlo, hL, sq_nonneg (Real.log 2 - 0.6931471803)]
  have hll2hi : Real.log (Real.log 2) ≤ 0 := by
    have h := Real.log_le_sub_one_of_pos hL
    linarith
  have hll2lo : -0.45 ≤ Real.log (Real.log 2) := by
    have h := Real.log_le_sub_one_of_pos (x := (Real.log 2)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    rw [one_div] at hinv
    linarith
  -- the boundary term
  have hlogM : Real.log 2 ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log (by norm_num) hM1
  have hlogMpos : 0 < Real.log ((M : ℝ) + 1) := lt_of_lt_of_le hL hlogM
  have hfM1 : fwt (M + 1) = 1 / Real.log ((M : ℝ) + 1) := by unfold fwt; rw [hMcast]
  have hf2 : fwt 2 = 1 / Real.log 2 := by unfold fwt; norm_num
  have hfM1nn : 0 ≤ fwt (M + 1) := by rw [hfM1]; positivity
  have hbd := mertens_first_prime (x := (M : ℝ) + 1) (by linarith)
  rw [← hCdef] at hbd
  have hbterm : |primeLogSum ((M : ℝ) + 1) * fwt (M + 1) - 1| ≤ C / Real.log 2 := by
    rw [hfM1]
    have heq : primeLogSum ((M : ℝ) + 1) * (1 / Real.log ((M : ℝ) + 1)) - 1
        = (primeLogSum ((M : ℝ) + 1) - Real.log ((M : ℝ) + 1)) / Real.log ((M : ℝ) + 1) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hlogMpos]
    calc |primeLogSum ((M : ℝ) + 1) - Real.log ((M : ℝ) + 1)| / Real.log ((M : ℝ) + 1)
        ≤ C / Real.log ((M : ℝ) + 1) := by gcongr
      _ ≤ C / Real.log 2 := by gcongr
  -- the error and main terms
  have herr := sum_error_bounds M hM
  have hCfwt : C * (fwt 2 - fwt (M + 1)) ≤ 20.4 :=
    calc C * (fwt 2 - fwt (M + 1)) ≤ C * fwt 2 := by
          nlinarith [mul_nonneg hCnn hfM1nn]
      _ = C / Real.log 2 := by rw [hf2]; ring
      _ ≤ 20.4 := hCdiv
  obtain ⟨hmain_lo, hmain_hi⟩ := sum_main_term_bounds M hM
  rw [← hCdef] at herr
  rw [abs_le] at hbterm herr ⊢
  constructor <;> linarith [hbterm.1, hbterm.2, herr.1, herr.2]

/-- **Mertens' second theorem**: `∑_{p ≤ x} 1/p = log log x + O(1)`. -/
theorem mertens_second {x : ℝ} (hx : 4 ≤ x) :
    |primeRecipSum x - Real.log (Real.log x)| ≤ 52 := by
  have hx0 : (0 : ℝ) < x := by linarith
  set N := ⌊x⌋₊ with hNdef
  have hN4 : 4 ≤ N := by
    have h : ((4 : ℕ) : ℝ) ≤ x := by exact_mod_cast hx
    exact Nat.le_floor h
  have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have heq : primeRecipSum x = primeRecipSum (N : ℝ) := by
    unfold primeRecipSum; rw [Nat.floor_natCast, hNdef]
  have h1 := mertens_second_nat (N := N) (by omega)
  have hN4r : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlogN : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN4r
  have hlogNpos : 0 < Real.log N := by rw [hl4] at hlogN; linarith
  have hlogx : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNle
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le hlogNpos hlogx
  have hlogx2 : Real.log x ≤ Real.log N + Real.log 2 := by
    have hle : x ≤ 2 * (N : ℝ) := by linarith
    calc Real.log x ≤ Real.log (2 * (N : ℝ)) := Real.log_le_log hx0 hle
      _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log N + Real.log 2 := by ring
  have hd : 0 ≤ Real.log (Real.log x) - Real.log (Real.log N) :=
    sub_nonneg.2 (Real.log_le_log hlogNpos hlogx)
  have hd2 : Real.log (Real.log x) - Real.log (Real.log N) ≤ 1 := by
    have hk : Real.log (Real.log x / Real.log N) ≤ Real.log x / Real.log N - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlogxpos hlogNpos)
    rw [Real.log_div (ne_of_gt hlogxpos) (ne_of_gt hlogNpos)] at hk
    have hq : Real.log x / Real.log N - 1 ≤ 1 := by
      rw [div_sub_one (ne_of_gt hlogNpos), div_le_one hlogNpos]
      rw [hl4] at hlogN
      linarith
    linarith
  rw [heq]
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end RiemannHypothesis
