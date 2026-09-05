/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BrunTwinPrimes

/-!
# Brun's theorem: the reciprocals of the twin primes converge

`RiemannHypothesis.BrunTwinPrimes` proves the twin-prime upper bound
`card_twinPrimes_le`: the number of `n < N` with `n` and `n + 2` both prime is at most
`900 N / (log N)² + √N + 1` as soon as `log N ≥ 32`.  Here that bound is summed dyadically:
the twin primes in `[2ᵏ, 2ᵏ⁺¹)` contribute at most `card (twinPrimes 2ᵏ⁺¹) / 2ᵏ`, which the
bound above makes `O(1/k²)`, and `∑ 1/k² < ∞`.  This is **Brun's theorem**.

## Main results

* `twinInv` — the function `n ↦ 1/n` restricted to the `n` with `n` and `n + 2` both prime.
* `sum_inv_twinPrimes_le` — `∑_{n < N, n, n+2 prime} 1/n ≤ 6600`, uniformly in `N`.
* `summable_twinInv` — **Brun's theorem**: the series `∑ 1/n` over the twin primes converges.
* `tsum_twinInv_le` — its sum is at most `6600`.
* `infinite_setOf_prime_not_prime_add_two` — there are infinitely many primes `p` with `p + 2`
  composite, because `∑ 1/p` over the primes diverges while its twin part converges.

## Scope

Only an upper bound for the sum is proved, and a very crude one: the Brun constant is
`B₂ = 1.902…`, while the bound obtained here is `6600`, the loss coming from the constant `900`
of `card_twinPrimes_le` (itself not sharp) and from the crude dyadic summation.  Nothing is
claimed about the *number* of twin primes from below (the twin-prime conjecture is open), and
nothing about `ζ` follows.  Convergence is compatible with there being only finitely many twin
primes, so `infinite_setOf_prime_not_prime_add_two` is a statement about the *non*-twin primes
only.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace BrunConstant

open BrunTwinPrimes BrunTitchmarsh

/-- The reciprocal `1/n`, restricted to the `n` with `n` and `n + 2` both prime. -/
def twinInv (n : ℕ) : ℝ := if n.Prime ∧ (n + 2).Prime then 1 / (n : ℝ) else 0

lemma twinInv_nonneg (n : ℕ) : 0 ≤ twinInv n := by
  unfold twinInv
  split
  · positivity
  · exact le_rfl

/-- The partial sums of `twinInv` are the sums of `1/n` over the twin primes below `N`. -/
lemma sum_twinInv_range (N : ℕ) :
    ∑ n ∈ range N, twinInv n = ∑ n ∈ twinPrimes N, (1 : ℝ) / (n : ℝ) := by
  classical
  rw [twinPrimes, Finset.sum_filter]
  rfl

/-- The dyadic block `[2ᵏ, 2ᵏ⁺¹)` of the twin-prime reciprocal sum. -/
def blockSum (k : ℕ) : ℝ := ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinInv n

lemma blockSum_nonneg (k : ℕ) : 0 ≤ blockSum k :=
  Finset.sum_nonneg fun n _ => twinInv_nonneg n

/-- The dyadic decomposition of the partial sums. -/
lemma sum_twinInv_two_pow (K : ℕ) :
    ∑ n ∈ range (2 ^ K), twinInv n = ∑ k ∈ range K, blockSum k := by
  induction K with
  | zero => simp [twinInv]
  | succ K ih =>
      have h : (2 : ℕ) ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Finset.sum_range_succ, ← ih, blockSum, Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) h).symm

/-- `k⁴ ≤ 2ᵏ` for `k ≥ 47`. -/
lemma pow_four_le_two_pow : ∀ k : ℕ, 47 ≤ k → k ^ 4 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hn1 : 1 ≤ n := by omega
      have h3 : n ≤ n ^ 3 := Nat.le_self_pow (by norm_num) n
      have h2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn1 (by norm_num)
      have h0 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h1 : 47 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
      have hstep : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by nlinarith [h1, h2, h3, h0]
      calc (n + 1) ^ 4 ≤ 2 * n ^ 4 := hstep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by ring

lemma card_Ico_two_pow (k : ℕ) : (Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
  rw [Nat.card_Ico, pow_succ]
  omega

/-- Each dyadic block contributes at most `1`. -/
lemma blockSum_le_one (k : ℕ) : blockSum k ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hb : ∀ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinInv n ≤ 1 / (2 : ℝ) ^ k := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnR : ((2 : ℝ) ^ k) ≤ (n : ℝ) := by exact_mod_cast hn.1
    unfold twinInv
    split
    · exact one_div_le_one_div_of_le hpos hnR
    · positivity
  calc blockSum k ≤ (Ico (2 ^ k) (2 ^ (k + 1))).card • ((1 : ℝ) / 2 ^ k) :=
        Finset.sum_le_card_nsmul _ _ _ hb
    _ = 1 := by
        rw [card_Ico_two_pow, nsmul_eq_mul]
        push_cast
        field_simp

/-- The numerical step of the dyadic bound: with `Mr = 2P` the endpoint of the block, `L` its
logarithm and `t` the parameter with `t² ≤ P` and `√Mr ≤ 2P/t²`, the twin-prime bound
`900 Mr/L² + √Mr + 1` is at most `3753 P/t²`. -/
lemma sieve_numeric {P t L S Mr : ℝ} (hP : 0 < P) (ht : 0 < t) (hMr : Mr = 2 * P)
    (hL : 0.48 * t ^ 2 ≤ L ^ 2) (hsqrt : Real.sqrt Mr ≤ 2 * P / t ^ 2)
    (ht2 : t ^ 2 ≤ P) (hS : S ≤ 900 * Mr / L ^ 2 + Real.sqrt Mr + 1) :
    S ≤ 3753 * P / t ^ 2 := by
  subst hMr
  have hLpos : (0 : ℝ) < L ^ 2 := by nlinarith
  have hterm1 : 900 * (2 * P) / L ^ 2 ≤ 3750 * P / t ^ 2 := by
    rw [div_le_div_iff₀ hLpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hL hP.le]
  have hterm3 : (1 : ℝ) ≤ P / t ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hsplit : 3750 * P / t ^ 2 + 2 * P / t ^ 2 + P / t ^ 2 = 3753 * P / t ^ 2 := by ring
  linarith

/-- For `k ≥ 46` the twin-prime bound makes the dyadic block `O(1/k²)`. -/
lemma blockSum_le_of_le {k : ℕ} (hk : 46 ≤ k) : blockSum k ≤ 3753 / ((k : ℝ) + 1) ^ 2 := by
  classical
  set t : ℝ := (k : ℝ) + 1 with ht
  have hkR : (46 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht47 : (47 : ℝ) ≤ t := by rw [ht]; linarith
  have htpos : (0 : ℝ) < t := by linarith
  set P : ℝ := (2 : ℝ) ^ k with hP
  have hPpos : (0 : ℝ) < P := by rw [hP]; positivity
  -- the twin primes of the block, and the sieve bound for them
  set M : ℕ := 2 ^ (k + 1) with hMdef
  have hMR : (M : ℝ) = 2 * P := by rw [hMdef, hP]; push_cast [pow_succ]; ring
  have hM4N : (k + 1) ^ 4 ≤ M := pow_four_le_two_pow (k + 1) (by omega)
  have ht4 : t ^ 4 ≤ 2 * P := by
    have h : (((k + 1) ^ 4 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4N
    rw [hMR] at h
    calc t ^ 4 = (((k + 1) ^ 4 : ℕ) : ℝ) := by rw [ht]; push_cast; ring
      _ ≤ 2 * P := h
  have ht2P : t ^ 2 ≤ P := by
    have ht2 : (2209 : ℝ) ≤ t ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
    have hsq : 2209 * t ^ 2 ≤ t ^ 4 := by nlinarith [hmul]
    linarith
  -- the logarithm of the block endpoint
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogM : Real.log (M : ℝ) = t * Real.log 2 := by
    rw [hMdef]
    push_cast
    rw [Real.log_pow, ht]
    push_cast
    ring
  have hL32 : (32 : ℝ) ≤ Real.log (M : ℝ) := by
    rw [hlogM]
    nlinarith
  have hlpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl48 : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by
    nlinarith [hlog2, hlpos, sq_nonneg (Real.log 2 - 0.6931471803)]
  have hLsq : 0.48 * t ^ 2 ≤ Real.log (M : ℝ) ^ 2 := by
    rw [hlogM, mul_pow]
    nlinarith [sq_nonneg t]
  have hcardM : ((twinPrimes M).card : ℝ) ≤
      900 * M / Real.log (M : ℝ) ^ 2 + Real.sqrt M + 1 := card_twinPrimes_le hL32
  have hterm2 : Real.sqrt (M : ℝ) ≤ 2 * P / t ^ 2 := by
    have hsq : (M : ℝ) ≤ (2 * P / t ^ 2) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity), hMR]
      nlinarith [mul_le_mul_of_nonneg_left ht4 hPpos.le]
    calc Real.sqrt (M : ℝ) ≤ Real.sqrt ((2 * P / t ^ 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * P / t ^ 2 := Real.sqrt_sq (by positivity)
  have hcard3753 : ((twinPrimes M).card : ℝ) ≤ 3753 * P / t ^ 2 :=
    sieve_numeric hPpos htpos hMR hLsq hterm2 ht2P hcardM
  -- the block sum, bounded by the count divided by `2ᵏ`
  set S := (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => n.Prime ∧ (n + 2).Prime) with hS
  have hblock : blockSum k = ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by
    rw [hS, Finset.sum_filter, blockSum]
    rfl
  have hterm : ∀ n ∈ S, (1 : ℝ) / (n : ℝ) ≤ 1 / P := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hn
    have hnR : P ≤ (n : ℝ) := by rw [hP]; exact_mod_cast hn.1.1
    exact one_div_le_one_div_of_le hPpos hnR
  have hSsub : S ⊆ twinPrimes M := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hn
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hn.1.2, hn.2⟩
  have hcardle : (S.card : ℝ) ≤ ((twinPrimes M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSsub
  calc blockSum k = ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := hblock
    _ ≤ S.card • ((1 : ℝ) / P) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (S.card : ℝ) * (1 / P) := by rw [nsmul_eq_mul]
    _ ≤ (3753 * P / t ^ 2) * (1 / P) := by
        have h1 : (0 : ℝ) ≤ 1 / P := by positivity
        exact mul_le_mul_of_nonneg_right (hcardle.trans hcard3753) h1
    _ = 3753 / t ^ 2 := by field_simp

/-- Every dyadic block is at most `3753/(k+1)²`. -/
lemma blockSum_le (k : ℕ) : blockSum k ≤ 3753 / ((k : ℝ) + 1) ^ 2 := by
  rcases Nat.lt_or_ge k 46 with hk | hk
  · have hkR : (k : ℝ) ≤ 45 := by exact_mod_cast (by omega : k ≤ 45)
    have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    have hle : ((k : ℝ) + 1) ^ 2 ≤ 2116 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h1 : (1 : ℝ) ≤ 3753 / ((k : ℝ) + 1) ^ 2 := by
      rw [le_div_iff₀ hpos]
      linarith
    exact (blockSum_le_one k).trans h1
  · exact blockSum_le_of_le hk

lemma sum_inv_sq_range_le (K : ℕ) : ∑ k ∈ range K, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 7 / 4 := by
  have hre : ∑ d ∈ Icc 1 K, (1 : ℝ) / (d : ℝ) ^ 2 = ∑ k ∈ range K, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring_nf
  rw [← hre]
  exact sum_inv_sq_Icc_one_le K

lemma sum_twinInv_two_pow_le (K : ℕ) : ∑ n ∈ range (2 ^ K), twinInv n ≤ 6600 := by
  have hstep : ∑ k ∈ range K, blockSum k ≤ ∑ k ∈ range K, 3753 * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have := blockSum_le k
    calc blockSum k ≤ 3753 / ((k : ℝ) + 1) ^ 2 := this
      _ = 3753 * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by ring
  calc ∑ n ∈ range (2 ^ K), twinInv n = ∑ k ∈ range K, blockSum k := sum_twinInv_two_pow K
    _ ≤ ∑ k ∈ range K, 3753 * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) := hstep
    _ = 3753 * ∑ k ∈ range K, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 3753 * (7 / 4) := by
        have := sum_inv_sq_range_le K
        nlinarith
    _ ≤ 6600 := by norm_num

/-- **Brun's bound.**  The reciprocals of the twin primes below `N` sum to at most `6600`,
uniformly in `N`. -/
theorem sum_inv_twinPrimes_le (N : ℕ) : ∑ n ∈ twinPrimes N, (1 : ℝ) / (n : ℝ) ≤ 6600 := by
  have hsub : range N ⊆ range (2 ^ N) := by
    intro n hn
    simp only [Finset.mem_range] at hn ⊢
    exact hn.trans_le Nat.lt_two_pow_self.le
  calc ∑ n ∈ twinPrimes N, (1 : ℝ) / (n : ℝ) = ∑ n ∈ range N, twinInv n :=
        (sum_twinInv_range N).symm
    _ ≤ ∑ n ∈ range (2 ^ N), twinInv n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => twinInv_nonneg n
    _ ≤ 6600 := sum_twinInv_two_pow_le N

lemma sum_range_twinInv_le (N : ℕ) : ∑ n ∈ range N, twinInv n ≤ 6600 := by
  rw [sum_twinInv_range N]
  exact sum_inv_twinPrimes_le N

/-- **Brun's theorem.**  The series `∑ 1/n` over the `n` with `n` and `n + 2` both prime
converges. -/
theorem summable_twinInv : Summable twinInv :=
  summable_of_sum_range_le twinInv_nonneg sum_range_twinInv_le

/-- The sum of the reciprocals of the twin primes is at most `6600`. -/
theorem tsum_twinInv_le : ∑' n, twinInv n ≤ 6600 :=
  Real.tsum_le_of_sum_range_le twinInv_nonneg sum_range_twinInv_le

/-! ## Most primes are not the smaller member of a twin pair -/

/-- The reciprocal `1/n`, restricted to the primes `n` for which `n + 2` is *not* prime. -/
def nonTwinInv (n : ℕ) : ℝ := if n.Prime ∧ ¬ (n + 2).Prime then 1 / (n : ℝ) else 0

/-- The reciprocals of the primes split into the twin and the non-twin part. -/
lemma indicator_prime_eq_twinInv_add_nonTwinInv :
    Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      = fun n => twinInv n + nonTwinInv n := by
  funext n
  by_cases hn : n.Prime
  · by_cases h2 : (n + 2).Prime <;>
      simp [Set.indicator_of_mem, twinInv, nonTwinInv, hn, h2]
  · simp [Set.indicator_of_notMem, twinInv, nonTwinInv, hn]

/-- The reciprocals of the primes `p` with `p + 2` composite diverge: Brun's theorem removes a
convergent part from the divergent sum of the prime reciprocals. -/
theorem not_summable_nonTwinInv : ¬ Summable nonTwinInv := by
  intro h
  refine not_summable_one_div_on_primes ?_
  rw [indicator_prime_eq_twinInv_add_nonTwinInv]
  exact summable_twinInv.add h

/-- **There are infinitely many primes `p` for which `p + 2` is not prime.**  This is a
consequence of Brun's theorem: the twin part of the sum of the prime reciprocals converges,
while the whole sum diverges. -/
theorem infinite_setOf_prime_not_prime_add_two :
    {p : ℕ | p.Prime ∧ ¬ (p + 2).Prime}.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  refine not_summable_nonTwinInv (summable_of_ne_finset_zero (s := hcon.toFinset) ?_)
  intro n hn
  have hmem : ¬ (n.Prime ∧ ¬ (n + 2).Prime) := fun h => hn (hcon.mem_toFinset.2 h)
  simp only [nonTwinInv, if_neg hmem]

end BrunConstant

end RiemannHypothesis
