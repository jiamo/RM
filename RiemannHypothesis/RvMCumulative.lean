/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroSumLogSq

/-!
# The Riemann–von Mangoldt formula in cumulative form: `N(T) = (T/2π) log (T/2πe) + O((log T)²)`

The vendored `Zeta23` library provides the Riemann–von Mangoldt formula on a *dyadic window*:
`|N(T, 2T) − (T/2π)·ℓ₁(T)| ≤ C log T` with `ℓ₁(T) = log T − κ` and
`κ = log(2π) − 2 log 2 + 1`.  Here it is summed over the dyadic decomposition of `(0, T]` to
give the classical *cumulative* statement

`N(0, T) = (T/2π)(log (T/2π) − 1) + O((log T)²)`,   hence   `N(T)/(T log T) → 1/(2π)`.

The constant of the main term survives the summation: the two geometric sums produce exactly
`(T/2π)(log T − κ − 2 log 2) = (T/2π)(log (T/2π) − 1)`, so the error is only the `O((log T)²)`
coming from the `n ≤ log₂ T` window errors, and no term of size `T` is left.

Only the divergent lower bound `N(0, T) ≫ T log T` (`exists_mul_le_windowCount_zero`) was
available before; this determines the constant.

## Method

Writing `T = 2^n s` with `s` in a fixed bounded range, additivity of the zero count gives
`N(0, T) = N(0, s) + ∑_{j < n} N(2^j s, 2^(j+1) s)`.  Each summand is `(2^j s/2π)(log(2^j s) − κ)`
up to `C log T`, and the two geometric sums `∑_{j<n} 2^j = 2^n − 1` and
`∑_{j<n} j 2^j = (n − 2) 2^n + 2` evaluate the main term to `(T/2π)(log (T/2π) − 1) + O(1)`.  The
`n ≤ log₂ T` error terms contribute `O((log T)²)`.

## Main results

* `rvmConst` — the constant `κ = log(2π) − 2 log 2 + 1`.
* `exists_abs_windowCount_sub_main_le` — the window form, restated in the repository's notation.
* `windowCount_eq_add_sum_dyadic` — the dyadic telescoping identity for `N(0, ·)`, from the
  additivity `windowCount_add` of `RiemannHypothesis.PartialProved`.
* `exists_abs_windowCount_zero_sub_rvmMain_le` — the sharp form
  `|N(0,T) − (T/2π)(log (T/2π) − 1)| ≤ A (log T)²`.
* `exists_abs_windowCount_zero_sub_main_le` — its crude corollary
  `|N(0,T) − (T/2π) log T| ≤ A (T + (log T)²)`.
* `tendsto_windowCount_zero_sub_rvmMain_div_atTop` — the `o(T)` form of the sharp statement.
* `tendsto_windowCount_zero_div` — `N(0,T)/(T log T) → 1/(2π)`.

Zeroes are counted **with** multiplicity, as `windowCount` always is.
-/

noncomputable section

open Filter

open scoped Topology

namespace RiemannHypothesis

/-- The constant `κ = log(2π) − 2 log 2 + 1` of the Riemann–von Mangoldt main term:
`ℓ₁(T) = log T − κ`. -/
def rvmConst : ℝ := Real.log (2 * Real.pi) - 2 * Real.log 2 + 1

lemma Zeta23_ell1_eq (T : ℝ) (hT : 0 < T) : Zeta23.ell1 T = Real.log T - rvmConst := by
  rw [Zeta23.ell1, Zeta23.l, rvmConst, Real.log_div (ne_of_gt hT) (by positivity)]
  ring

/-- **The Riemann–von Mangoldt formula on a dyadic window**, in the repository's notation:
`N(T, 2T) = (T/2π)(log T − κ) + O(log T)`. -/
theorem exists_abs_windowCount_sub_main_le :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |(windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * (Real.log T - rvmConst)|
        ≤ C * Real.log T := by
  obtain ⟨C, T₀, hmain⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  refine ⟨max C 1, max T₀ 2, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_right _ _,
    fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have h := hmain T hT₀
  rw [Zeta23_ell1_eq T hT0] at h
  have hN : (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) = (windowCount T (2 * T) : ℝ) := by
    rw [Zeta23.zetaZeroConfig_N, windowCount_eq]
  rw [hN] at h
  exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0)

/-! ## Window additivity and the dyadic telescope -/

/-- Monotonicity of the zero count in the window. -/
theorem windowCount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    windowCount a b ≤ windowCount c d := by
  simp only [windowCount_eq]
  exact Zeta23.Ncount_mono hca hbd

/-- **The dyadic telescope.**  `N(0, 2^n s) = N(0, s) + ∑_{j < n} N(2^j s, 2^(j+1) s)`. -/
theorem windowCount_eq_add_sum_dyadic {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    windowCount 0 ((2 : ℝ) ^ n * s)
      = windowCount 0 s
        + ∑ j ∈ Finset.range n, windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmono : (2 : ℝ) ^ n * s ≤ (2 : ℝ) ^ (n + 1) * s := by
      have : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
        apply pow_le_pow_right₀ (by norm_num); omega
      nlinarith
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ n * s := by positivity
    rw [windowCount_add h0 hmono, ih, Finset.sum_range_succ]
    ring

/-! ## The two geometric sums -/

lemma sum_range_two_pow_real (n : ℕ) : ∑ j ∈ Finset.range n, (2 : ℝ) ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

lemma sum_range_mul_two_pow_real (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) * 2 ^ j = ((n : ℝ) - 2) * 2 ^ n + 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The main term summed over the dyadic blocks `2^j s`, `j < n`. -/
lemma sum_dyadic_main_term (s : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n,
        (2 : ℝ) ^ j * s / (2 * Real.pi) * (Real.log s + (j : ℝ) * Real.log 2 - rvmConst)
      = (2 : ℝ) ^ n * s / (2 * Real.pi) * (Real.log s + (n : ℝ) * Real.log 2)
        - (2 : ℝ) ^ n * s / (2 * Real.pi) * (rvmConst + 2 * Real.log 2)
        + s / (2 * Real.pi) * (rvmConst - Real.log s + 2 * Real.log 2) := by
  have hexp : ∀ j : ℕ,
      (2 : ℝ) ^ j * s / (2 * Real.pi) * (Real.log s + (j : ℝ) * Real.log 2 - rvmConst)
        = (s / (2 * Real.pi) * (Real.log s - rvmConst)) * 2 ^ j
          + (s / (2 * Real.pi) * Real.log 2) * ((j : ℝ) * 2 ^ j) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_range_two_pow_real, sum_range_mul_two_pow_real]
  ring

/-! ## The cumulative estimate -/

/-- Every `T ≥ 2b` can be written as `2^n s` with `b ≤ s ≤ 2b`, and then `n log 2 ≤ log T`. -/
private lemma exists_dyadic_scale {b T : ℝ} (hb2 : 2 ≤ b) (hT : 2 * b ≤ T) :
    ∃ (n : ℕ) (s : ℝ), b ≤ s ∧ s ≤ 2 * b ∧ T = 2 ^ n * s ∧
      (n : ℝ) * Real.log 2 ≤ Real.log T := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hTb1 : (1 : ℝ) ≤ T / b := by rw [le_div_iff₀ hb0]; linarith
  have hTbpos : (0 : ℝ) < T / b := by positivity
  have hL0 : 0 ≤ Real.logb 2 (T / b) := Real.logb_nonneg (by norm_num) hTb1
  refine ⟨⌊Real.logb 2 (T / b)⌋₊, T / 2 ^ (⌊Real.logb 2 (T / b)⌋₊), ?_, ?_, ?_, ?_⟩
  · have hpow_le : (2 : ℝ) ^ (⌊Real.logb 2 (T / b)⌋₊) ≤ T / b := by
      have h1 : (2 : ℝ) ^ ((⌊Real.logb 2 (T / b)⌋₊ : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (Real.logb 2 (T / b)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL0)
      rwa [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hTbpos] at h1
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (⌊Real.logb 2 (T / b)⌋₊))]
    rw [le_div_iff₀ hb0] at hpow_le
    linarith
  · have hpow_gt : T / b < (2 : ℝ) ^ (⌊Real.logb 2 (T / b)⌋₊ + 1) := by
      have h1 : (2 : ℝ) ^ (Real.logb 2 (T / b))
          < (2 : ℝ) ^ (((⌊Real.logb 2 (T / b)⌋₊ + 1 : ℕ) : ℝ)) := by
        refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
        push_cast
        exact Nat.lt_floor_add_one _
      rwa [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hTbpos] at h1
    have h2n : (0 : ℝ) < 2 ^ (⌊Real.logb 2 (T / b)⌋₊) := by positivity
    rw [div_le_iff₀ h2n]
    rw [div_lt_iff₀ hb0] at hpow_gt
    have hpp : (2 : ℝ) ^ (⌊Real.logb 2 (T / b)⌋₊ + 1)
        = 2 * 2 ^ (⌊Real.logb 2 (T / b)⌋₊) := by ring
    nlinarith
  · have h2n : (0 : ℝ) < 2 ^ (⌊Real.logb 2 (T / b)⌋₊) := by positivity
    field_simp
  · have h1 : (⌊Real.logb 2 (T / b)⌋₊ : ℝ) ≤ Real.log (T / b) / Real.log 2 := by
      have := Nat.floor_le hL0
      rwa [Real.logb] at this
    rw [le_div_iff₀ hlog2] at h1
    have h2 : Real.log (T / b) ≤ Real.log T := by
      rw [Real.log_div (ne_of_gt hT0) (ne_of_gt hb0)]
      have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
      linarith
    linarith

/-- **The Riemann–von Mangoldt formula in cumulative form.**  With the classical main term,
including its constant: `|N(0, T) − (T/2π)(log (T/2π) − 1)| ≤ A (log T)²` for all large `T`.

Only the two geometric sums of `sum_dyadic_main_term` are needed beyond the dyadic input
`exists_abs_windowCount_sub_main_le`: the `O(T)` term of the cruder
`exists_abs_windowCount_zero_sub_main_le` below is exactly the constant `log (2π) + 1` of the
main term, and keeping it leaves an error of size only `O((log T)²)`. -/
theorem exists_abs_windowCount_zero_sub_rvmMain_le :
    ∃ A : ℝ, 0 < A ∧ ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
      |(windowCount 0 T : ℝ) - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)|
        ≤ A * (Real.log T) ^ 2 := by
  obtain ⟨C, b, hC0, hb2, hwin⟩ := exists_abs_windowCount_sub_main_le
  have hb0 : (0 : ℝ) < b := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2b : (0 : ℝ) ≤ Real.log (2 * b) := Real.log_nonneg (by linarith)
  obtain ⟨cA, hcA0, hcA⟩ : ∃ cA : ℝ, 0 ≤ cA ∧ cA = (windowCount 0 (2 * b) : ℝ) :=
    ⟨_, Nat.cast_nonneg _, rfl⟩
  obtain ⟨M₁, hM₁0, hM₁⟩ : ∃ M₁ : ℝ, 0 ≤ M₁ ∧
      M₁ = b / Real.pi * (|rvmConst| + Real.log (2 * b) + 2 * Real.log 2) := by
    refine ⟨_, ?_, rfl⟩
    have h : 0 ≤ |rvmConst| + Real.log (2 * b) + 2 * Real.log 2 := by
      have := abs_nonneg rvmConst; linarith
    positivity
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ D = C / Real.log 2 := ⟨_, by positivity, rfl⟩
  refine ⟨cA + M₁ + D + 1, by linarith, max (2 * b) 3, fun T hT => ?_⟩
  have hT2b : 2 * b ≤ T := le_trans (le_max_left _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogT0 : (0 : ℝ) ≤ Real.log T := by linarith
  have hsq : (1 : ℝ) ≤ (Real.log T) ^ 2 := by nlinarith
  -- choose `n` and `s` with `T = 2^n s` and `b ≤ s ≤ 2b`
  obtain ⟨n, s, hsb, hs2b, hTs, hnlogT⟩ := exists_dyadic_scale hb2 hT2b
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hb0 hsb
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlogT : Real.log T = Real.log s + (n : ℝ) * Real.log 2 := by
    rw [hTs, Real.log_mul (ne_of_gt h2n) (ne_of_gt hs0), Real.log_pow]
    ring
  -- the telescope
  have htel := windowCount_eq_add_sum_dyadic hs0.le n
  rw [← hTs] at htel
  have htelR : (windowCount 0 T : ℝ)
      = (windowCount 0 s : ℝ)
        + ∑ j ∈ Finset.range n,
            ((windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) : ℕ) : ℝ) := by
    rw [htel]; push_cast; ring
  -- the blockwise error
  have hblock : ∀ j ∈ Finset.range n,
      |((windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) : ℕ) : ℝ)
          - (2 : ℝ) ^ j * s / (2 * Real.pi)
              * (Real.log s + (j : ℝ) * Real.log 2 - rvmConst)| ≤ C * Real.log T := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hxj0 : (0 : ℝ) < (2 : ℝ) ^ j * s := by positivity
    have hxjb : b ≤ (2 : ℝ) ^ j * s := by nlinarith
    have hxjT : (2 : ℝ) ^ j * s ≤ T := by
      have hle : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hjn.le
      rw [hTs]
      nlinarith
    have hlogxj : Real.log ((2 : ℝ) ^ j * s) = Real.log s + (j : ℝ) * Real.log 2 := by
      rw [Real.log_mul (by positivity) (ne_of_gt hs0), Real.log_pow]
      ring
    have h := hwin ((2 : ℝ) ^ j * s) hxjb
    rw [show ((2 : ℝ) ^ (j + 1) * s) = 2 * ((2 : ℝ) ^ j * s) from by ring, ← hlogxj]
    exact le_trans h (mul_le_mul_of_nonneg_left (Real.log_le_log hxj0 hxjT) hC0.le)
  have hsumerr : |∑ j ∈ Finset.range n,
      (((windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) : ℕ) : ℝ)
        - (2 : ℝ) ^ j * s / (2 * Real.pi)
            * (Real.log s + (j : ℝ) * Real.log 2 - rvmConst))|
      ≤ (n : ℝ) * (C * Real.log T) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hblock) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the main term
  have hmainsum := sum_dyadic_main_term s n
  rw [← hlogT, ← hTs] at hmainsum
  -- the constant of the main term is exactly `κ + 2 log 2`
  have hlogTpi : Real.log (T / (2 * Real.pi)) - 1 = Real.log T - (rvmConst + 2 * Real.log 2) := by
    rw [Real.log_div (ne_of_gt hT0) (by positivity), rvmConst,
      Real.log_mul (by norm_num) (ne_of_gt hpi)]
    ring
  have hdecomp : (windowCount 0 T : ℝ)
        - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)
      = (windowCount 0 s : ℝ)
        + (∑ j ∈ Finset.range n,
            (((windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) : ℕ) : ℝ)
              - (2 : ℝ) ^ j * s / (2 * Real.pi)
                  * (Real.log s + (j : ℝ) * Real.log 2 - rvmConst)))
        + s / (2 * Real.pi) * (rvmConst - Real.log s + 2 * Real.log 2) := by
    rw [hlogTpi, Finset.sum_sub_distrib, hmainsum, htelR]
    ring
  -- bound each piece
  have hpiece1 : (windowCount 0 s : ℝ) ≤ cA := by
    rw [hcA]
    have hmono : windowCount 0 s ≤ windowCount 0 (2 * b) := windowCount_mono (le_refl 0) hs2b
    exact_mod_cast hmono
  have hpiece10 : (0 : ℝ) ≤ (windowCount 0 s : ℝ) := Nat.cast_nonneg _
  have hpiece2 : (n : ℝ) * (C * Real.log T) ≤ D * (Real.log T) ^ 2 := by
    have h1 : (n : ℝ) ≤ Real.log T / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; exact hnlogT
    have h2 : 0 ≤ C * Real.log T := by positivity
    have h3 : (n : ℝ) * (C * Real.log T) ≤ (Real.log T / Real.log 2) * (C * Real.log T) :=
      mul_le_mul_of_nonneg_right h1 h2
    have h4 : (Real.log T / Real.log 2) * (C * Real.log T) = D * (Real.log T) ^ 2 := by
      rw [hD]; field_simp
    linarith
  have hpiece4 : |s / (2 * Real.pi) * (rvmConst - Real.log s + 2 * Real.log 2)| ≤ M₁ := by
    have hlogs : Real.log s ≤ Real.log (2 * b) := Real.log_le_log hs0 hs2b
    have h1 : -|rvmConst| ≤ rvmConst := neg_abs_le _
    have h2 : rvmConst ≤ |rvmConst| := le_abs_self _
    have habs : |rvmConst - Real.log s + 2 * Real.log 2|
        ≤ |rvmConst| + Real.log (2 * b) + 2 * Real.log 2 := by
      rw [abs_le]; constructor <;> linarith
    have hfac : s / (2 * Real.pi) ≤ b / Real.pi := by
      have hid : b / Real.pi - s / (2 * Real.pi) = (2 * b - s) / (2 * Real.pi) := by
        field_simp
      have hnn : (0 : ℝ) ≤ (2 * b - s) / (2 * Real.pi) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s / (2 * Real.pi)), hM₁]
    calc s / (2 * Real.pi) * |rvmConst - Real.log s + 2 * Real.log 2|
        ≤ (b / Real.pi) * |rvmConst - Real.log s + 2 * Real.log 2| :=
          mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ ≤ (b / Real.pi) * (|rvmConst| + Real.log (2 * b) + 2 * Real.log 2) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
  -- put it together
  obtain ⟨he1, he2⟩ := abs_le.mp hsumerr
  obtain ⟨hy1, hy2⟩ := abs_le.mp hpiece4
  have e1 : cA ≤ cA * (Real.log T) ^ 2 := le_mul_of_one_le_right hcA0 hsq
  have e2 : M₁ ≤ M₁ * (Real.log T) ^ 2 := le_mul_of_one_le_right hM₁0 hsq
  have e3 : (0 : ℝ) ≤ cA * (Real.log T) ^ 2 := by positivity
  have e4 : (0 : ℝ) ≤ (Real.log T) ^ 2 := sq_nonneg _
  rw [hdecomp, abs_le]
  constructor <;> linarith

/-- **The Riemann–von Mangoldt formula in cumulative form, crude form.**
`|N(0, T) − (T/2π) log T| ≤ A·(T + (log T)²)` for all large `T`.  This is
`exists_abs_windowCount_zero_sub_rvmMain_le` with the constant `log (2π) + 1` of the main term
thrown into the error. -/
theorem exists_abs_windowCount_zero_sub_main_le :
    ∃ A : ℝ, 0 < A ∧ ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
      |(windowCount 0 T : ℝ) - T / (2 * Real.pi) * Real.log T| ≤ A * (T + (Real.log T) ^ 2) := by
  obtain ⟨A, hA0, T₁, hA⟩ := exists_abs_windowCount_zero_sub_rvmMain_le
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2pi : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ M = (Real.log (2 * Real.pi) + 1) / (2 * Real.pi) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨A + M, by linarith, max T₁ 1, fun T hT => ?_⟩
  have hT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hsplit : T / (2 * Real.pi) * Real.log T
      = T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1) + T * M := by
    rw [Real.log_div (ne_of_gt hT0) (by positivity), hM]
    field_simp
    ring
  obtain ⟨u1, u2⟩ := abs_le.mp (hA T hT₁)
  have hTM : (0 : ℝ) ≤ T * M := by positivity
  have hAT : (0 : ℝ) ≤ A * T := by positivity
  have hMsq : (0 : ℝ) ≤ M * (Real.log T) ^ 2 := by positivity
  have hAsq : (0 : ℝ) ≤ A * (Real.log T) ^ 2 := by positivity
  rw [hsplit, abs_le]
  constructor <;> linarith


/-- **`N(T) ~ (T/2π) log T`.**  The number of nontrivial zeroes of `ζ` with ordinate in `(0, T]`,
counted with multiplicity, divided by `T log T`, tends to `1/(2π)`. -/
theorem tendsto_windowCount_zero_div :
    Tendsto (fun T : ℝ => (windowCount 0 T : ℝ) / (T * Real.log T)) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨A, hA0, T₁, hA⟩ := exists_abs_windowCount_zero_sub_main_le
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [tendsto_iff_dist_tendsto_zero]
  have hg : Tendsto (fun T : ℝ => A / Real.log T + A * (Real.log T / T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => A / Real.log T) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa [Function.comp] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 : Tendsto (fun T : ℝ => A * (Real.log T / T)) atTop (𝓝 0) := by
      simpa using h0.const_mul A
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun T => dist_nonneg) ?_ hg
  filter_upwards [eventually_ge_atTop (max T₁ 2)] with T hT
  have hT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hden : (0 : ℝ) < T * Real.log T := by positivity
  rw [Real.dist_eq]
  have heq : (windowCount 0 T : ℝ) / (T * Real.log T) - 1 / (2 * Real.pi)
      = ((windowCount 0 T : ℝ) - T / (2 * Real.pi) * Real.log T) / (T * Real.log T) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hrhs : (A / Real.log T + A * (Real.log T / T)) * (T * Real.log T)
      = A * (T + (Real.log T) ^ 2) := by
    field_simp
  rw [hrhs]
  exact hA T hT₁

/-- **The Riemann–von Mangoldt formula with `o(T)` error.**  The difference between `N(0, T)` and
the classical main term `(T/2π)(log (T/2π) − 1)` is `o(T)`; indeed it is `O((log T)²)` by
`exists_abs_windowCount_zero_sub_rvmMain_le`. -/
theorem tendsto_windowCount_zero_sub_rvmMain_div_atTop :
    Tendsto (fun T : ℝ => ((windowCount 0 T : ℝ)
        - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)) / T) atTop (𝓝 0) := by
  obtain ⟨A, hA0, T₁, hA⟩ := exists_abs_windowCount_zero_sub_rvmMain_le
  have hg : Tendsto (fun T : ℝ => A * ((Real.log T) ^ 2 / T)) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simp only [one_mul, add_zero] at h0
    simpa using h0.const_mul A
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (max T₁ 1)] with T hT
  have hT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  have hrhs : A * ((Real.log T) ^ 2 / T) * T = A * (Real.log T) ^ 2 := by field_simp
  rw [hrhs]
  exact hA T hT₁

end RiemannHypothesis
