/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroExponentOne

/-!
# The order of `∑_{0 < γ ≤ T} 1/‖ρ‖`

`RiemannHypothesis.ZeroExponentOne` shows that `∑_ρ 1/‖ρ‖` diverges.  Here the rate is
determined: the partial sum over the nontrivial zeroes of ordinate in `(0, T]` is `≍ (log T)²`.

Both bounds come from the Riemann–von Mangoldt count on a *dyadic window*: the zeroes with
`2^k < γ ≤ 2^(k+1)` number `≍ 2^k k` and each has modulus between `2^k` and `2^(k+1) + 1`, so
each dyadic block contributes `≍ k` to the sum, and the `≍ log T` blocks up to height `T`
contribute `≍ (log T)²`.

## Main results

* `exists_mul_le_windowCount_dyadic` — `N(T, 2T) ≫ T log T`.
* `exists_mul_le_windowCountDistinct_dyadic` — the same for the distinct zeroes.
* `pairwiseDisjoint_dyadic_windowZeros` — the dyadic windows carry disjoint sets of zeroes.
* `exists_mul_le_sum_inv_norm_block`, `exists_sum_inv_norm_block_le` — a dyadic block
  `2^k < γ ≤ 2^(k+1)` contributes `≍ k` to the sum.
* `exists_mul_log_sq_le_sum_inv_norm` — `∑_{0 < γ ≤ T} 1/‖ρ‖ ≫ (log T)²`.
* `exists_sum_inv_norm_le_mul_log_sq` — `∑_{0 < γ ≤ T} 1/‖ρ‖ ≪ (log T)²`.
* `exists_sum_inv_norm_asymptotic` — the two-sided bound `∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²`.

Zeroes are counted *without* multiplicity in the last statement.
-/

noncomputable section

open Complex Filter Set

open scoped Topology

namespace RiemannHypothesis

/-! ## The Riemann–von Mangoldt count on a dyadic window -/

/-- **The Riemann–von Mangoldt lower bound on a dyadic window.**  The number of nontrivial zeroes
of `ζ` with ordinate in `(T, 2T]`, counted with multiplicity, is `≫ T log T`. -/
theorem exists_mul_le_windowCount_dyadic :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hmain⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := Real.log (2 * Real.pi) - 2 * Real.log 2 + 1 with hK
  refine ⟨1 / (8 * Real.pi), by positivity,
    max (max T₀ 2) (max (Real.exp (2 * K)) (8 * Real.pi * C')), fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTexp : Real.exp (2 * K) ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTC : 8 * Real.pi * C' ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 2 * K ≤ Real.log T := by
    rw [← Real.log_exp (2 * K)]
    exact Real.log_le_log (Real.exp_pos _) hTexp
  have hlogT0 : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hmainT := hmain T hT₀
  have hell : Zeta23.ell1 T = Real.log T - K := by
    rw [Zeta23.ell1, Zeta23.l, hK, Real.log_div (by linarith) (by positivity)]
    ring
  rw [hell] at hmainT
  have habs := abs_le.mp hmainT
  have hNeq : (windowCount T (2 * T) : ℝ) = (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) := by
    rw [windowCount_eq, Zeta23.zetaZeroConfig_N]
  have hN : T / (2 * Real.pi) * (Real.log T - K) - C * Real.log T
      ≤ (windowCount T (2 * T) : ℝ) := by
    rw [hNeq]; linarith [habs.1]
  have hCle : C * Real.log T ≤ T / (8 * Real.pi) * Real.log T := by
    have h1 : C ≤ T / (8 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hlogT0.le
  have hmain2 : T / (2 * Real.pi) * (Real.log T - K) ≥ T / (2 * Real.pi) * (Real.log T / 2) := by
    have hstep : Real.log T - K ≥ Real.log T / 2 := by linarith
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have harith : 1 / (8 * Real.pi) * (T * Real.log T)
      ≤ T / (2 * Real.pi) * (Real.log T / 2) - T / (8 * Real.pi) * Real.log T := by
    have h : T / (2 * Real.pi) * (Real.log T / 2) - T / (8 * Real.pi) * Real.log T
        = 1 / (8 * Real.pi) * (T * Real.log T) := by
      field_simp
      ring
    linarith
  linarith

/-- **The same lower bound for the distinct zeroes**: the number of distinct nontrivial zeroes of
`ζ` with ordinate in `(T, 2T]` is `≫ T log T`. -/
theorem exists_mul_le_windowCountDistinct_dyadic :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (windowCountDistinct T (2 * T) : ℝ) := by
  obtain ⟨c, hc, T₀, hcount⟩ := exists_mul_le_windowCount_dyadic
  obtain ⟨T₁, hdist⟩ := five_sixths_distinct (1 / 6) (by norm_num)
  refine ⟨2 / 3 * c, by positivity, max (max T₀ T₁) 1, fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have h1 : c * (T * Real.log T) ≤ (windowCount T (2 * T) : ℝ) := hcount T hT₀
  have h2 : (5 / 6 - 1 / 6 : ℝ) * (windowCount T (2 * T) : ℝ)
      ≤ (windowCountDistinct T (2 * T) : ℝ) := hdist T hT₁
  have h3 : (5 / 6 - 1 / 6 : ℝ) = 2 / 3 := by norm_num
  rw [h3] at h2
  nlinarith [hc.le]

/-! ## The sum over a dyadic block -/

/-- A nontrivial zero of ordinate in `(a, b]` with `a ≥ 0` has norm at most `1 + b`. -/
theorem norm_le_of_mem_windowZeros_of_nonneg {a b : ℝ} {ρ : ℂ} (ha : 0 ≤ a)
    (hρ : ρ ∈ windowZeros a b) : ‖ρ‖ ≤ 1 + b := by
  obtain ⟨⟨_, hre0, hre1⟩, him0, him1⟩ := hρ
  have h := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_pos hre0, abs_of_pos (lt_of_le_of_lt ha him0)] at h
  linarith

/-- The sum of `1/‖ρ‖` over the nontrivial zeroes of ordinate in `(a, b]` is at least their
number divided by `1 + b`. -/
theorem div_le_sum_inv_norm_windowZeros {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (windowCountDistinct a b : ℝ) / (1 + b)
      ≤ ∑ ρ ∈ (windowZeros_finite a b).toFinset, ‖ρ‖⁻¹ := by
  have hb0 : (0 : ℝ) < 1 + b := by linarith
  have hcard : (windowCountDistinct a b : ℝ) = ((windowZeros_finite a b).toFinset.card : ℝ) := by
    rw [windowCountDistinct, Set.ncard_eq_toFinset_card _ (windowZeros_finite a b)]
  have hterm : ∀ ρ ∈ (windowZeros_finite a b).toFinset, (1 + b)⁻¹ ≤ ‖ρ‖⁻¹ := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hpos : 0 < ‖ρ‖ := by
      obtain ⟨⟨_, hre0, _⟩, _, _⟩ := hρ
      refine norm_pos_iff.mpr fun h => ?_
      rw [h] at hre0
      simp at hre0
    exact inv_anti₀ hpos (norm_le_of_mem_windowZeros_of_nonneg ha hρ)
  calc (windowCountDistinct a b : ℝ) / (1 + b)
      = ∑ _ρ ∈ (windowZeros_finite a b).toFinset, (1 + b)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, div_eq_mul_inv]
    _ ≤ ∑ ρ ∈ (windowZeros_finite a b).toFinset, ‖ρ‖⁻¹ := Finset.sum_le_sum hterm

/-- **Each dyadic block contributes `≫ k`.**  The sum of `1/‖ρ‖` over the nontrivial zeroes of
ordinate in `(2^k, 2^(k+1)]` is at least `c k` for all large `k`. -/
theorem exists_mul_le_sum_inv_norm_block :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      c * k ≤ ∑ ρ ∈ (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset, ‖ρ‖⁻¹ := by
  obtain ⟨c, hc, T₁, hcount⟩ := exists_mul_le_windowCountDistinct_dyadic
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℕ, T₁ < (2 : ℝ) ^ k := pow_unbounded_of_one_lt _ (by norm_num)
  refine ⟨c * Real.log 2 / 4, by positivity, k₀, fun k hk => ?_⟩
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hT₁ : T₁ ≤ (2 : ℝ) ^ k :=
    le_trans hk₀.le (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  have hcount' := hcount ((2 : ℝ) ^ k) hT₁
  have hlog : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := by
    rw [Real.log_pow]
  rw [hlog] at hcount'
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hstep : (windowCountDistinct ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) : ℝ) / (1 + 2 ^ (k + 1))
      ≤ ∑ ρ ∈ (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset, ‖ρ‖⁻¹ :=
    div_le_sum_inv_norm_windowZeros (by positivity) (by positivity)
  refine le_trans ?_ hstep
  rw [le_div_iff₀ (by positivity), hpow]
  have hbig : c * (2 ^ k * (k * Real.log 2))
      ≤ (windowCountDistinct ((2 : ℝ) ^ k) (2 * 2 ^ k) : ℝ) := hcount'
  have hpow' : (windowCountDistinct ((2 : ℝ) ^ k) (2 * 2 ^ k) : ℝ)
      = (windowCountDistinct ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) : ℝ) := by
    rw [hpow]
  rw [hpow'] at hbig
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2k1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hA : (0 : ℝ) ≤ c * Real.log 2 * k := by positivity
  have key : c * Real.log 2 / 4 * k * (1 + 2 * 2 ^ k)
      ≤ c * (2 ^ k * (k * Real.log 2)) := by
    nlinarith [mul_nonneg hA (by linarith : (0:ℝ) ≤ 2 * 2 ^ k - 1)]
  linarith

/-- Zeroes lying in distinct dyadic windows are distinct: the dyadic blocks are pairwise
disjoint. -/
theorem pairwiseDisjoint_dyadic_windowZeros (s : Set ℕ) :
    s.PairwiseDisjoint
      (fun k : ℕ => (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset) := by
  intro k _ l _ hkl
  simp only [Function.onFun, Finset.disjoint_left]
  intro ρ hρk hρl
  simp only [Set.Finite.mem_toFinset] at hρk hρl
  obtain ⟨-, hk1, hk2⟩ := hρk
  obtain ⟨-, hl1, hl2⟩ := hρl
  rcases lt_or_gt_of_ne hkl with h | h
  · have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
    linarith
  · have : (2 : ℝ) ^ (l + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) h
    linarith

/-- **Each dyadic block contributes `O(k)`.**  Every zero in the window `2^k < γ ≤ 2^(k+1)` has
norm at least `2^k`, and by Riemann–von Mangoldt there are `O(2^k k)` of them. -/
theorem exists_sum_inv_norm_block_le :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∑ ρ ∈ (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset, ‖ρ‖⁻¹
        ≤ C * ((k : ℝ) + 1) := by
  obtain ⟨C, hC0, hC⟩ := ncard_nontrivialZeros_le
  refine ⟨2 * C, by positivity, fun k => ?_⟩
  set F : Finset ℂ := (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset with hF
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hterm : ∀ ρ ∈ F, ‖ρ‖⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := by
    intro ρ hρ
    rw [hF, Set.Finite.mem_toFinset] at hρ
    obtain ⟨-, h1, -⟩ := hρ
    exact inv_anti₀ h2k
      (le_trans h1.le (le_trans (le_abs_self _) (Complex.abs_im_le_norm ρ)))
  have hsum : ∑ ρ ∈ F, ‖ρ‖⁻¹ ≤ (F.card : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
    calc ∑ ρ ∈ F, ‖ρ‖⁻¹ ≤ ∑ _ρ ∈ F, ((2 : ℝ) ^ k)⁻¹ := Finset.sum_le_sum hterm
      _ = (F.card : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsub : (F : Set ℂ) ⊆ nontrivialZeros ((2 : ℝ) ^ (k + 1)) := by
    intro ρ hρ
    have hρ' : ρ ∈ F := hρ
    rw [hF, Set.Finite.mem_toFinset] at hρ'
    obtain ⟨⟨hz, hre0, hre1⟩, h1, h2⟩ := hρ'
    exact ⟨hz, hre0, hre1, by rw [abs_of_pos (lt_trans h2k h1)]; exact h2⟩
  have hcard : (F.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
    have h1 : (F : Set ℂ).ncard ≤ (nontrivialZeros ((2 : ℝ) ^ (k + 1))).ncard :=
      Set.ncard_le_ncard hsub (finite_nontrivialZeros _)
    have h2 : (F : Set ℂ).ncard = F.card := Set.ncard_coe_finset F
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [← h2]
    exact le_trans (by exact_mod_cast h1) (hC ((2 : ℝ) ^ (k + 1)) h3)
  have hlog : Real.log ((2 : ℝ) ^ (k + 1)) ≤ (k : ℝ) + 1 := by
    rw [Real.log_pow]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hcard2 : (F.card : ℝ) ≤ 2 * C * 2 ^ k * ((k : ℝ) + 1) := by
    calc (F.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := hcard
      _ ≤ C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 2 * C * 2 ^ k * ((k : ℝ) + 1) := by ring
  calc ∑ ρ ∈ F, ‖ρ‖⁻¹ ≤ (F.card : ℝ) * ((2 : ℝ) ^ k)⁻¹ := hsum
    _ ≤ 2 * C * 2 ^ k * ((k : ℝ) + 1) * ((2 : ℝ) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard2 (by positivity)
    _ = 2 * C * ((k : ℝ) + 1) := by field_simp

/-! ## The lower bound of order `(log T)²` -/

/-- **`∑_{0 < γ ≤ T} 1/‖ρ‖ ≫ (log T)²`.**  The zeroes are counted without multiplicity. -/
theorem exists_mul_log_sq_le_sum_inv_norm :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (Real.log T) ^ 2 ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ := by
  classical
  obtain ⟨c, hc, k₀, hblock⟩ := exists_mul_le_sum_inv_norm_block
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c / (32 * (Real.log 2) ^ 2), by positivity,
    max 4 ((2 : ℝ) ^ (2 * k₀ + 2)), fun T hT => ?_⟩
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hTk : (2 : ℝ) ^ (2 * k₀ + 2) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- the number of dyadic blocks
  set L : ℝ := Real.logb 2 T with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hT1
  set K : ℕ := ⌊L⌋₊ with hK
  have hKL : (K : ℝ) ≤ L := Nat.floor_le hL0
  have hLK : L < K + 1 := Nat.lt_floor_add_one L
  have hpowK : (2 : ℝ) ^ K ≤ T := by
    have h1 : (2 : ℝ) ^ (K : ℝ) ≤ (2 : ℝ) ^ L :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hKL
    rwa [Real.rpow_natCast, hL, Real.rpow_logb (by norm_num) (by norm_num) hT0] at h1
  have hKbig : 2 * k₀ + 2 ≤ K := by
    refine Nat.le_floor ?_
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hT0, Real.rpow_natCast]
    exact hTk
  -- the dyadic blocks `2^k < γ ≤ 2^(k+1)` for `K/2 ≤ k < K`
  set m : ℕ := K / 2 with hm
  have hmK : 2 * m ≤ K := by omega
  have hmK' : K ≤ 2 * m + 1 := by omega
  have hmle : m ≤ K := by omega
  have hk₀m : k₀ ≤ m := by omega
  have hK2 : 2 ≤ K := by omega
  set S : ℕ → Finset ℂ :=
    fun k => (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset with hS
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ico m K) : Set ℕ) S :=
    pairwiseDisjoint_dyadic_windowZeros _
  have hsub : (Finset.Ico m K).biUnion S ⊆ (windowZeros_finite 0 T).toFinset := by
    intro ρ hρ
    rw [Finset.mem_biUnion] at hρ
    obtain ⟨k, hk, hρk⟩ := hρ
    simp only [hS, Set.Finite.mem_toFinset] at hρk ⊢
    obtain ⟨hz, h1, h2⟩ := hρk
    have hpos : (0 : ℝ) < 2 ^ k := by positivity
    have hkK : k + 1 ≤ K := (Finset.mem_Ico.mp hk).2
    have hmono : (2 : ℝ) ^ (k + 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hkK
    exact ⟨hz, by linarith, by linarith⟩
  -- compare the blockwise sum with the full sum
  have hstep1 : ∑ k ∈ Finset.Ico m K, (c * (k : ℝ)) ≤ ∑ k ∈ Finset.Ico m K, ∑ ρ ∈ S k, ‖ρ‖⁻¹ :=
    Finset.sum_le_sum fun k hk => hblock k (le_trans hk₀m (Finset.mem_Ico.mp hk).1)
  have hstep2 : ∑ k ∈ Finset.Ico m K, ∑ ρ ∈ S k, ‖ρ‖⁻¹
      = ∑ ρ ∈ (Finset.Ico m K).biUnion S, ‖ρ‖⁻¹ := (Finset.sum_biUnion hdisj).symm
  have hstep3 : ∑ ρ ∈ (Finset.Ico m K).biUnion S, ‖ρ‖⁻¹
      ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hstep0 : ((K - m : ℕ) : ℝ) * (c * (m : ℝ)) ≤ ∑ k ∈ Finset.Ico m K, (c * (k : ℝ)) := by
    calc ((K - m : ℕ) : ℝ) * (c * (m : ℝ))
        = ∑ _k ∈ Finset.Ico m K, (c * (m : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun k hk => by
          have hkm : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Finset.mem_Ico.mp hk).1
          exact mul_le_mul_of_nonneg_left hkm hc.le
  refine le_trans ?_ (le_trans hstep0 (le_trans hstep1 (le_of_eq hstep2 |>.trans hstep3)))
  -- the remaining estimate is pure arithmetic
  have hcast : ((K - m : ℕ) : ℝ) = (K : ℝ) - (m : ℝ) := Nat.cast_sub hmle
  rw [hcast]
  have hKR2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hmR : (2 : ℝ) * (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
  have hmR' : (K : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hmK'
  have hL2 : (2 : ℝ) ≤ L := le_trans hKR2 hKL
  have hlogTL : Real.log T = L * Real.log 2 := by
    rw [hL, Real.logb]
    field_simp
  rw [hlogTL, mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hprod : L ^ 2 / 32 ≤ ((K : ℝ) - m) * (m : ℝ) := by
    have h1 : L / 4 ≤ (K : ℝ) - m := by linarith
    have h2 : L / 8 ≤ (m : ℝ) := by linarith
    nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith : (0 : ℝ) ≤ (K : ℝ) - m)]
  have hlog2sq : (0 : ℝ) ≤ Real.log 2 ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hprod hc.le)) hlog2sq]

/-! ## The matching upper bound -/

/-- **`∑_{0 < γ ≤ T} 1/‖ρ‖ = O((log T)²)`.**  The zeroes are counted without multiplicity. -/
theorem exists_sum_inv_norm_le_mul_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ≤ C * (Real.log T) ^ 2 := by
  classical
  obtain ⟨C, hC0, hblock⟩ := exists_sum_inv_norm_block_le
  set B : ℝ := ∑ ρ ∈ (windowZeros_finite 0 1).toFinset, ‖ρ‖⁻¹ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(4 * C + B) / (Real.log 2) ^ 2, div_pos (by linarith) (by positivity), 4,
    fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  set L : ℝ := Real.logb 2 T with hL
  have hlogTL : Real.log T = L * Real.log 2 := by
    rw [hL, Real.logb]
    field_simp
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hL2 : (2 : ℝ) ≤ L := by
    have hlogT4 : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    nlinarith
  -- the dyadic decomposition of `(0, T]`
  set K : ℕ := ⌈L⌉₊ with hK
  have hLK : L ≤ (K : ℝ) := Nat.le_ceil L
  have hKL : (K : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hTpow : T ≤ (2 : ℝ) ^ K := by
    have h1 : (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ ((K : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hLK
    rwa [Real.rpow_natCast, hL, Real.rpow_logb (by norm_num) (by norm_num) hT0] at h1
  set S : ℕ → Finset ℂ :=
    fun k => (windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset with hS
  have hsub : (windowZeros_finite 0 T).toFinset ⊆
      (windowZeros_finite 0 1).toFinset ∪ (Finset.range K).biUnion S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨hz, h1, h2⟩ := hρ
    rcases le_or_gt ρ.im 1 with hle | hgt
    · exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact ⟨hz, h1, hle⟩)
    · have hex : ∃ n : ℕ, ρ.im ≤ (2 : ℝ) ^ n := ⟨K, le_trans h2 hTpow⟩
      have hjspec : ρ.im ≤ (2 : ℝ) ^ Nat.find hex := Nat.find_spec hex
      have hj1 : 1 ≤ Nat.find hex := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
        · exfalso; rw [h] at hjspec; norm_num at hjspec; linarith
        · exact h
      have hjm : (2 : ℝ) ^ (Nat.find hex - 1) < ρ.im :=
        not_le.mp (Nat.find_min hex (by omega))
      have hjK : Nat.find hex ≤ K := Nat.find_le (le_trans h2 hTpow)
      refine Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨Nat.find hex - 1, Finset.mem_range.mpr (by omega), ?_⟩)
      simp only [hS, Set.Finite.mem_toFinset]
      refine ⟨hz, hjm, ?_⟩
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
      exact hjspec
  have hsplit : ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹
      ≤ ∑ ρ ∈ (windowZeros_finite 0 1).toFinset ∪ (Finset.range K).biUnion S, ‖ρ‖⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hunion : ∑ ρ ∈ (windowZeros_finite 0 1).toFinset ∪ (Finset.range K).biUnion S, ‖ρ‖⁻¹
      ≤ B + ∑ ρ ∈ (Finset.range K).biUnion S, ‖ρ‖⁻¹ := by
    have h := Finset.sum_union_inter (s₁ := (windowZeros_finite 0 1).toFinset)
      (s₂ := (Finset.range K).biUnion S) (f := fun ρ : ℂ => ‖ρ‖⁻¹)
    have hi : 0 ≤ ∑ ρ ∈ (windowZeros_finite 0 1).toFinset ∩ (Finset.range K).biUnion S, ‖ρ‖⁻¹ :=
      Finset.sum_nonneg fun _ _ => by positivity
    rw [hB]
    linarith
  have hbi : ∑ ρ ∈ (Finset.range K).biUnion S, ‖ρ‖⁻¹
      = ∑ k ∈ Finset.range K, ∑ ρ ∈ S k, ‖ρ‖⁻¹ :=
    Finset.sum_biUnion (pairwiseDisjoint_dyadic_windowZeros _)
  have hblocks : ∑ ρ ∈ (Finset.range K).biUnion S, ‖ρ‖⁻¹ ≤ C * (K : ℝ) ^ 2 := by
    rw [hbi]
    calc ∑ k ∈ Finset.range K, ∑ ρ ∈ S k, ‖ρ‖⁻¹ ≤ ∑ _k ∈ Finset.range K, C * (K : ℝ) :=
          Finset.sum_le_sum fun k hk => le_trans (hblock k) (by
            have hkK : (k : ℝ) + 1 ≤ (K : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
            exact mul_le_mul_of_nonneg_left hkK hC0.le)
      _ = (K : ℝ) * (C * (K : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C * (K : ℝ) ^ 2 := by ring
  have hKR : (K : ℝ) ≤ 2 * L := by linarith
  have hKR0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hfin : B + C * (K : ℝ) ^ 2 ≤ (4 * C + B) * L ^ 2 := by
    have hKsq : (K : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
      nlinarith [mul_le_mul hKR hKR hKR0 (by linarith : (0 : ℝ) ≤ 2 * L)]
    have h1 : C * (K : ℝ) ^ 2 ≤ 4 * C * L ^ 2 := by nlinarith [hC0.le]
    have h2 : B ≤ B * L ^ 2 := le_mul_of_one_le_right hB0 (by nlinarith)
    nlinarith
  have hrhs : (4 * C + B) / (Real.log 2) ^ 2 * (Real.log T) ^ 2 = (4 * C + B) * L ^ 2 := by
    rw [hlogTL, mul_pow]
    field_simp
  rw [hrhs]
  linarith

/-- **`∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²`.**  Combining the two bounds: the partial sums of the
reciprocals of the moduli of the nontrivial zeroes grow exactly like `(log T)²`. -/
theorem exists_sum_inv_norm_asymptotic :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (Real.log T) ^ 2 ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ∧
        ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ≤ C * (Real.log T) ^ 2 := by
  obtain ⟨c, hc, T₁, hlow⟩ := exists_mul_log_sq_le_sum_inv_norm
  obtain ⟨C, hC, T₂, hupp⟩ := exists_sum_inv_norm_le_mul_log_sq
  exact ⟨c, C, hc, hC, max T₁ T₂, fun T hT =>
    ⟨hlow T (le_trans (le_max_left _ _) hT), hupp T (le_trans (le_max_right _ _) hT)⟩⟩

end RiemannHypothesis
