/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MertensSums
import RiemannHypothesis.LiouvilleCriterion

/-!
# Elementary sums of the Liouville function

The Liouville analogue of `RiemannHypothesis.MertensSums`.  Because `∑_{d ∣ k} λ(d)` is the
indicator function of the squares (`RiemannHypothesis.zeta_mul_liouvilleAF`), the hyperbola
reindexing `sum_pairs_outer` turns into the classical identity

* `sum_liouville_mul_div` : `∑_{n ≤ N} λ(n) ⌊N/n⌋ = ⌊√N⌋`,

the Liouville counterpart of `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1`.  Replacing `⌊N/n⌋` by `N/n` at the
cost of the fractional parts gives the elementary bound

* `abs_littleLiouville_sub_le_one` : `|∑_{n ≤ N} λ(n)/n − ⌊√N⌋/N| ≤ 1`.

Both are unconditional and elementary.  They are very far from the square-root cancellation
`LiouvilleBoundForm` of `RiemannHypothesis.LiouvilleCriterion`, which is what implies the
Riemann hypothesis; nothing here proves the hypothesis.
-/

noncomputable section

open Filter Finset ArithmeticFunction

namespace RiemannHypothesis

/-- The sum of `λ` over the divisors of `k` is `1` if `k` is a square and `0` otherwise. -/
lemma sum_divisors_liouville {k : ℕ} (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, liouville d = if IsSquare k then 1 else 0 := by
  classical
  have h := congrArg (fun f : ArithmeticFunction ℂ => f k) zeta_mul_liouvilleAF
  simp only [ArithmeticFunction.coe_zeta_mul_apply] at h
  rw [sqAF_apply_of_ne_zero hk] at h
  have hcast : ((∑ d ∈ k.divisors, liouville d : ℤ) : ℂ)
      = ∑ d ∈ k.divisors, liouvilleAF d := by
    push_cast
    rfl
  have hval : ((∑ d ∈ k.divisors, liouville d : ℤ) : ℂ) = if IsSquare k then 1 else 0 := by
    rw [hcast, h]
  by_cases hsq : IsSquare k
  · rw [if_pos hsq] at hval ⊢
    exact_mod_cast hval
  · rw [if_neg hsq] at hval ⊢
    exact_mod_cast hval

/-- The squares in `[1, m]` are exactly the `j²` with `1 ≤ j ≤ ⌊√m⌋`. -/
lemma filter_isSquare_Icc (m : ℕ) :
    {k ∈ Icc 1 m | IsSquare k} = (Icc 1 (Nat.sqrt m)).image (fun j => j ^ 2) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hk1, hkm⟩, r, rfl⟩
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · simp at hk1
      · exact h
    refine ⟨r, ⟨hr1, ?_⟩, by ring⟩
    exact Nat.le_sqrt.mpr hkm
  · rintro ⟨j, ⟨hj1, hjm⟩, rfl⟩
    refine ⟨⟨Nat.one_le_pow _ _ hj1, ?_⟩, j, by ring⟩
    calc j ^ 2 ≤ Nat.sqrt m ^ 2 := Nat.pow_le_pow_left hjm 2
      _ ≤ m := Nat.sqrt_le' m

/-- `∑_{k ≤ m} [k is a square] = ⌊√m⌋`. -/
lemma sum_Icc_ite_isSquare (m : ℕ) :
    ∑ k ∈ Icc 1 m, (if IsSquare k then (1 : ℤ) else 0) = Nat.sqrt m := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, filter_isSquare_Icc,
    Finset.card_image_of_injective _ (fun a b hab => by
      simpa using Nat.pow_left_injective (two_ne_zero) hab), Nat.card_Icc]
  simp

/-- `∑_{k ≤ m} ∑_{e ∣ k} λ(e) = ⌊√m⌋`. -/
lemma sum_Icc_sum_divisors_liouville (m : ℕ) :
    ∑ k ∈ Icc 1 m, ∑ e ∈ k.divisors, liouville e = Nat.sqrt m := by
  classical
  rw [← sum_Icc_ite_isSquare m]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  exact sum_divisors_liouville (by omega)

/-- **`∑_{n ≤ N} λ(n) ⌊N/n⌋ = ⌊√N⌋`** for every `N`. -/
theorem sum_liouville_mul_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℤ) * liouville n = Nat.sqrt N := by
  rw [← sum_Icc_sum_divisors_liouville N, ← sum_pairs_outer N (fun n => liouville n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_const, Nat.card_Icc]
  simp

/-- The weighted Liouville sums `∑_{n ≤ N} λ(n)/n`. -/
def littleLiouville (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (liouville n : ℝ) / n

/-- The elementary bound coming from `∑_{n ≤ N} λ(n) ⌊N/n⌋ = ⌊√N⌋`: the weighted Liouville sum
differs from `⌊√N⌋/N` by at most `1`. -/
theorem abs_littleLiouville_sub_le_one (N : ℕ) :
    |littleLiouville N - (Nat.sqrt N : ℝ) / N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [littleLiouville]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : (N : ℝ) * littleLiouville N
      = ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * (liouville n : ℝ)
        + ∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (liouville n : ℝ) := by
    rw [← Finset.sum_add_distrib, littleLiouville, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hone : ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * (liouville n : ℝ) = (Nat.sqrt N : ℝ) := by
    have h2 : ((∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℤ) * liouville n : ℤ) : ℝ) = (Nat.sqrt N : ℝ) := by
      rw [sum_liouville_mul_div N]; norm_num
    rw [← h2, Int.cast_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Int.cast_mul, Int.cast_natCast]
  have hbound : ∀ n ∈ Icc 1 N,
      |((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (liouville n : ℝ)| ≤ if n = 1 then 0 else 1 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : 0 < n := hn.1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlow : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
      rw [le_div_iff₀ hnR]
      exact_mod_cast Nat.div_mul_le_self N n
    have hhigh : (N : ℝ) / n < ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hnR]
      have hlt : N < (N / n + 1) * n := by nlinarith [Nat.div_add_mod N n, Nat.mod_lt N hn0]
      exact_mod_cast hlt
    have hlam : |(liouville n : ℝ)| ≤ 1 := by
      have h := norm_liouvilleAF_le n
      rw [liouvilleAF, ArithmeticFunction.intCoe_apply, Complex.norm_intCast] at h
      exact_mod_cast h
    by_cases h1 : n = 1
    · subst h1
      simp
    · simp only [h1, if_false]
      rw [abs_mul]
      have h0 : |(N : ℝ) / n - ((N / n : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      calc |(N : ℝ) / n - ((N / n : ℕ) : ℝ)| * |(liouville n : ℝ)|
          ≤ 1 * 1 := mul_le_mul h0 hlam (abs_nonneg _) zero_le_one
        _ = 1 := by ring
  have hcount : ∑ n ∈ Icc 1 N, (if n = 1 then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
    have hrw : ∀ n ∈ Icc 1 N,
        (if n = 1 then (0 : ℝ) else 1) = 1 - (if n = 1 then (1 : ℝ) else 0) := by
      intro n _
      split <;> ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' (Icc 1 N) 1 (fun _ => (1 : ℝ)), Finset.sum_const, Nat.card_Icc,
      if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)]
    simp
  have hfrac : |∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (liouville n : ℝ)|
      ≤ (N : ℝ) - 1 :=
    calc |∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (liouville n : ℝ)|
        ≤ ∑ n ∈ Icc 1 N, |((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (liouville n : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, (if n = 1 then (0 : ℝ) else 1) := Finset.sum_le_sum hbound
      _ = (N : ℝ) - 1 := hcount
  have hmain : |(N : ℝ) * littleLiouville N - (Nat.sqrt N : ℝ)| ≤ (N : ℝ) - 1 := by
    rw [hsplit, hone]
    simpa using hfrac
  have hkey : |(N : ℝ) * (littleLiouville N - (Nat.sqrt N : ℝ) / N)| ≤ (N : ℝ) - 1 := by
    have : (N : ℝ) * (littleLiouville N - (Nat.sqrt N : ℝ) / N)
        = (N : ℝ) * littleLiouville N - (Nat.sqrt N : ℝ) := by
      field_simp
    rw [this]
    exact hmain
  rw [abs_mul, abs_of_pos hN0] at hkey
  calc |littleLiouville N - (Nat.sqrt N : ℝ) / N|
      = ((N : ℝ) * |littleLiouville N - (Nat.sqrt N : ℝ) / N|) / N := by field_simp
    _ ≤ ((N : ℝ) - 1) / N := by gcongr
    _ ≤ 1 := by rw [div_le_one hN0]; linarith

end RiemannHypothesis
