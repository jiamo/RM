/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MoebiusOverNCriterion

/-!
# Elementary sums of the Möbius function

The two hyperbola reindexings of the set of pairs `(d, e)` with `d · e ≤ m`, and the two
classical elementary consequences for the Möbius function:

* `sum_moebius_mul_div` : `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1` for `N ≥ 1`;
* `abs_littleMertens_le_one` : **Landau's inequality** `|∑_{n ≤ N} μ(n)/n| ≤ 1`, for every `N`.

The second is the elementary (and unconditional) counterpart of the criterion in
`RiemannHypothesis.MoebiusOverNCriterion`, where the *quantitative* bound
`∑_{n ≤ N} μ(n)/n = O(N^{-1/2+ε})` is shown to imply the Riemann hypothesis.  Landau's
inequality gives that sum bounded by `1`, with no cancellation beyond the trivial one; it is
very far from the square-root bound, and nothing here proves the hypothesis.

## Proofs

Both hyperbola identities are the same bijection `(d, e) ↦ (d·e, e)` between the pairs with
`d·e ≤ m` and the pairs `(k, e)` with `k ≤ m` and `e ∣ k`; they differ only in which of the two
coordinates the summand depends on.  Landau's inequality follows from
`∑_{n ≤ N} μ(n)⌊N/n⌋ = 1` by replacing `⌊N/n⌋` with `N/n` at the cost of the `N - 1` fractional
parts, each of absolute value at most one (the term `n = 1` contributes nothing).
-/

noncomputable section

open Filter Finset ArithmeticFunction

namespace RiemannHypothesis

/-- The sum of `μ` over the divisors of `k`: `1` if `k = 1`, and `0` otherwise. -/
lemma sum_divisors_moebius {k : ℕ} : ∑ d ∈ k.divisors, moebius d = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.one_apply] using h

/-- Reindexing the pairs `(d, e)` with `d · e ≤ m`, for a summand depending on the *second*
coordinate: summing over `d` first, or over the product `k = d · e` first. -/
lemma sum_pairs_inner (m : ℕ) (f : ℕ → ℤ) :
    ∑ d ∈ Icc 1 m, ∑ e ∈ Icc 1 (m / d), f e = ∑ k ∈ Icc 1 m, ∑ e ∈ k.divisors, f e := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.1 * p.2, p.2⟩) (j := fun p => ⟨p.1 / p.2, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h
    obtain ⟨⟨hd1, hdm⟩, he1, hem⟩ := h
    have hd0 : 0 < d := hd1
    have hde : d * e ≤ m := by
      rw [Nat.le_div_iff_mul_le hd0] at hem
      rwa [Nat.mul_comm]
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hde⟩,
      ⟨d, by ring⟩, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨k, e⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at h
    obtain ⟨⟨hk1, hkm⟩, hek, hk0⟩ := h
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hek (by omega)
    have hke : 0 < k / e := (Nat.one_le_div_iff he0).mpr (Nat.le_of_dvd (by omega) hek)
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨hke, le_trans (Nat.div_le_self _ _) hkm⟩, he0, ?_⟩
    rw [Nat.le_div_iff_mul_le hke]
    calc e * (k / e) = k := Nat.mul_div_cancel' hek
      _ ≤ m := hkm
  · rintro ⟨d, e⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h
    have he0 : 0 < e := h.2.1
    simp [Nat.mul_div_cancel _ he0]
  · rintro ⟨k, e⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h
    have hek := h.2.1
    simp [Nat.div_mul_cancel hek]
  · rintro ⟨d, e⟩ _
    rfl

/-- Reindexing the pairs `(e, d)` with `e · d ≤ m`, for a summand depending on the *first*
coordinate.  The inner sum is constant, so the left-hand side is `∑_e ⌊m/e⌋ f(e)`. -/
lemma sum_pairs_outer (m : ℕ) (f : ℕ → ℤ) :
    ∑ e ∈ Icc 1 m, ∑ _d ∈ Icc 1 (m / e), f e = ∑ k ∈ Icc 1 m, ∑ e ∈ k.divisors, f e := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.1 * p.2, p.1⟩) (j := fun p => ⟨p.2, p.1 / p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, d⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h
    obtain ⟨⟨he1, hem⟩, hd1, hdm⟩ := h
    have he0 : 0 < e := he1
    have hde : e * d ≤ m := by
      rw [Nat.le_div_iff_mul_le he0] at hdm
      rwa [Nat.mul_comm]
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hde⟩,
      ⟨d, rfl⟩, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨k, e⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at h
    obtain ⟨⟨hk1, hkm⟩, hek, hk0⟩ := h
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hek (by omega)
    have hke : 0 < k / e := (Nat.one_le_div_iff he0).mpr (Nat.le_of_dvd (by omega) hek)
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨he0, le_trans (Nat.le_of_dvd (by omega) hek) hkm⟩, hke, ?_⟩
    rw [Nat.le_div_iff_mul_le he0]
    calc k / e * e = k := Nat.div_mul_cancel hek
      _ ≤ m := hkm
  · rintro ⟨e, d⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h
    have he0 : 0 < e := h.1.1
    simp [Nat.mul_div_cancel_left _ he0]
  · rintro ⟨k, e⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h
    have hek := h.2.1
    simp [Nat.mul_div_cancel' hek]
  · rintro ⟨e, d⟩ _
    rfl

/-- `∑_{k ≤ m} ∑_{e ∣ k} μ(e) = 1` for `m ≥ 1`: only `k = 1` contributes. -/
lemma sum_Icc_sum_divisors_moebius {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Icc 1 m, ∑ e ∈ k.divisors, moebius e = 1 := by
  have h : ∀ k ∈ Icc 1 m, (∑ e ∈ k.divisors, moebius e) = if k = 1 then 1 else 0 :=
    fun k _ => sum_divisors_moebius
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Icc 1 m) 1 (fun _ => (1 : ℤ))]
  simp [hm]

/-- **`∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1`** for every `N ≥ 1`. -/
theorem sum_moebius_mul_div {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℤ) * moebius n = 1 := by
  rw [← sum_Icc_sum_divisors_moebius hN, ← sum_pairs_outer N moebius]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_const, Nat.card_Icc]
  simp

/-- **Landau's inequality**: the weighted Mertens sums satisfy `|∑_{n ≤ N} μ(n)/n| ≤ 1`. -/
theorem abs_littleMertens_le_one (N : ℕ) : |littleMertens N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [littleMertens]
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hsplit : (N : ℝ) * littleMertens N
        = ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * (moebius n : ℝ)
          + ∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ) := by
      rw [← Finset.sum_add_distrib, littleMertens, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have hone : ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℝ) * (moebius n : ℝ) = 1 := by
      have h2 : ((∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℤ) * moebius n : ℤ) : ℝ) = 1 := by
        rw [sum_moebius_mul_div hN]; norm_num
      rw [← h2, Int.cast_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [Int.cast_mul, Int.cast_natCast]
    have hbound : ∀ n ∈ Icc 1 N,
        |((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)| ≤ if n = 1 then 0 else 1 := by
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
      have hmu : |(moebius n : ℝ)| ≤ 1 := by
        have := abs_moebius_le_one (n := n)
        exact_mod_cast this
      by_cases h1 : n = 1
      · subst h1
        simp
      · simp only [h1, if_false]
        rw [abs_mul]
        have h0 : |(N : ℝ) / n - ((N / n : ℕ) : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        calc |(N : ℝ) / n - ((N / n : ℕ) : ℝ)| * |(moebius n : ℝ)|
            ≤ 1 * 1 := mul_le_mul h0 hmu (abs_nonneg _) zero_le_one
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
    have hfrac : |∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)|
        ≤ (N : ℝ) - 1 :=
      calc |∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)|
          ≤ ∑ n ∈ Icc 1 N, |((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Icc 1 N, (if n = 1 then (0 : ℝ) else 1) := Finset.sum_le_sum hbound
        _ = (N : ℝ) - 1 := hcount
    have hmain : |(N : ℝ) * littleMertens N| ≤ (N : ℝ) := by
      rw [hsplit, hone]
      calc |1 + ∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)|
          ≤ 1 + |∑ n ∈ Icc 1 N, ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) * (moebius n : ℝ)| :=
            (abs_add_le _ _).trans (by simp)
        _ ≤ 1 + ((N : ℝ) - 1) := by linarith
        _ = N := by ring
    rw [abs_mul, abs_of_pos hN0] at hmain
    calc |littleMertens N| = ((N : ℝ) * |littleMertens N|) / N := by field_simp
      _ ≤ (N : ℝ) / N := by gcongr
      _ = 1 := by field_simp

end RiemannHypothesis
