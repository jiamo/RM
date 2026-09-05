/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The divisor bound `τ(n) = O_ε(n^ε)`, and the divisor weight of a product

Weyl's method, as formalized in `RiemannHypothesis.WeylGeneral`, differences a polynomial phase
of degree `d` down to a linear one and is left with a `(d − 1)`-fold sum

`∑_{k₁ < H} ⋯ ∑_{k_{d-1} < H} min(N, 1/(2‖β k₁⋯k_{d-1}‖))`

over the tuples of shifts.  Folding the tuples onto their product `m = k₁⋯k_{d-1}` replaces this
by a one-dimensional sum in which each `m` is counted with the multiplicity of its factorizations
into `d − 1` factors; the classical treatment of that multiplicity is the **divisor bound**

`τ(n) ≤ C_ε n^ε`   for every `ε > 0`,

which is what this file proves.  Mathlib has `Nat.card_divisors` (the factorization formula) and
`Nat.card_divisors_le_self`, but not the `ε`-bound, so it is proved here from scratch.

## Main results

* `exists_pow_bound` : for `ε > 0` there is `K ≥ 1` with `a + 1 ≤ K (2^ε)^a` for every `a : ℕ`;
  Bernoulli's inequality, with `K = max(1, 1/(2^ε − 1))`.
* `exists_card_divisors_le` : **the divisor bound.**  For every `ε > 0` there is `C ≥ 1` with
  `τ(n) ≤ C n^ε` for every `n ≥ 1`.  The proof is the classical one: `τ` is multiplicative, so
  `τ(n)/n^ε = ∏_{p^a ‖ n} (a + 1)/p^{aε}`, and a factor is at most `1` as soon as `p^ε ≥ 2`
  (because `a + 1 ≤ 2^a`) while the remaining primes are the ones below `2^{1/ε}`, of which there
  are at most `⌈2^{1/ε}⌉` and each of which contributes at most `K`.
* `sum_mul_divisor_le` : **the divisor weight of a product.**  For a nonnegative `F`,
  `∑_{k ≤ A} ∑_{u ≤ M} τ(u)^p F(k u) ≤ ∑_{v ≤ A M} τ(v)^{p+1} F(v)`: grouping the pairs `(k, u)`
  by their product `v`, a fibre has at most `τ(v)` elements (the first coordinate divides `v` and
  determines the second) and each of its terms has `τ(u) ≤ τ(v)`.  Iterating this is what turns
  the `r`-fold sum of Weyl's method into a one-dimensional sum with the weight `τ^r`.
* `card_divisors_pow_le` : the two combined, in the form used downstream: for `1 ≤ v ≤ V`,
  `τ(v)^r ≤ (C V^ε)^r`.

Nothing here is conditional, and nothing here uses the Riemann hypothesis.
-/

open Finset

namespace RiemannHypothesis

namespace DivisorBound

/-- **Bernoulli's inequality in the form needed for the divisor bound.**  For `ε > 0` there is a
constant `K ≥ 1` with `a + 1 ≤ K (2^ε)^a` for every natural number `a`. -/
theorem exists_pow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a : ℕ, (a : ℝ) + 1 ≤ K * ((2 : ℝ) ^ ε) ^ a := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ ε :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hε⟩)
  set x : ℝ := (2 : ℝ) ^ ε - 1 with hx
  have hxpos : 0 < x := by simp only [hx, sub_pos]; linarith
  refine ⟨max 1 (1 / x), le_max_left _ _, fun a => ?_⟩
  have hbern : 1 + (a : ℝ) * x ≤ (1 + x) ^ a := one_add_mul_le_pow (by linarith) a
  have hK1 : (1 : ℝ) ≤ max 1 (1 / x) := le_max_left _ _
  have hKx : 1 ≤ max 1 (1 / x) * x := by
    have h : 1 / x ≤ max 1 (1 / x) := le_max_right _ _
    have h' := mul_le_mul_of_nonneg_right h hxpos.le
    rw [div_mul_cancel₀ _ hxpos.ne'] at h'
    linarith
  have h1x : (1 + x) = (2 : ℝ) ^ ε := by simp [hx]
  rw [← h1x]
  nlinarith [hbern, Nat.cast_nonneg (α := ℝ) a,
    mul_le_mul_of_nonneg_left hbern (le_trans zero_le_one hK1)]

/-- `(p^a)^ε = (p^ε)^a` for `p ≥ 0`: the natural power and the real power commute. -/
theorem rpow_pow_comm (p : ℝ) (hp : 0 ≤ p) (a : ℕ) (ε : ℝ) : (p ^ a) ^ ε = (p ^ ε) ^ a := by
  rw [← Real.rpow_natCast p a, ← Real.rpow_mul hp, ← Real.rpow_natCast (p ^ ε) a,
    ← Real.rpow_mul hp, mul_comm]

/-- **The divisor bound.**  For every `ε > 0` there is a constant `C ≥ 1` such that the number of
divisors of `n` is at most `C n^ε` for every `n ≥ 1`.

The proof is the classical one.  By `Nat.card_divisors`, `τ(n) = ∏_{p ∣ n} (a_p + 1)` where
`a_p = v_p(n)`, while `n^ε = ∏_{p ∣ n} (p^{a_p})^ε`; so it suffices to bound each factor
`(a_p + 1)/(p^{a_p})^ε`.  If `p^ε ≥ 2` the factor is at most `1`, since `a + 1 ≤ 2^a`.  Otherwise
`p < 2^{1/ε}`, which happens for at most `⌈2^{1/ε}⌉` primes, and each such factor is at most the
constant `K` of `exists_pow_bound`. -/
theorem exists_card_divisors_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  obtain ⟨K, hK1, hK⟩ := exists_pow_bound hε
  set B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hB
  refine ⟨K ^ B, one_le_pow₀ hK1, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := hn.ne'
  set c : ℕ → ℝ := fun p : ℕ => if (p : ℝ) ^ ε < 2 then K else 1 with hc
  have hnnat : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    conv_lhs => rw [hnnat]
    push_cast
    ring
  have hnrpow : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity), ← hnprod]
  have hterm : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) ≤ c p * (((p : ℝ) ^ (n.factorization p)) ^ ε) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    set a := n.factorization p
    rw [rpow_pow_comm _ hp0]
    by_cases hcase : (p : ℝ) ^ ε < 2
    · have hcp : c p = K := by simp [hc, hcase]
      rw [hcp]
      have h2 : ((2 : ℝ) ^ ε) ^ a ≤ ((p : ℝ) ^ ε) ^ a :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2R hε.le) a
      nlinarith [hK a, h2, le_trans zero_le_one hK1]
    · have hcp : c p = 1 := by simp [hc, hcase]
      rw [hcp, one_mul]
      rw [not_lt] at hcase
      have h2 : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) hcase a
      have h3 : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
        have h3n : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
        exact_mod_cast h3n
      linarith
  have hcard : (#n.divisors : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    push_cast
    ring
  have hprodle : ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (c p * (((p : ℝ) ^ (n.factorization p)) ^ ε)) :=
    Finset.prod_le_prod (fun p _ => by positivity) hterm
  have hsplit : ∏ p ∈ n.primeFactors, (c p * (((p : ℝ) ^ (n.factorization p)) ^ ε))
      = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by
    rw [Finset.prod_mul_distrib, hnrpow]
  have hbad : (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ ε < 2)) ⊆ Finset.range B := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast this
    have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_lt_rpow (by positivity) hp.2 (by positivity)
    have h2 : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
      rw [← Real.rpow_mul hppos.le, mul_one_div, div_self hε.ne', Real.rpow_one]
    rw [h2] at h1
    have h3 : (p : ℝ) < (B : ℝ) := lt_of_lt_of_le h1 (Nat.le_ceil _)
    exact Finset.mem_range.mpr (by exact_mod_cast h3)
  have hprodc : ∏ p ∈ n.primeFactors, c p ≤ K ^ B := by
    have hval : ∏ p ∈ n.primeFactors, c p
        = K ^ (#(n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ ε < 2))) := by
      rw [hc, Finset.prod_ite]
      simp
    rw [hval]
    have hcards := Finset.card_le_card hbad
    rw [Finset.card_range] at hcards
    exact pow_le_pow_right₀ hK1 hcards
  have hnε : (0 : ℝ) ≤ (n : ℝ) ^ ε := by positivity
  calc (#n.divisors : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := hcard
    _ ≤ (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [← hsplit]; exact hprodle
    _ ≤ K ^ B * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprodc hnε

/-- **The divisor weight of a product.**  Grouping the pairs `(k, u)` with `1 ≤ k ≤ A` and
`1 ≤ u ≤ M` by their product `v = k u`, a fibre has at most `τ(v)` elements — the first coordinate
divides `v` and determines the second — and every element of the fibre has `τ(u) ≤ τ(v)`.  Hence
one factor of `τ` is gained for each variable folded in. -/
theorem sum_mul_divisor_le (A M p : ℕ) (F : ℕ → ℝ) (hF : ∀ v, 0 ≤ F v) :
    ∑ k ∈ Finset.Icc 1 A, ∑ u ∈ Finset.Icc 1 M, (#u.divisors : ℝ) ^ p * F (k * u)
      ≤ ∑ v ∈ Finset.Icc 1 (A * M), (#v.divisors : ℝ) ^ (p + 1) * F v := by
  classical
  set s : Finset (ℕ × ℕ) := (Finset.Icc 1 A) ×ˢ (Finset.Icc 1 M) with hs
  set f : ℕ × ℕ → ℝ := fun x => (#x.2.divisors : ℝ) ^ p * F (x.1 * x.2) with hf
  have hmaps : ∀ x ∈ s, x.1 * x.2 ∈ Finset.Icc 1 (A * M) := by
    intro x hx
    simp only [hs, Finset.mem_product, Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (by have := hx.1.1; have := hx.2.1; positivity),
      Nat.mul_le_mul hx.1.2 hx.2.2⟩
  have hLHS : ∑ k ∈ Finset.Icc 1 A, ∑ u ∈ Finset.Icc 1 M, (#u.divisors : ℝ) ^ p * F (k * u)
      = ∑ x ∈ s, f x := by
    rw [hs, Finset.sum_product]
  rw [hLHS, ← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_le_sum ?_
  intro v hv
  rw [Finset.mem_Icc] at hv
  have hv0 : v ≠ 0 := by omega
  set T : Finset (ℕ × ℕ) := {x ∈ s | x.1 * x.2 = v} with hT
  have hcardT : #T ≤ #v.divisors := by
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      simp only [hT, Finset.coe_filter, Set.mem_ofPred_eq] at hx
      simp only [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨⟨x.2, hx.2.symm⟩, hv0⟩
    · intro x hx y hy hxy
      simp only [hT, Finset.coe_filter, Set.mem_ofPred_eq, hs, Finset.mem_product,
        Finset.mem_Icc] at hx hy
      have hxy' : x.1 = y.1 := hxy
      have hx1 : 0 < x.1 := by omega
      have heq : x.1 * x.2 = x.1 * y.2 := by rw [hx.2, hxy', hy.2]
      exact Prod.ext hxy' (Nat.eq_of_mul_eq_mul_left hx1 heq)
  have hnn : (0 : ℝ) ≤ (#v.divisors : ℝ) ^ p * F v := mul_nonneg (by positivity) (hF v)
  have hterm : ∀ x ∈ T, f x ≤ (#v.divisors : ℝ) ^ p * F v := by
    intro x hx
    simp only [hT, Finset.mem_filter] at hx
    have hdvd : x.2 ∣ v := ⟨x.1, by rw [← hx.2]; ring⟩
    have hsub : #x.2.divisors ≤ #v.divisors :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hv0 hdvd)
    have hsubR : (#x.2.divisors : ℝ) ≤ (#v.divisors : ℝ) := by exact_mod_cast hsub
    simp only [hf, hx.2]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsubR p) (hF v)
  calc ∑ x ∈ T, f x ≤ #T • ((#v.divisors : ℝ) ^ p * F v) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (#T : ℝ) * ((#v.divisors : ℝ) ^ p * F v) := by rw [nsmul_eq_mul]
    _ ≤ (#v.divisors : ℝ) * ((#v.divisors : ℝ) ^ p * F v) := by
        have hc : (#T : ℝ) ≤ (#v.divisors : ℝ) := by exact_mod_cast hcardT
        exact mul_le_mul_of_nonneg_right hc hnn
    _ = (#v.divisors : ℝ) ^ (p + 1) * F v := by ring

/-- **The divisor weight, bounded uniformly on `[1, V]`.**  If `τ(n) ≤ C n^ε` for all `n ≥ 1`, then
`τ(v)^r ≤ (C V^ε)^r` for `1 ≤ v ≤ V`. -/
theorem card_divisors_pow_le {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) (r V v : ℕ)
    (hv : 0 < v) (hvV : v ≤ V) :
    (#v.divisors : ℝ) ^ r ≤ (C * (V : ℝ) ^ ε) ^ r := by
  refine pow_le_pow_left₀ (by positivity) ?_ r
  refine (hbound v hv).trans ?_
  have hmono : (v : ℝ) ^ ε ≤ (V : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hvV) hε.le
  exact mul_le_mul_of_nonneg_left hmono (by linarith)

end DivisorBound

end RiemannHypothesis
