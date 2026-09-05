/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BrunTitchmarsh

/-!
# Brun's theorem for the twin primes, from the large sieve

`RiemannHypothesis.BrunTitchmarsh` runs Montgomery's sieve of `M2-LARGE-SIEVE-SQUAREFREE` at the
weights `w p = p − 1`, one forbidden residue class for each prime.  Here the same sieve is run at
the weights `w p = p − 2` for the odd primes: a `n` with `n` and `n + 2` both prime and `n > Q`
misses *two* classes modulo every odd prime `p ≤ Q`, namely `0` and `p − 2`.  The sifting sum is
then of size `(log Q)²` rather than `log Q`, and the sieve gives the twin-prime upper bound of
Brun's theorem.

## Main results

* `twinSiftSum` — the sifting sum of the large sieve at the twin-prime weights.
* `twinSiftSum_ge` — `twinSiftSum Q ≥ (9/16) ((log √Q)/2 − 1/2)²`, of order `(log Q)²`.
* `card_mul_twinSiftSum_le` — the sieve: a set `A ⊆ [0, N)` missing two residue classes modulo
  every odd prime `p ≤ Q` and one class modulo `2` satisfies `|A| · twinSiftSum Q ≤ Q² + π N`.
* `card_twinPrimes_le` — **Brun's twin-prime bound**: the number of `n < N` with `n` and `n + 2`
  both prime is at most `900 N / (log N)² + √N + 1`, once `log N ≥ 32`.

## Scope

The constant `900` is an honest artefact of the crude bounds used, exactly as in
`RiemannHypothesis.BrunTitchmarsh`: the factor `π` of this repository's large sieve in place of
the sharp `1`, the rigid choice `Q = ⌊√N⌋` which halves the logarithm, the estimate `9/16` for
the coprimality loss in the sifting sum, and the estimate `∏_{p ∣ q} 2/(p − 1)` in place of the
singular series.  The sharp form of the sieve gives `(8 + o(1)) C₂ N / (log N)²`.  Nothing about
the *lower* order of the twin primes is proved (that is the twin-prime conjecture, open), and
nothing about `ζ` follows.  The convergence of `∑ 1/p` over the twin primes — Brun's theorem —
is drawn from `card_twinPrimes_le` in `RiemannHypothesis.BrunConstant`.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace BrunTwinPrimes

open LargeSieveSquarefree BrunTitchmarsh

/-! ## The sifting sum at the twin-prime weights -/

/-- The number of residue classes modulo `p` that a twin-prime pair can occupy: one class modulo
`2`, and `p − 2` classes modulo an odd prime `p`. -/
def twinWeight (p : ℕ) : ℕ := if p = 2 then 1 else p - 2

/-- The sifting sum of the large sieve at the twin-prime weights, that is
`∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/w p`, whose odd factors are `2/(p − 2)`. -/
def twinSiftSum (Q : ℕ) : ℝ :=
  ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors,
    (((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ))

/-- The odd squarefree numbers up to `X`. -/
def oddSquarefreeUpTo (X : ℕ) : Finset ℕ := (squarefreeUpTo X).filter (fun d => ¬ 2 ∣ d)

/-- The multiplicative weight `∏_{p ∣ d} 1/(p − 1)` of the sifting sum of `BrunTitchmarsh`. -/
def sieveWeight (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)

/-- The total weight of the odd squarefree numbers up to `X`. -/
def oddSieveTotal (X : ℕ) : ℝ := ∑ d ∈ oddSquarefreeUpTo X, sieveWeight d

/-! ## Elementary properties of the weights -/

theorem sieveWeight_nonneg (d : ℕ) : 0 ≤ sieveWeight d := by
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  exact div_nonneg zero_le_one (by linarith)

theorem oddSieveTotal_nonneg (X : ℕ) : 0 ≤ oddSieveTotal X :=
  Finset.sum_nonneg fun d _ => sieveWeight_nonneg d

theorem mem_oddSquarefreeUpTo {X d : ℕ} :
    d ∈ oddSquarefreeUpTo X ↔ ((1 ≤ d ∧ d ≤ X) ∧ Squarefree d) ∧ ¬ 2 ∣ d := by
  simp [oddSquarefreeUpTo, mem_squarefreeUpTo]

/-- `∏_{p ∣ a b} 1/(p − 1) = (∏_{p ∣ a} 1/(p − 1)) (∏_{p ∣ b} 1/(p − 1))` for coprime `a, b`. -/
theorem sieveWeight_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    sieveWeight (a * b) = sieveWeight a * sieveWeight b := by
  unfold sieveWeight
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

/-! ## The odd harmonic sum -/

/-- The reciprocals of the odd `m ≤ X` sum to at least `(log X)/2 − 1/2`. -/
theorem half_log_sub_half_le_sum_inv_odd (X : ℕ) :
    Real.log X / 2 - 1 / 2 ≤ ∑ m ∈ (Icc 1 X).filter (fun m => ¬ 2 ∣ m), (1 : ℝ) / m := by
  classical
  have hsplit : ∑ m ∈ (Icc 1 X).filter (fun m => 2 ∣ m), (1 : ℝ) / m
      + ∑ m ∈ (Icc 1 X).filter (fun m => ¬ 2 ∣ m), (1 : ℝ) / m = ∑ m ∈ Icc 1 X, (1 : ℝ) / m :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have himg : (Icc 1 X).filter (fun m => 2 ∣ m) = (Icc 1 (X / 2)).image (fun k => 2 * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  have heven : ∑ m ∈ (Icc 1 X).filter (fun m => 2 ∣ m), (1 : ℝ) / m
      = 1 / 2 * ∑ k ∈ Icc 1 (X / 2), (1 : ℝ) / k := by
    rw [himg, Finset.sum_image
      (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by norm_num) h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    push_cast
    field_simp
  have hupper : ∑ k ∈ Icc 1 (X / 2), (1 : ℝ) / k ≤ Real.log X + 1 := by
    refine le_trans (sum_inv_le_log_add_one (X / 2)) ?_
    have hle : Real.log ((X / 2 : ℕ) : ℝ) ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos (X / 2) with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.log_zero]
        rcases Nat.eq_zero_or_pos X with hX | hX
        · simp [hX]
        · exact Real.log_nonneg (by exact_mod_cast hX)
      · refine Real.log_le_log (by exact_mod_cast h) ?_
        exact_mod_cast Nat.div_le_self X 2
    linarith
  have hlower : Real.log X ≤ ∑ m ∈ Icc 1 X, (1 : ℝ) / m := log_le_sum_inv X
  rw [heven] at hsplit
  linarith

/-- Every odd `m ≤ X` lies in the fibre of its radical, which is odd, squarefree and at most `m`;
with the fibre bound `sum_inv_primeFactors_eq_le` this dominates the odd harmonic sum. -/
theorem sum_inv_odd_le_oddSieveTotal (X : ℕ) :
    ∑ m ∈ (Icc 1 X).filter (fun m => ¬ 2 ∣ m), (1 : ℝ) / m ≤ oddSieveTotal X := by
  classical
  have hsub : (Icc 1 X).filter (fun m => ¬ 2 ∣ m) ⊆ (oddSquarefreeUpTo X).biUnion
      (fun d => (Icc 1 X).filter (fun m => m.primeFactors = d.primeFactors)) := by
    intro n hn
    obtain ⟨hnI, hodd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hnI
    set d := ∏ p ∈ n.primeFactors, p with hd
    have hdvd : d ∣ n := Nat.prod_primeFactors_dvd n
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by
      intro h
      rw [h] at hdle hdvd
      omega)
    have hdsf : Squarefree d := squarefree_prod_primeFactors n
    have hdpf : d.primeFactors = n.primeFactors :=
      Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
    have hdodd : ¬ 2 ∣ d := by
      intro h2
      exact hodd (dvd_trans h2 hdvd)
    refine Finset.mem_biUnion.2 ⟨d, mem_oddSquarefreeUpTo.2 ⟨⟨⟨hdpos, le_trans hdle hn2⟩, hdsf⟩,
      hdodd⟩, Finset.mem_filter.2 ⟨hnI, by rw [hdpf]⟩⟩
  calc ∑ m ∈ (Icc 1 X).filter (fun m => ¬ 2 ∣ m), (1 : ℝ) / m
      ≤ ∑ n ∈ (oddSquarefreeUpTo X).biUnion
          (fun d => (Icc 1 X).filter (fun m => m.primeFactors = d.primeFactors)), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ d ∈ oddSquarefreeUpTo X,
          ∑ m ∈ (Icc 1 X).filter (fun m => m.primeFactors = d.primeFactors), (1 : ℝ) / m :=
        sum_biUnion_le_sum_sum _ _ (fun n => by positivity) _
    _ ≤ oddSieveTotal X :=
        Finset.sum_le_sum fun d _ => sum_inv_primeFactors_eq_le X d.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- `(log X)/2 − 1/2 ≤ oddSieveTotal X`. -/
theorem half_log_sub_half_le_oddSieveTotal (X : ℕ) :
    Real.log X / 2 - 1 / 2 ≤ oddSieveTotal X :=
  le_trans (half_log_sub_half_le_sum_inv_odd X) (sum_inv_odd_le_oddSieveTotal X)

/-! ## Removing the coprimality condition -/

/-- The weight of the odd squarefree `d ≤ X` divisible by a fixed prime `p` is at most
`1/(p − 1)` of the total weight: `d ↦ d/p` is injective and divides the weight by `p − 1`. -/
theorem sum_sieveWeight_dvd_le {X p : ℕ} (hp : p.Prime) :
    ∑ d ∈ (oddSquarefreeUpTo X).filter (fun d => p ∣ d), sieveWeight d
      ≤ 1 / ((p : ℝ) - 1) * oddSieveTotal X := by
  classical
  set S := (oddSquarefreeUpTo X).filter (fun d => p ∣ d) with hSdef
  have hp1 : 1 < p := hp.one_lt
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hweight_p : sieveWeight p = 1 / ((p : ℝ) - 1) := by
    simp [sieveWeight, hp.primeFactors]
  have hstruct : ∀ d ∈ S, sieveWeight d = 1 / ((p : ℝ) - 1) * sieveWeight (d / p) ∧
      d / p ∈ oddSquarefreeUpTo X := by
    intro d hd
    obtain ⟨hdmem, hpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨⟨⟨hd1, hdX⟩, hdsf⟩, hdodd⟩ := mem_oddSquarefreeUpTo.mp hdmem
    obtain ⟨e, rfl⟩ := hpd
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at hd1
    have hcop : Nat.Coprime p e := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      rintro ⟨f, rfl⟩
      exact hp.not_isUnit (hdsf p ⟨f, by ring⟩)
    have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
    have hesf : Squarefree e := hdsf.squarefree_of_dvd ⟨p, by ring⟩
    have heodd : ¬ 2 ∣ e := fun h2 => hdodd (dvd_trans h2 ⟨p, by ring⟩)
    have hele : e ≤ p * e := Nat.le_mul_of_pos_left e hp.pos
    refine ⟨?_, ?_⟩
    · rw [hdiv, sieveWeight_mul hp.ne_zero he0 hcop, hweight_p]
    · rw [hdiv]
      exact mem_oddSquarefreeUpTo.2 ⟨⟨⟨by omega, le_trans hele hdX⟩, hesf⟩, heodd⟩
  have hinj : ∀ d₁ ∈ S, ∀ d₂ ∈ S, d₁ / p = d₂ / p → d₁ = d₂ := by
    intro d₁ h₁ d₂ h₂ h
    obtain ⟨-, hp₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨-, hp₂⟩ := Finset.mem_filter.mp h₂
    rw [← Nat.div_mul_cancel hp₁, ← Nat.div_mul_cancel hp₂, h]
  calc ∑ d ∈ S, sieveWeight d
      = ∑ d ∈ S, 1 / ((p : ℝ) - 1) * sieveWeight (d / p) :=
        Finset.sum_congr rfl fun d hd => (hstruct d hd).1
    _ = 1 / ((p : ℝ) - 1) * ∑ e ∈ S.image (fun d => d / p), sieveWeight e := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ 1 / ((p : ℝ) - 1) * oddSieveTotal X := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => sieveWeight_nonneg e)
        intro e he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
        exact (hstruct d hd).2

/-- `∑_{3 ≤ p ≤ X prime} 1/(p − 1)² ≤ 7/16`: the numbers `p − 1` are distinct even numbers. -/
theorem sum_inv_sq_odd_primes_le (X : ℕ) :
    ∑ p ∈ (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2), 1 / ((p : ℝ) - 1) ^ 2 ≤ 7 / 16 := by
  classical
  set S := (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2) with hSdef
  have hthree : ∀ p ∈ S, 3 ≤ p ∧ p % 2 = 1 ∧ p ≤ X := by
    intro p hp
    obtain ⟨hpI, hpp, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpX⟩ := Finset.mem_Icc.mp hpI
    have hodd : p % 2 = 1 := by
      rcases Nat.even_or_odd p with he | ho
      · exact absurd ((Nat.Prime.even_iff hpp).mp he) hp2
      · exact Nat.odd_iff.mp ho
    have hp2le := hpp.two_le
    exact ⟨by omega, hodd, hpX⟩
  have hcast : ∀ p ∈ S, 1 / ((p : ℝ) - 1) ^ 2 = 1 / 4 * (1 / ((((p - 1) / 2 : ℕ)) : ℝ) ^ 2) := by
    intro p hp
    obtain ⟨h3, hodd, -⟩ := hthree p hp
    have hnat : 2 * ((p - 1) / 2 : ℕ) = p - 1 := by omega
    have hR : 2 * ((((p - 1) / 2 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
      have h := congrArg (fun t : ℕ => (t : ℝ)) hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at h
      linarith
    have hjpos : (0 : ℝ) < ((((p - 1) / 2 : ℕ)) : ℝ) := by
      have : 1 ≤ ((p - 1) / 2 : ℕ) := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    rw [← hR]
    field_simp
    ring
  have hinj : ∀ p₁ ∈ S, ∀ p₂ ∈ S, (p₁ - 1) / 2 = (p₂ - 1) / 2 → p₁ = p₂ := by
    intro p₁ h₁ p₂ h₂ h
    obtain ⟨h3₁, hodd₁, -⟩ := hthree p₁ h₁
    obtain ⟨h3₂, hodd₂, -⟩ := hthree p₂ h₂
    omega
  have hsub : S.image (fun p => (p - 1) / 2) ⊆ Icc 1 X := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨h3, hodd, hpX⟩ := hthree p hp
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  calc ∑ p ∈ S, 1 / ((p : ℝ) - 1) ^ 2
      = ∑ p ∈ S, 1 / 4 * (1 / ((((p - 1) / 2 : ℕ)) : ℝ) ^ 2) := Finset.sum_congr rfl hcast
    _ = 1 / 4 * ∑ j ∈ S.image (fun p => (p - 1) / 2), 1 / ((j : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ 1 / 4 * ∑ j ∈ Icc 1 X, 1 / ((j : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ 1 / 4 * (7 / 4) := by
        refine mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_one_le X) (by norm_num)
    _ = 7 / 16 := by norm_num

/-- The pairs of odd squarefree numbers up to `X`. -/
def oddPairs (X : ℕ) : Finset (ℕ × ℕ) := oddSquarefreeUpTo X ×ˢ oddSquarefreeUpTo X

/-- The coprime pairs of odd squarefree numbers up to `X`. -/
def coprimeOddPairs (X : ℕ) : Finset (ℕ × ℕ) :=
  (oddPairs X).filter (fun ab => Nat.Coprime ab.1 ab.2)

/-- Subadditivity of a sum of nonnegative terms over a `Finset.biUnion`, for an arbitrary index
type and an arbitrary type of elements. -/
theorem sum_biUnion_le_sum_sum' {ι α : Type*} [DecidableEq α] (T : ι → Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (s : Finset ι) :
    ∑ a ∈ s.biUnion T, f a ≤ ∑ i ∈ s, ∑ a ∈ T i, f a := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi IH
  rw [Finset.biUnion_insert, Finset.sum_insert hi]
  have hui := Finset.sum_union_inter (s₁ := T i) (s₂ := s.biUnion T) (f := f)
  have hnn : 0 ≤ ∑ a ∈ T i ∩ s.biUnion T, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

/-- The total weight of the pairs of odd squarefree numbers up to `X` is `oddSieveTotal X` squared.
-/
theorem sum_oddPairs_eq (X : ℕ) :
    ∑ ab ∈ oddPairs X, sieveWeight ab.1 * sieveWeight ab.2 = oddSieveTotal X ^ 2 := by
  rw [oddPairs, Finset.sum_product, sq, oddSieveTotal, Finset.sum_mul_sum]

/-- The pairs with a common prime factor carry at most `7/16` of the total weight. -/
theorem sum_noncoprime_pairs_le (X : ℕ) :
    ∑ ab ∈ (oddPairs X).filter (fun ab => ¬ Nat.Coprime ab.1 ab.2),
        sieveWeight ab.1 * sieveWeight ab.2
      ≤ 7 / 16 * oddSieveTotal X ^ 2 := by
  classical
  set P := (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2) with hP
  set T : ℕ → Finset (ℕ × ℕ) :=
    fun p => (oddSquarefreeUpTo X).filter (fun d => p ∣ d) ×ˢ
      (oddSquarefreeUpTo X).filter (fun d => p ∣ d) with hT
  have hsub : (oddPairs X).filter (fun ab => ¬ Nat.Coprime ab.1 ab.2) ⊆ P.biUnion T := by
    intro ab hab
    obtain ⟨habP, hncop⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp habP
    obtain ⟨⟨⟨ha1, haX⟩, -⟩, haodd⟩ := mem_oddSquarefreeUpTo.mp ha
    obtain ⟨⟨⟨hb1, hbX⟩, -⟩, hbodd⟩ := mem_oddSquarefreeUpTo.mp hb
    have hg1 : Nat.gcd ab.1 ab.2 ≠ 1 := hncop
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
    have hpa : p ∣ ab.1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpb : p ∣ ab.2 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hple : p ≤ ab.1 := Nat.le_of_dvd (by omega) hpa
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact haodd hpa
    refine Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hp.one_lt.le, by omega⟩,
      hp, hp2⟩, ?_⟩
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨ha, hpa⟩, Finset.mem_filter.2 ⟨hb, hpb⟩⟩
  have hfiber : ∀ p ∈ P, ∑ ab ∈ T p, sieveWeight ab.1 * sieveWeight ab.2
      ≤ 1 / ((p : ℝ) - 1) ^ 2 * oddSieveTotal X ^ 2 := by
    intro p hpP
    obtain ⟨-, hp, hp2⟩ := Finset.mem_filter.mp hpP
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hsq : ∑ ab ∈ T p, sieveWeight ab.1 * sieveWeight ab.2
        = (∑ d ∈ (oddSquarefreeUpTo X).filter (fun d => p ∣ d), sieveWeight d) ^ 2 := by
      simp only [hT]
      rw [Finset.sum_product, sq, Finset.sum_mul_sum]
    rw [hsq]
    have hle := sum_sieveWeight_dvd_le (X := X) hp
    have hnn : 0 ≤ ∑ d ∈ (oddSquarefreeUpTo X).filter (fun d => p ∣ d), sieveWeight d :=
      Finset.sum_nonneg fun d _ => sieveWeight_nonneg d
    have hrhs : 0 ≤ 1 / ((p : ℝ) - 1) * oddSieveTotal X :=
      mul_nonneg (by positivity) (oddSieveTotal_nonneg X)
    calc (∑ d ∈ (oddSquarefreeUpTo X).filter (fun d => p ∣ d), sieveWeight d) ^ 2
        ≤ (1 / ((p : ℝ) - 1) * oddSieveTotal X) ^ 2 := by nlinarith
      _ = 1 / ((p : ℝ) - 1) ^ 2 * oddSieveTotal X ^ 2 := by
          rw [mul_pow, div_pow, one_pow]
  calc ∑ ab ∈ (oddPairs X).filter (fun ab => ¬ Nat.Coprime ab.1 ab.2),
        sieveWeight ab.1 * sieveWeight ab.2
      ≤ ∑ ab ∈ P.biUnion T, sieveWeight ab.1 * sieveWeight ab.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ab _ _ => mul_nonneg (sieveWeight_nonneg _) (sieveWeight_nonneg _))
    _ ≤ ∑ p ∈ P, ∑ ab ∈ T p, sieveWeight ab.1 * sieveWeight ab.2 :=
        sum_biUnion_le_sum_sum' T _
          (fun ab => mul_nonneg (sieveWeight_nonneg _) (sieveWeight_nonneg _)) P
    _ ≤ ∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2 * oddSieveTotal X ^ 2 := Finset.sum_le_sum hfiber
    _ = (∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2) * oddSieveTotal X ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ 7 / 16 * oddSieveTotal X ^ 2 := by
        refine mul_le_mul_of_nonneg_right (sum_inv_sq_odd_primes_le X) (by positivity)

/-- Hence the coprime pairs carry at least `9/16` of it. -/
theorem nine_sixteenths_le_sum_coprime_pairs (X : ℕ) :
    9 / 16 * oddSieveTotal X ^ 2
      ≤ ∑ ab ∈ coprimeOddPairs X, sieveWeight ab.1 * sieveWeight ab.2 := by
  classical
  have hsplit : ∑ ab ∈ coprimeOddPairs X, sieveWeight ab.1 * sieveWeight ab.2
      + ∑ ab ∈ (oddPairs X).filter (fun ab => ¬ Nat.Coprime ab.1 ab.2),
          sieveWeight ab.1 * sieveWeight ab.2
      = oddSieveTotal X ^ 2 := by
    rw [coprimeOddPairs, ← sum_oddPairs_eq X]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have := sum_noncoprime_pairs_le X
  linarith

/-! ## The coprime pairs are dominated by the twin sifting sum -/

/-- The twin-prime weight of a prime is positive. -/
theorem twinWeight_pos {p : ℕ} (hp : p.Prime) : 0 < twinWeight p := by
  have := hp.two_le
  rcases eq_or_ne p 2 with rfl | h
  · simp [twinWeight]
  · have h3 : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h' | h'
      · omega
      · exact h'
    simp only [twinWeight, if_neg h]
    omega

/-- The twin-prime weight of a prime `p` is at most `p`. -/
theorem twinWeight_le {p : ℕ} (hp : p.Prime) : twinWeight p ≤ p := by
  have := hp.two_le
  rcases eq_or_ne p 2 with rfl | h
  · simp [twinWeight]
  · simp only [twinWeight, if_neg h]
    omega

/-- Every factor of the twin sifting sum is nonnegative. -/
theorem twinFactor_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ ((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ) := by
  have h1 : (twinWeight p : ℝ) ≤ (p : ℝ) := by exact_mod_cast twinWeight_le hp
  have h2 : (0 : ℝ) < (twinWeight p : ℝ) := by exact_mod_cast twinWeight_pos hp
  exact div_nonneg (by linarith) h2.le

/-- For an odd prime `p`, the twin factor is `2/(p − 2)`, which dominates `2/(p − 1)`. -/
theorem two_div_sub_one_le_twinFactor {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (1 / ((p : ℝ) - 1)) ≤ ((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ) := by
  have h2 := hp.two_le
  have h3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h' | h'
    · omega
    · exact h'
  have hw : twinWeight p = p - 2 := by simp [twinWeight, hp2]
  have hwR : ((twinWeight p : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [hw]
    have : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
      ring
    exact this
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  rw [hwR]
  have hnum : (p : ℝ) - ((p : ℝ) - 2) = 2 := by ring
  rw [hnum]
  have hle : 1 / ((p : ℝ) - 1) ≤ 1 / ((p : ℝ) - 2) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hrw : 2 / ((p : ℝ) - 2) = 2 * (1 / ((p : ℝ) - 2)) := by ring
  rw [hrw]
  linarith

/-- For a squarefree `q`, the pairs `(a, b)` with `a b = q` are at most `2^{ω(q)}` in number, and
each contributes `∏_{p ∣ q} 1/(p − 1)`; since `2^{ω(q)} ∏_{p ∣ q} 1/(p − 1) = ∏_{p ∣ q} 2/(p − 1)`
is at most the twin factor `∏_{p ∣ q} 2/(p − 2)` for odd `q`, the coprime pairs of odd squarefree
numbers up to `X` are dominated by the twin sifting sum at `Q ≥ X²`. -/
theorem sum_coprime_pairs_le_twinSiftSum {X Q : ℕ} (hXQ : X * X ≤ Q) :
    ∑ ab ∈ coprimeOddPairs X, sieveWeight ab.1 * sieveWeight ab.2 ≤ twinSiftSum Q := by
  classical
  have hmem : ∀ ab ∈ coprimeOddPairs X,
      (((1 ≤ ab.1 ∧ ab.1 ≤ X) ∧ Squarefree ab.1) ∧ ¬ 2 ∣ ab.1) ∧
      (((1 ≤ ab.2 ∧ ab.2 ≤ X) ∧ Squarefree ab.2) ∧ ¬ 2 ∣ ab.2) ∧ Nat.Coprime ab.1 ab.2 := by
    intro ab hab
    obtain ⟨habP, hcop⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp habP
    exact ⟨mem_oddSquarefreeUpTo.mp ha, mem_oddSquarefreeUpTo.mp hb, hcop⟩
  have hmaps : ∀ ab ∈ coprimeOddPairs X, ab.1 * ab.2 ∈ squarefreeUpTo Q := by
    intro ab hab
    obtain ⟨⟨⟨⟨ha1, haX⟩, hasf⟩, -⟩, ⟨⟨⟨hb1, hbX⟩, hbsf⟩, -⟩, hcop⟩ := hmem ab hab
    refine mem_squarefreeUpTo.2 ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩,
      (Nat.squarefree_mul hcop).2 ⟨hasf, hbsf⟩⟩
    exact le_trans (Nat.mul_le_mul haX hbX) hXQ
  unfold twinSiftSum
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨⟨hq1, hqQ⟩, hqsf⟩ := mem_squarefreeUpTo.mp hq
  have hprodnn : 0 ≤ ∏ p ∈ q.primeFactors, (((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ)) :=
    Finset.prod_nonneg fun p hp => twinFactor_nonneg (Nat.prime_of_mem_primeFactors hp)
  by_cases hqeven : 2 ∣ q
  · have hempty : (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro ab hab hprod
      obtain ⟨⟨-, haodd⟩, ⟨-, hbodd⟩, -⟩ := hmem ab hab
      have hdvd : (2 : ℕ) ∣ ab.1 * ab.2 := by rw [hprod]; exact hqeven
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
      · exact haodd h
      · exact hbodd h
    rw [hempty, Finset.sum_empty]
    exact hprodnn
  · have hconst : ∀ ab ∈ (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q),
        sieveWeight ab.1 * sieveWeight ab.2 = sieveWeight q := by
      intro ab hab
      obtain ⟨habm, hprod⟩ := Finset.mem_filter.mp hab
      obtain ⟨⟨⟨⟨ha1, -⟩, -⟩, -⟩, ⟨⟨⟨hb1, -⟩, -⟩, -⟩, hcop⟩ := hmem ab habm
      rw [← hprod, sieveWeight_mul (by omega) (by omega) hcop]
    have hcard : ((coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q)).card
        ≤ 2 ^ q.primeFactors.card := by
      have hmapsto : ∀ ab ∈ (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q),
          ab.1.primeFactors ∈ q.primeFactors.powerset := by
        intro ab hab
        obtain ⟨habm, hprod⟩ := Finset.mem_filter.mp hab
        obtain ⟨⟨⟨⟨ha1, -⟩, -⟩, -⟩, ⟨⟨⟨hb1, -⟩, -⟩, -⟩, -⟩ := hmem ab habm
        refine Finset.mem_powerset.2 ?_
        refine Nat.primeFactors_mono ⟨ab.2, hprod.symm⟩ (by omega)
      have hinj : ∀ ab₁ ∈ (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q),
          ∀ ab₂ ∈ (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q),
          ab₁.1.primeFactors = ab₂.1.primeFactors → ab₁ = ab₂ := by
        intro ab₁ h₁ ab₂ h₂ h
        obtain ⟨habm₁, hprod₁⟩ := Finset.mem_filter.mp h₁
        obtain ⟨habm₂, hprod₂⟩ := Finset.mem_filter.mp h₂
        obtain ⟨⟨⟨⟨ha1₁, -⟩, hasf₁⟩, -⟩, -⟩ := hmem ab₁ habm₁
        obtain ⟨⟨⟨⟨ha1₂, -⟩, hasf₂⟩, -⟩, -⟩ := hmem ab₂ habm₂
        have hfst : ab₁.1 = ab₂.1 := by
          rw [← Nat.prod_primeFactors_of_squarefree hasf₁,
            ← Nat.prod_primeFactors_of_squarefree hasf₂, h]
        have hsnd : ab₁.2 = ab₂.2 := by
          have hq' : ab₁.1 * ab₁.2 = ab₁.1 * ab₂.2 := by rw [hprod₁, hfst, hprod₂]
          exact Nat.eq_of_mul_eq_mul_left (by omega) hq'
        exact Prod.ext hfst hsnd
      calc ((coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q)).card
          ≤ q.primeFactors.powerset.card := Finset.card_le_card_of_injOn _ hmapsto
            (fun a ha b hb h => hinj a ha b hb h)
        _ = 2 ^ q.primeFactors.card := Finset.card_powerset _
    have hcardR : (((coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q)).card : ℝ)
        ≤ 2 ^ q.primeFactors.card := by exact_mod_cast hcard
    have hpow : (2 : ℝ) ^ q.primeFactors.card * sieveWeight q
        ≤ ∏ p ∈ q.primeFactors, (((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ)) := by
      rw [sieveWeight, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
          refine div_nonneg zero_le_one (by linarith)
        linarith
      · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
        have hp2 : p ≠ 2 := by
          rintro rfl
          exact hqeven hpq
        exact two_div_sub_one_le_twinFactor hpp hp2
    calc ∑ ab ∈ (coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q),
          sieveWeight ab.1 * sieveWeight ab.2
        = (((coprimeOddPairs X).filter (fun ab => ab.1 * ab.2 = q)).card : ℝ) * sieveWeight q := by
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ q.primeFactors.card * sieveWeight q :=
          mul_le_mul_of_nonneg_right hcardR (sieveWeight_nonneg q)
      _ ≤ ∏ p ∈ q.primeFactors, (((p : ℝ) - (twinWeight p : ℝ)) / (twinWeight p : ℝ)) := hpow

/-- **The lower bound for the twin sifting sum**: `twinSiftSum Q ≥ (9/16) T²` with
`T = (log √Q)/2 − 1/2`, as soon as `T ≥ 0`. -/
theorem twinSiftSum_ge {Q : ℕ} (hQ : 1 ≤ Real.log (Nat.sqrt Q)) :
    9 / 16 * (Real.log (Nat.sqrt Q) / 2 - 1 / 2) ^ 2 ≤ twinSiftSum Q := by
  set X := Nat.sqrt Q with hX
  have hXQ : X * X ≤ Q := by
    have h := Nat.sqrt_le' Q
    rw [pow_two] at h
    exact h
  have hT := half_log_sub_half_le_oddSieveTotal X
  have hL : 0 ≤ Real.log X / 2 - 1 / 2 := by linarith
  have hsq : (Real.log X / 2 - 1 / 2) ^ 2 ≤ oddSieveTotal X ^ 2 := by
    nlinarith [oddSieveTotal_nonneg X]
  calc 9 / 16 * (Real.log X / 2 - 1 / 2) ^ 2 ≤ 9 / 16 * oddSieveTotal X ^ 2 := by linarith
    _ ≤ ∑ ab ∈ coprimeOddPairs X, sieveWeight ab.1 * sieveWeight ab.2 :=
        nine_sixteenths_le_sum_coprime_pairs X
    _ ≤ twinSiftSum Q := sum_coprime_pairs_le_twinSiftSum hXQ

/-! ## The sieve at the twin-prime weights -/

/-- **The large sieve for a set missing two residue classes modulo every odd prime `p ≤ Q` and one
class modulo `2`.** -/
theorem card_mul_twinSiftSum_le {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ twinWeight p) :
    (A.card : ℝ) * twinSiftSum Q ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  card_le_sifted_squarefree hQ hA twinWeight (fun _ hp _ => twinWeight_pos hp)
    (fun _ hp _ => twinWeight_le hp) havoid

/-- The twin primes below `N`. -/
def twinPrimes (N : ℕ) : Finset ℕ := (range N).filter (fun n => n.Prime ∧ (n + 2).Prime)

/-- A twin prime `n > Q` misses the residue classes `0` and `p − 2` modulo every odd prime
`p ≤ Q`, and the class `0` modulo `2`. -/
theorem twinPrimes_image_card_le {N Q : ℕ} {p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) :
    (((twinPrimes N).filter (fun n => Q < n)).image (fun n => n % p)).card ≤ twinWeight p := by
  classical
  have hfacts : ∀ n ∈ (twinPrimes N).filter (fun n => Q < n),
      n.Prime ∧ (n + 2).Prime ∧ Q < n := by
    intro n hn
    obtain ⟨hnT, hnQ⟩ := Finset.mem_filter.mp hn
    obtain ⟨-, hnp, hnp2⟩ := Finset.mem_filter.mp hnT
    exact ⟨hnp, hnp2, hnQ⟩
  have hnot0 : ∀ n ∈ (twinPrimes N).filter (fun n => Q < n), n % p ≠ 0 := by
    intro n hn h0
    obtain ⟨hnp, -, hnQ⟩ := hfacts n hn
    have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.Prime.eq_one_or_self_of_dvd hnp p hdvd)
    have hp1 := hp.one_lt
    omega
  rcases eq_or_ne p 2 with rfl | hp2
  · have hsub : ((twinPrimes N).filter (fun n => Q < n)).image (fun n => n % 2) ⊆ {1} := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have h0 := hnot0 n hn
      have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
      simp only [Finset.mem_singleton]
      omega
    calc (((twinPrimes N).filter (fun n => Q < n)).image (fun n => n % 2)).card
        ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton 1
      _ = twinWeight 2 := by simp [twinWeight]
  · have h3 : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · omega
      · exact h'
    have hnot2 : ∀ n ∈ (twinPrimes N).filter (fun n => Q < n), n % p ≠ p - 2 := by
      intro n hn h2
      obtain ⟨-, hnp2, hnQ⟩ := hfacts n hn
      have hmod : (n + 2) % p = 0 := by
        have h := Nat.add_mod n 2 p
        rw [h2] at h
        have h2p : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
        rw [h2p] at h
        have hpp : p - 2 + 2 = p := by omega
        rw [hpp, Nat.mod_self] at h
        exact h
      have hdvd : p ∣ n + 2 := Nat.dvd_of_mod_eq_zero hmod
      have := Nat.Prime.eq_one_or_self_of_dvd hnp2 p hdvd
      have hp1 := hp.one_lt
      omega
    have hsub : ((twinPrimes N).filter (fun n => Q < n)).image (fun n => n % p)
        ⊆ ((range p).erase 0).erase (p - 2) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      refine Finset.mem_erase.2 ⟨hnot2 n hn, Finset.mem_erase.2 ⟨hnot0 n hn, ?_⟩⟩
      exact Finset.mem_range.2 (Nat.mod_lt _ hp.pos)
    have hcard : (((range p).erase 0).erase (p - 2)).card = p - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩),
        Finset.card_erase_of_mem (Finset.mem_range.2 hp.pos), Finset.card_range]
      omega
    calc (((twinPrimes N).filter (fun n => Q < n)).image (fun n => n % p)).card
        ≤ (((range p).erase 0).erase (p - 2)).card := Finset.card_le_card hsub
      _ = p - 2 := hcard
      _ = twinWeight p := by simp [twinWeight, hp2]

/-- **Brun's twin-prime bound.**  The number of `n < N` with `n` and `n + 2` both prime is at most
`900 N/(log N)² + √N + 1`, once `log N ≥ 32`. -/
theorem card_twinPrimes_le {N : ℕ} (hN : 32 ≤ Real.log N) :
    ((twinPrimes N).card : ℝ) ≤ 900 * N / Real.log N ^ 2 + Real.sqrt N + 1 := by
  classical
  have hN16 : 16 ≤ N := by
    by_contra hcon
    push Not at hcon
    have hle : (N : ℝ) ≤ 15 := by exact_mod_cast (by omega : N ≤ 15)
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · norm_num at hN
    · have h1 : Real.log N ≤ Real.log 15 := Real.log_le_log (by exact_mod_cast hpos) hle
      have h2 : Real.log 15 ≤ 14 := by
        have := Real.log_le_sub_one_of_pos (x := (15 : ℝ)) (by norm_num)
        linarith
      linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log N with hL
  set Q := Nat.sqrt N with hQdef
  have hQ4 : 4 ≤ Q := by
    have h : Nat.sqrt 16 ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN16
    have h16 : Nat.sqrt 16 = 4 := by norm_num
    omega
  set X := Nat.sqrt Q with hXdef
  have hlog2 : Real.log 2 ≤ 0.6932 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hlogQ : L / 2 - Real.log 2 ≤ Real.log Q :=
    half_log_sub_log_two_le_log_sqrt (by omega : 4 ≤ N)
  have hlogX : Real.log Q / 2 - Real.log 2 ≤ Real.log X :=
    half_log_sub_log_two_le_log_sqrt hQ4
  have hXlow : L / 4 - 3 / 2 * Real.log 2 ≤ Real.log X := by linarith
  have hX1 : 1 ≤ Real.log X := by linarith
  have hT : 93 / 1000 * L ≤ Real.log X / 2 - 1 / 2 := by linarith
  have hTnn : (0 : ℝ) ≤ 93 / 1000 * L := by linarith
  have hS : 9 / 16 * (Real.log X / 2 - 1 / 2) ^ 2 ≤ twinSiftSum Q := twinSiftSum_ge hX1
  have hSlow : 486 / 100000 * L ^ 2 ≤ twinSiftSum Q := by nlinarith
  -- the sieve, applied to the twin primes above `Q`
  set A := (twinPrimes N).filter (fun n => Q < n) with hAdef
  set B := (twinPrimes N).filter (fun n => ¬ Q < n) with hBdef
  have hAB : A.card + B.card = (twinPrimes N).card :=
    Finset.card_filter_add_card_filter_not _
  have hAsub : A ⊆ range N := by
    refine (Finset.filter_subset _ _).trans ?_
    exact Finset.filter_subset _ _
  have hmain := card_mul_twinSiftSum_le (N := N) (Q := Q) (by omega) hAsub
    (fun p hp hpQ => twinPrimes_image_card_le hp hpQ)
  have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hLpos : (0 : ℝ) < L := by linarith
  have hstep : (A.card : ℝ) * (486 / 100000 * L ^ 2) ≤ 4.15 * (N : ℝ) := by
    have h1 : (A.card : ℝ) * (486 / 100000 * L ^ 2) ≤ (A.card : ℝ) * twinSiftSum Q :=
      mul_le_mul_of_nonneg_left hSlow hAcard0
    nlinarith
  have hAbound : (A.card : ℝ) ≤ 900 * (N : ℝ) / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- the twin primes below `Q`
  have hBcard : B.card ≤ Q + 1 := by
    have hsub : B ⊆ range (Q + 1) := by
      intro n hn
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_range.2 (by omega)
    simpa using Finset.card_le_card hsub
  have hQle : (Q : ℝ) ≤ Real.sqrt N := by
    have h : (Q : ℝ) ^ 2 ≤ (N : ℝ) := hQsq
    nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) Q]
  have hBbound : (B.card : ℝ) ≤ Real.sqrt N + 1 := by
    have h : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
    linarith
  have hsum : ((twinPrimes N).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
    rw [← hAB]
    push_cast
    ring
  rw [hsum]
  linarith

end BrunTwinPrimes

end RiemannHypothesis
