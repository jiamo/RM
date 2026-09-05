/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieveSquarefree

/-!
# A Brun–Titchmarsh inequality from the large sieve

`RiemannHypothesis.LargeSieveSquarefree` proves Montgomery's sieve: a set `A ⊆ [0, N)` that meets
at most `w p` residue classes modulo every prime `p ≤ Q` satisfies

`|A| ∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/(w p) ≤ Q² + π N`.

Here that inequality is applied to the primes in an interval, with the weights `w p = p − 1`: a
prime larger than `Q` avoids the class `0` modulo every prime `p ≤ Q`, so the sifting density is
`∏_{p ∣ q} 1/(p − 1)`, and the sifting sum is at least `∑_{q ≤ Q squarefree} 1/q`, which is
`≫ log Q`. The result is a Brun–Titchmarsh inequality: uniformly in the starting point `x`,

`π(x + y) − π(x) ≪ y / log y`.

## Main results

* `siftSum` — the sifting sum `∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p − 1)`;
* `sum_inv_squarefree_le_siftSum` — `∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`;
* `sum_inv_not_squarefree_le` — the reciprocals of the non-squarefree `n ≤ Q` sum to at most
  `(3/4)(log Q + 1)`;
* `quarter_log_le_siftSum` — `(1/4) log Q − 3/4 ≤ siftSum Q`;
* `sum_inv_le_sum_inv_sq_mul_sum_inv_squarefree` — the factorization `n = d² q` with `q`
  squarefree gives `∑_{n ≤ Q} 1/n ≤ (∑_{d ≤ Q} 1/d²)(∑_{q ≤ Q squarefree} 1/q)`;
* `four_sevenths_log_le_siftSum` — the sharper lower bound `(4/7) log Q ≤ siftSum Q`, with no
  additive loss;
* `sum_inv_primeFactors_eq_le` — the reciprocals of the `m ≤ Q` with a prescribed set `P` of prime
  factors sum to at most `∏_{p ∈ P} 1/(p − 1)`;
* `log_le_siftSum` — the classical lower bound `log Q ≤ siftSum Q`, with the constant `1`;
* `card_mul_siftSum_le` — the sieve for a set avoiding one residue class modulo every prime
  `p ≤ Q`: `|A| · siftSum Q ≤ Q² + π N`;
* `card_primes_Ico_le` — **Brun–Titchmarsh (with a non-optimal constant)**: for `log y ≥ 4` and
  every `x`, the number of primes in `[x, x + y)` is at most `13 y / log y + √y + 1`;
* `card_primes_Ico_le_of_log_ge_24` — the same with the constant `9`, for `log y ≥ 24`.

## Scope

The constant `13` is still above the sharp `2` of Montgomery–Vaughan: what remains is the factor
`π` of the repository's large sieve, in place of the sharp `1`, and the rigid choice `Q = ⌊√y⌋`,
which loses an additive `log 2`. With the sharp large sieve and `Q = √y / log y` the same route
gives `2 + o(1)`; with the factor `π` kept and `Q` optimized it would give `2π + o(1)`.
The threshold `log y ≥ 4`, that is `y ≥ 55`, is an artefact of that additive loss, and so is the
improvement to `9` above `log y ≥ 24`. Only the interval form is proved: no arithmetic-progression
form, and no Bombieri–Vinogradov consequence. No consequence for `ζ` is drawn: no zero-free
region, no zero-density estimate and no mean value theorem follows from this row.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace BrunTitchmarsh

open LargeSieveSquarefree

/-- The sifting sum of the large sieve with the weights `w p = p − 1`, that is
`∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p − 1)`. -/
def siftSum (Q : ℕ) : ℝ :=
  ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)

/-! ## The sifting sum is at least the squarefree harmonic sum -/

/-- For squarefree `q`, `∏_{p ∣ q} 1/(p − 1) ≥ 1/q`. -/
theorem inv_le_prod_inv_sub_one {q : ℕ} (hq : Squarefree q) :
    (1 : ℝ) / q ≤ ∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
  have hqe : ∏ p ∈ q.primeFactors, p = q := Nat.prod_primeFactors_of_squarefree hq
  have hcast : ((q : ℕ) : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) hqe
    push_cast at h
    exact h.symm
  rw [hcast, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    positivity
  · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- `∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`. -/
theorem sum_inv_squarefree_le_siftSum (Q : ℕ) :
    ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q ≤ siftSum Q :=
  Finset.sum_le_sum fun _ hq => inv_le_prod_inv_sub_one (mem_squarefreeUpTo.mp hq).2

/-! ## The squarefree harmonic sum is at least `(log Q)/4 − 3/4` -/

/-- The harmonic sum as a sum of reciprocals. -/
theorem harmonic_cast (Q : ℕ) : ((harmonic Q : ℚ) : ℝ) = ∑ n ∈ Icc 1 Q, (1 : ℝ) / n := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

/-- The harmonic sum `∑_{n ≤ Q} 1/n` is at least `log Q`. -/
theorem log_le_sum_inv (Q : ℕ) : Real.log Q ≤ ∑ n ∈ Icc 1 Q, (1 : ℝ) / n := by
  have h := log_add_one_le_harmonic Q
  have hmono : Real.log Q ≤ Real.log (Q + 1) := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    · exact Real.log_le_log (by exact_mod_cast hQ) (by linarith)
  rw [← harmonic_cast Q]
  push_cast at h
  linarith

/-- The harmonic sum `∑_{n ≤ Q} 1/n` is at most `log Q + 1`. -/
theorem sum_inv_le_log_add_one (Q : ℕ) : ∑ n ∈ Icc 1 Q, (1 : ℝ) / n ≤ Real.log Q + 1 := by
  have h := harmonic_le_one_add_log Q
  rw [← harmonic_cast Q]
  linarith

/-- The reciprocals of the multiples of `d²` in `[1, Q]` sum to at most `(log Q + 1)/d²`. -/
theorem sum_inv_multiples_le (Q : ℕ) {d : ℕ} (hd : 2 ≤ d) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => d ^ 2 ∣ n), (1 : ℝ) / n
      ≤ (Real.log Q + 1) / (d : ℝ) ^ 2 := by
  classical
  have hd0 : 0 < d ^ 2 := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    positivity
  have hset : (Icc 1 Q).filter (fun n => d ^ 2 ∣ n)
      = (Icc 1 (Q / d ^ 2)).image (fun m => d ^ 2 * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, m, rfl⟩
      refine ⟨m, ⟨?_, (Nat.le_div_iff_mul_le hd0).2 (by rw [Nat.mul_comm]; exact h2)⟩, rfl⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · omega
      · omega
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.2 (by positivity)
      · rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd0).1 hm2
  rw [hset, Finset.sum_image (by
    intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hd0 h)]
  have hterm : ∀ m ∈ Icc 1 (Q / d ^ 2),
      (1 : ℝ) / ((d ^ 2 * m : ℕ) : ℝ) = (1 / (d : ℝ) ^ 2) * (1 / (m : ℝ)) := by
    intro m _
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hQ0 : 0 ≤ Real.log Q := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hQ)
  have hlog : Real.log ((Q / d ^ 2 : ℕ) : ℝ) ≤ Real.log Q := by
    rcases Nat.eq_zero_or_pos (Q / d ^ 2) with h | h
    · simp only [h, Nat.cast_zero, Real.log_zero]; exact hQ0
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.div_le_self Q (d ^ 2))
  have hsum := sum_inv_le_log_add_one (Q / d ^ 2)
  have hkey : ∑ n ∈ Icc 1 (Q / d ^ 2), (1 : ℝ) / n ≤ Real.log Q + 1 := by linarith
  have hnn : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 2 := by positivity
  exact (mul_le_mul_of_nonneg_left hkey hnn).trans_eq (by ring)

/-- Subadditivity of a sum of nonnegative terms over a `Finset.biUnion`. -/
theorem sum_biUnion_le_sum_sum {ι : Type*} (T : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (s : Finset ι) :
    ∑ n ∈ s.biUnion T, f n ≤ ∑ i ∈ s, ∑ n ∈ T i, f n := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi IH
  rw [Finset.biUnion_insert, Finset.sum_insert hi]
  have hui := Finset.sum_union_inter (s₁ := T i) (s₂ := s.biUnion T) (f := f)
  have hnn : 0 ≤ ∑ n ∈ T i ∩ s.biUnion T, f n := Finset.sum_nonneg fun n _ => hf n
  linarith

/-- The reciprocals of the non-squarefree `n ≤ Q` sum to at most `(3/4)(log Q + 1)`. -/
theorem sum_inv_not_squarefree_le (Q : ℕ) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => ¬ Squarefree n), (1 : ℝ) / n
      ≤ 3 / 4 * (Real.log Q + 1) := by
  classical
  have hlogQ : 0 ≤ Real.log Q := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hQ)
  rcases Nat.lt_or_ge Q 2 with hQ | hQ
  · have hempty : (Icc 1 Q).filter (fun n => ¬ Squarefree n) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn
      have h := Finset.mem_Icc.mp hn
      have hn1 : n = 1 := by omega
      subst hn1
      simp
    rw [hempty, Finset.sum_empty]
    linarith
  · have hsub : (Icc 1 Q).filter (fun n => ¬ Squarefree n)
        ⊆ (Icc 2 Q).biUnion (fun d => (Icc 1 Q).filter (fun n => d ^ 2 ∣ n)) := by
      intro q hq
      obtain ⟨hq1, hnsf⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hq1
      obtain ⟨p, hp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p * p ∣ q := by
        by_contra hcon
        push Not at hcon
        exact hnsf (Nat.squarefree_iff_prime_squarefree.2 fun p hp => hcon p hp)
      have hpq : p ≤ q := le_trans (Nat.le_mul_of_pos_left p hp.pos)
        (Nat.le_of_dvd (by omega) hpd)
      refine Finset.mem_biUnion.2 ⟨p, Finset.mem_Icc.2 ⟨hp.two_le, le_trans hpq h2⟩, ?_⟩
      exact Finset.mem_filter.2 ⟨hq1, by rwa [pow_two]⟩
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    have hsq := sum_inv_sq_le Q hQ
    have hsqle : ∑ d ∈ Icc 2 Q, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 := by
      have : (0 : ℝ) < 1 / (Q : ℝ) := by positivity
      linarith
    calc ∑ n ∈ (Icc 1 Q).filter (fun n => ¬ Squarefree n), (1 : ℝ) / n
        ≤ ∑ n ∈ (Icc 2 Q).biUnion (fun d => (Icc 1 Q).filter (fun n => d ^ 2 ∣ n)), (1 : ℝ) / n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ ≤ ∑ d ∈ Icc 2 Q, ∑ n ∈ (Icc 1 Q).filter (fun n => d ^ 2 ∣ n), (1 : ℝ) / n :=
          sum_biUnion_le_sum_sum _ _ (fun n => by positivity) _
      _ ≤ ∑ d ∈ Icc 2 Q, (Real.log Q + 1) / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum fun d hd => sum_inv_multiples_le Q (Finset.mem_Icc.mp hd).1
      _ = (Real.log Q + 1) * ∑ d ∈ Icc 2 Q, (1 : ℝ) / (d : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ ≤ (Real.log Q + 1) * (3 / 4) :=
          mul_le_mul_of_nonneg_left hsqle (by linarith)
      _ = 3 / 4 * (Real.log Q + 1) := by ring

/-- `∑_{q ≤ Q squarefree} 1/q ≥ (log Q)/4 − 3/4`. -/
theorem quarter_log_le_sum_inv_squarefree (Q : ℕ) :
    Real.log Q / 4 - 3 / 4 ≤ ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q := by
  classical
  have hsplit : ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q
      + ∑ n ∈ (Icc 1 Q).filter (fun n => ¬ Squarefree n), (1 : ℝ) / n
      = ∑ n ∈ Icc 1 Q, (1 : ℝ) / n :=
    Finset.sum_filter_add_sum_filter_not (Icc 1 Q) Squarefree _
  have h1 := log_le_sum_inv Q
  have h2 := sum_inv_not_squarefree_le Q
  linarith

/-- `siftSum Q ≥ (log Q)/4 − 3/4`. -/
theorem quarter_log_le_siftSum (Q : ℕ) : Real.log Q / 4 - 3 / 4 ≤ siftSum Q :=
  le_trans (quarter_log_le_sum_inv_squarefree Q) (sum_inv_squarefree_le_siftSum Q)

/-! ## The sharper lower bound `∑_{q ≤ Q squarefree} 1/q ≥ (4/7) log Q`

Every `n ≥ 1` factors as `d² q` with `q` squarefree, and the factorization is determined by `n`, so
the harmonic sum up to `Q` is at most `(∑_{d ≤ Q} 1/d²)(∑_{q ≤ Q squarefree} 1/q)`.  The first
factor is at most `7/4`, which turns the lower bound `log Q` for the harmonic sum into the lower
bound `(4/7) log Q` for the squarefree harmonic sum: better than the `(log Q)/4 − 3/4` above, and
with no additive loss.  The truth is `(6/π²) log Q + O(1)`, and `6/π² = 0.6079…` against
`4/7 = 0.5714…`. -/

/-- `∑_{d ≤ Q} 1/d² ≤ 7/4`. -/
theorem sum_inv_sq_Icc_one_le (Q : ℕ) : ∑ d ∈ Icc 1 Q, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 := by
  rcases Nat.lt_or_ge Q 2 with hQ | hQ
  · have hsub : Icc 1 Q ⊆ ({1} : Finset ℕ) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_singleton]
      omega
    calc ∑ d ∈ Icc 1 Q, (1 : ℝ) / (d : ℝ) ^ 2
        ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 7 / 4 := by norm_num
  · have hins : Icc 1 Q = insert 1 (Icc 2 Q) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (1 : ℕ) ∉ Icc 2 Q := by simp
    have h := sum_inv_sq_le Q hQ
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    have hinv : (0 : ℝ) < 1 / (Q : ℝ) := by positivity
    rw [hins, Finset.sum_insert hnot]
    have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [h1]
    linarith

/-- **The harmonic sum splits along `n = d² q`.**  Sending `n` to the pair `(d, q)` of a
factorization `n = d² q` with `q` squarefree is injective, so
`∑_{n ≤ Q} 1/n ≤ (∑_{d ≤ Q} 1/d²)(∑_{q ≤ Q squarefree} 1/q)`. -/
theorem sum_inv_le_sum_inv_sq_mul_sum_inv_squarefree (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, (1 : ℝ) / n
      ≤ (∑ d ∈ Icc 1 Q, (1 : ℝ) / (d : ℝ) ^ 2) * ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q := by
  classical
  choose a b hab using fun n : ℕ => Nat.sq_mul_squarefree n
  set F : ℕ → ℕ × ℕ := fun n => (b n, a n) with hF
  have hinj : ∀ m ∈ Icc 1 Q, ∀ n ∈ Icc 1 Q, F m = F n → m = n := by
    intro m _ n _ h
    have h1 : b m = b n := congrArg Prod.fst h
    have h2 : a m = a n := congrArg Prod.snd h
    have hm := (hab m).1
    rw [h1, h2, (hab n).1] at hm
    exact hm.symm
  have hmem : ∀ n ∈ Icc 1 Q, F n ∈ (Icc 1 Q) ×ˢ squarefreeUpTo Q := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, hsf⟩ := hab n
    have ha1 : 1 ≤ a n := by
      rcases Nat.eq_zero_or_pos (a n) with h | h
      · rw [h, Nat.mul_zero] at hprod
        omega
      · exact h
    have hb1 : 1 ≤ b n := by
      rcases Nat.eq_zero_or_pos (b n) with h | h
      · rw [h] at hprod
        simp at hprod
        omega
      · exact h
    have hble : b n ≤ n := by
      calc b n ≤ b n ^ 2 := by nlinarith
        _ ≤ b n ^ 2 * a n := Nat.le_mul_of_pos_right _ ha1
        _ = n := hprod
    have hale : a n ≤ n := by
      calc a n ≤ b n ^ 2 * a n := Nat.le_mul_of_pos_left _ (by positivity)
        _ = n := hprod
    exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hb1, le_trans hble hn2⟩,
      mem_squarefreeUpTo.2 ⟨⟨ha1, le_trans hale hn2⟩, hsf⟩⟩
  have hval : ∀ n ∈ Icc 1 Q,
      (1 : ℝ) / n = 1 / ((F n).1 : ℝ) ^ 2 * (1 / ((F n).2 : ℝ)) := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, -⟩ := hab n
    have hcast : ((n : ℕ) : ℝ) = ((b n : ℝ)) ^ 2 * (a n : ℝ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hprod.symm
    simp only [hF]
    rw [hcast]
    field_simp
  calc ∑ n ∈ Icc 1 Q, (1 : ℝ) / n
      = ∑ n ∈ Icc 1 Q, 1 / ((F n).1 : ℝ) ^ 2 * (1 / ((F n).2 : ℝ)) :=
        Finset.sum_congr rfl hval
    _ = ∑ p ∈ (Icc 1 Q).image F, 1 / ((p.1 : ℝ)) ^ 2 * (1 / (p.2 : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (Icc 1 Q) ×ˢ squarefreeUpTo Q, 1 / ((p.1 : ℝ)) ^ 2 * (1 / (p.2 : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
        intro p hp
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
        exact hmem n hn
    _ = (∑ d ∈ Icc 1 Q, (1 : ℝ) / (d : ℝ) ^ 2) * ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q := by
        rw [Finset.sum_product, Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]

/-- **The squarefree harmonic sum is at least `(4/7) log Q`.** -/
theorem four_sevenths_log_le_sum_inv_squarefree (Q : ℕ) :
    4 / 7 * Real.log Q ≤ ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q := by
  have hS : (0 : ℝ) ≤ ∑ q ∈ squarefreeUpTo Q, (1 : ℝ) / q :=
    Finset.sum_nonneg fun q _ => by positivity
  have h1 := log_le_sum_inv Q
  have h2 := sum_inv_le_sum_inv_sq_mul_sum_inv_squarefree Q
  have h3 := sum_inv_sq_Icc_one_le Q
  nlinarith

/-- `siftSum Q ≥ (4/7) log Q`. -/
theorem four_sevenths_log_le_siftSum (Q : ℕ) : 4 / 7 * Real.log Q ≤ siftSum Q :=
  le_trans (four_sevenths_log_le_sum_inv_squarefree Q) (sum_inv_squarefree_le_siftSum Q)

/-! ## The sharp lower bound `siftSum Q ≥ log Q`

The sifting sum is larger than the squarefree harmonic sum, and the classical bound for it has the
constant `1`, not `4/7`: for squarefree `d`,

`∏_{p ∣ d} 1/(p − 1) = ∏_{p ∣ d} (1/p + 1/p² + ⋯) = ∑_{m : rad m = d} 1/m`,

and every `n ≤ Q` occurs in exactly one of these sums, the one indexed by its radical `rad n`,
which is squarefree and at most `n`.  Hence `siftSum Q ≥ ∑_{n ≤ Q} 1/n ≥ log Q`.  The proof below
is the finite form of the same computation: the expansion of the product is replaced by an
induction on the set of prime factors, and the geometric series by its partial sums. -/

/-- The geometric bound `∑_{k=1}^{K} x^k ≤ x/(1 − x)` for `0 ≤ x < 1`. -/
theorem sum_geom_Icc_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑ k ∈ Icc 1 K, x ^ k ≤ x / (1 - x) := by
  have hset : range (K + 1) = insert 0 (Icc 1 K) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (0 : ℕ) ∉ Icc 1 K := by simp
  have hsplit : ∑ k ∈ range (K + 1), x ^ k = 1 + ∑ k ∈ Icc 1 K, x ^ k := by
    rw [hset, Finset.sum_insert hnot, pow_zero]
  have hmul : (∑ i ∈ range (K + 1), x ^ i) * (x - 1) = x ^ (K + 1) - 1 := geom_sum_mul x (K + 1)
  have hpow : (0 : ℝ) ≤ x ^ (K + 1) := by positivity
  have h1x : (0 : ℝ) < 1 - x := by linarith
  rw [le_div_iff₀ h1x]
  nlinarith [hsplit, hmul]

/-- **The reciprocals of the `m ≤ Q` whose prime factors are exactly `P` sum to at most
`∏_{p ∈ P} 1/(p − 1)`.**  The induction removes one prime `p` from `P`, writing `m = p^k m'` with
`k ≥ 1` and `m'` prime to `p`; the factor contributed by `p` is the geometric sum
`∑_{k ≥ 1} p^{-k} ≤ 1/(p − 1)`. -/
theorem sum_inv_primeFactors_eq_le (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ m ∈ (Icc 1 Q).filter (fun m => m.primeFactors = P), (1 : ℝ) / m
      ≤ ∏ p ∈ P, 1 / ((p : ℝ) - 1) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      have hsub : (Icc 1 Q).filter (fun m => m.primeFactors = ∅) ⊆ ({1} : Finset ℕ) := by
        intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
        obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hm1
        have := Nat.primeFactors_eq_empty.mp hm2
        simp only [Finset.mem_singleton]
        omega
      calc ∑ m ∈ (Icc 1 Q).filter (fun m => m.primeFactors = ∅), (1 : ℝ) / m
          ≤ ∑ m ∈ ({1} : Finset ℕ), (1 : ℝ) / m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = 1 := by norm_num
        _ = ∏ p ∈ (∅ : Finset ℕ), 1 / ((p : ℝ) - 1) := by simp
  | insert p P hpP IH =>
      have hp : p.Prime := hP p (Finset.mem_insert_self p P)
      have hPprime : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
      have hIH := IH hPprime
      have hp2 : 2 ≤ p := hp.two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      set T := (Icc 1 Q).filter (fun m => m.primeFactors = insert p P) with hT
      set S := (Icc 1 Q).filter (fun m => m.primeFactors = P) with hS
      set G : ℕ → ℕ × ℕ := fun m => (m.factorization p, m / p ^ m.factorization p) with hG
      have hrecon : ∀ m : ℕ, p ^ (G m).1 * (G m).2 = m := fun m =>
        Nat.ordProj_mul_ordCompl_eq_self m p
      have hinj : ∀ m ∈ T, ∀ n ∈ T, G m = G n → m = n := by
        intro m _ n _ h
        have h1 := hrecon m
        have h2 := hrecon n
        rw [h] at h1
        omega
      have hmem : ∀ m ∈ T, G m ∈ (Icc 1 Q) ×ˢ S := by
        intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
        obtain ⟨hmge, hmle⟩ := Finset.mem_Icc.mp hm1
        have hm0 : m ≠ 0 := by omega
        have hk1 : 1 ≤ m.factorization p := by
          have hmem' : p ∈ m.primeFactors := by rw [hm2]; exact Finset.mem_insert_self p P
          rw [← Nat.support_factorization] at hmem'
          have := Finsupp.mem_support_iff.mp hmem'
          omega
        have hple : p ^ m.factorization p ≤ m := Nat.ordProj_le p hm0
        have hkQ : m.factorization p ≤ Q := by
          have h2k : m.factorization p < 2 ^ m.factorization p := Nat.lt_two_pow_self
          have hmono : (2 : ℕ) ^ m.factorization p ≤ p ^ m.factorization p :=
            Nat.pow_le_pow_left hp2 _
          omega
        have hcompl_pos : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm0
        have hcompl_le : m / p ^ m.factorization p ≤ m := Nat.ordCompl_le m p
        have hpf : (m / p ^ m.factorization p).primeFactors = P := by
          rw [← Nat.support_factorization, Nat.factorization_ordCompl m p, Finsupp.support_erase,
            Nat.support_factorization, hm2, Finset.erase_insert hpP]
        exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hk1, hkQ⟩,
          Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hcompl_pos, le_trans hcompl_le hmle⟩, hpf⟩⟩
      have hval : ∀ m ∈ T,
          (1 : ℝ) / m = ((1 : ℝ) / p) ^ (G m).1 * (1 / ((G m).2 : ℝ)) := by
        intro m _
        have hrec := hrecon m
        have hcast : ((m : ℕ) : ℝ) = (p : ℝ) ^ (G m).1 * ((G m).2 : ℝ) := by
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hrec.symm
        rw [hcast, div_pow, one_pow]
        field_simp
      have hgeom : ∑ k ∈ Icc 1 Q, ((1 : ℝ) / p) ^ k ≤ 1 / ((p : ℝ) - 1) := by
        have h := sum_geom_Icc_le (x := (1 : ℝ) / p) (by positivity)
          (by rw [div_lt_one (by linarith)]; linarith) Q
        have heq : (1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) = 1 / ((p : ℝ) - 1) := by field_simp
        linarith [h, heq.le, heq.ge]
      have hSnn : (0 : ℝ) ≤ ∑ m ∈ S, (1 : ℝ) / m := Finset.sum_nonneg fun m _ => by positivity
      have hprodnn : (0 : ℝ) ≤ ∏ q ∈ P, 1 / ((q : ℝ) - 1) := by
        refine Finset.prod_nonneg fun q hq => ?_
        have hq2 := (hPprime q hq).two_le
        have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
        have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
        positivity
      calc ∑ m ∈ T, (1 : ℝ) / m
          = ∑ m ∈ T, ((1 : ℝ) / p) ^ (G m).1 * (1 / ((G m).2 : ℝ)) := Finset.sum_congr rfl hval
        _ = ∑ z ∈ T.image G, ((1 : ℝ) / p) ^ z.1 * (1 / (z.2 : ℝ)) := by
            rw [Finset.sum_image hinj]
        _ ≤ ∑ z ∈ (Icc 1 Q) ×ˢ S, ((1 : ℝ) / p) ^ z.1 * (1 / (z.2 : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => by positivity)
            intro z hz
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
            exact hmem m hm
        _ = (∑ k ∈ Icc 1 Q, ((1 : ℝ) / p) ^ k) * ∑ m ∈ S, (1 : ℝ) / m := by
            rw [Finset.sum_product, Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
        _ ≤ (1 / ((p : ℝ) - 1)) * ∏ q ∈ P, 1 / ((q : ℝ) - 1) := by
            have h1 : (0 : ℝ) ≤ ∑ k ∈ Icc 1 Q, ((1 : ℝ) / p) ^ k :=
              Finset.sum_nonneg fun k _ => by positivity
            have h2 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
              have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
              positivity
            nlinarith
        _ = ∏ q ∈ insert p P, 1 / ((q : ℝ) - 1) := by rw [Finset.prod_insert hpP]

/-- The radical `∏_{p ∣ n} p` is squarefree. -/
theorem squarefree_prod_primeFactors (n : ℕ) : Squarefree (∏ p ∈ n.primeFactors, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_) (fun p hp => ?_)
  · exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq)
  · exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Every `n ∈ [1, Q]` has the same prime factors as its radical, which is one of the squarefree
`d ≤ Q`. -/
theorem Icc_subset_biUnion_primeFactors (Q : ℕ) :
    Icc 1 Q ⊆ (squarefreeUpTo Q).biUnion
      (fun d => (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors)) := by
  classical
  intro n hn
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
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
  refine Finset.mem_biUnion.2 ⟨d, mem_squarefreeUpTo.2 ⟨⟨hdpos, le_trans hdle hn2⟩, hdsf⟩, ?_⟩
  exact Finset.mem_filter.2 ⟨hn, by rw [hdpf]⟩

/-- **`log Q ≤ siftSum Q`**, the classical lower bound for the sifting sum of the large sieve at
the weights `w p = p − 1`. -/
theorem log_le_siftSum (Q : ℕ) : Real.log Q ≤ siftSum Q := by
  classical
  calc Real.log Q ≤ ∑ n ∈ Icc 1 Q, (1 : ℝ) / n := log_le_sum_inv Q
    _ ≤ ∑ n ∈ (squarefreeUpTo Q).biUnion
          (fun d => (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors)), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_biUnion_primeFactors Q)
          (fun _ _ _ => by positivity)
    _ ≤ ∑ d ∈ squarefreeUpTo Q,
          ∑ m ∈ (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors), (1 : ℝ) / m :=
        sum_biUnion_le_sum_sum _ _ (fun n => by positivity) _
    _ ≤ siftSum Q :=
        Finset.sum_le_sum fun d _ => sum_inv_primeFactors_eq_le Q d.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-! ## The sieve for a set avoiding a residue class modulo every small prime -/

/-- **The large sieve for a set that avoids one residue class modulo every prime `p ≤ Q`.** -/
theorem card_mul_siftSum_le {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * siftSum Q ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
  classical
  have hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ p - 1 := by
    intro p hp hpQ
    obtain ⟨c, hc, hcA⟩ := havoid p hp hpQ
    have hsub : A.image (fun n => n % p) ⊆ (range p).erase c := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_erase.2 ⟨hcA n hn, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
    calc (A.image (fun n => n % p)).card ≤ ((range p).erase c).card := Finset.card_le_card hsub
      _ = p - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.2 hc), Finset.card_range]
  have hmain := card_le_sifted_squarefree hQ hA (fun p => p - 1)
    (fun p hp _ => by have := hp.two_le; omega) (fun p _ _ => Nat.sub_le p 1) hAw
  have hprod : ∀ q ∈ squarefreeUpTo Q,
      ∏ p ∈ q.primeFactors, (((p : ℝ) - ((p - 1 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ))
        = ∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
    intro q _
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ p := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [hc]
    have hnum : (p : ℝ) - ((p : ℝ) - 1) = 1 := by ring
    rw [hnum]
  have hrw : ∑ q ∈ squarefreeUpTo Q,
      ∏ p ∈ q.primeFactors, (((p : ℝ) - ((p - 1 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ)) = siftSum Q :=
    Finset.sum_congr rfl hprod
  rw [hrw] at hmain
  exact hmain

/-! ## Brun–Titchmarsh -/

/-- Shifting by `x` matches the primes of `[x, x + y)` with the `m < y` for which `x + m` is
prime. -/
theorem card_primes_Ico_eq (x y : ℕ) :
    ((Ico x (x + y)).filter Nat.Prime).card
      = ((range y).filter (fun m => (x + m).Prime)).card := by
  classical
  refine Finset.card_nbij' (fun n => n - x) (fun m => x + m) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
    obtain ⟨⟨h1, h2⟩, hp⟩ := hn
    refine ⟨by omega, ?_⟩
    have hx : x + (n - x) = n := by omega
    rw [hx]
    exact hp
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hm ⊢
    exact ⟨⟨by omega, by omega⟩, hm.2⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hn
    change x + (n - x) = n
    omega
  · intro m _
    change x + m - x = m
    omega

/-- A prime `p ≤ Q` misses the residue class `(p − x mod p) mod p` among those `m < y` for which
`x + m` is a prime exceeding `Q`: such an `x + m` cannot be divisible by `p`. -/
theorem shifted_primes_avoid (x y Q : ℕ) {p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) :
    ∃ c < p, ∀ m ∈ ((range y).filter (fun m => (x + m).Prime)).filter (fun m => Q < x + m),
      m % p ≠ c := by
  classical
  refine ⟨(p - x % p) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro m hm hcon
  obtain ⟨hmS, hgt⟩ := Finset.mem_filter.mp hm
  obtain ⟨-, hprime⟩ := Finset.mem_filter.mp hmS
  have hmod : (x + m) % p = 0 := by
    rw [Nat.add_mod, hcon]
    rcases Nat.eq_zero_or_pos (x % p) with h0 | h0
    · simp [h0]
    · have hlt : x % p < p := Nat.mod_lt _ hp.pos
      rw [Nat.mod_eq_of_lt (show p - x % p < p by omega)]
      have hsum : x % p + (p - x % p) = p := by omega
      rw [hsum, Nat.mod_self]
  rcases hprime.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hmod) with h | h
  · have := hp.two_le
    omega
  · omega

/-- `log √y ≥ (log y)/2 − log 2`, because `y < (⌊√y⌋ + 1)² ≤ 4⌊√y⌋²`. -/
theorem half_log_sub_log_two_le_log_sqrt {y : ℕ} (hy : 4 ≤ y) :
    Real.log y / 2 - Real.log 2 ≤ Real.log (Nat.sqrt y) := by
  set Q := Nat.sqrt y with hQdef
  have hQ2 : 2 ≤ Q := by
    have h : Nat.sqrt 4 ≤ Nat.sqrt y := Nat.sqrt_le_sqrt hy
    have h4 : Nat.sqrt 4 = 2 := by norm_num
    omega
  have hlt : y < (Q + 1) ^ 2 := Nat.lt_succ_sqrt' y
  have hnat : y < 4 * Q ^ 2 := by nlinarith
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hle : (y : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by exact_mod_cast hnat.le
  have hlog : Real.log y ≤ Real.log (4 * (Q : ℝ) ^ 2) := Real.log_le_log hyR hle
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4] at hlog
  push_cast at hlog
  linarith

/-- The Brun–Titchmarsh estimate with its two constants left as parameters.  The sifting sum at
`Q = ⌊√y⌋` is at least `(1/2) log y − log 2`, so any `c` below that ratio is admissible in `hc`;
the sieve then gives `|A| c log y ≤ 4.15 y` for the primes of `[x, x + y)` above `√y`, and `K` is
any constant with `K c ≥ 4.15`. -/
theorem card_primes_Ico_le_of_const (x : ℕ) {y : ℕ} {c K : ℝ} (hy : 4 ≤ Real.log y)
    (hcpos : 0 < c) (hc : c * Real.log y ≤ 1 / 2 * Real.log y - Real.log 2)
    (hK : 4.15 ≤ K * c) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ K * y / Real.log y + Real.sqrt y + 1 := by
  classical
  have hy4 : 4 ≤ y := by
    by_contra hcon
    push Not at hcon
    have hy3 : (y : ℝ) ≤ 3 := by exact_mod_cast (by omega : y ≤ 3)
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · norm_num at hy
    · have h1 : Real.log y ≤ Real.log 3 :=
        Real.log_le_log (by exact_mod_cast hy0) hy3
      have h2 : Real.log 3 ≤ 3 - 1 := by
        have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num)
        linarith
      linarith
  set Q := Nat.sqrt y with hQdef
  have hQ2 : 2 ≤ Q := by
    have h : Nat.sqrt 4 ≤ Nat.sqrt y := Nat.sqrt_le_sqrt hy4
    have h4 : Nat.sqrt 4 = 2 := by norm_num
    omega
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  set S := (range y).filter (fun m => (x + m).Prime) with hSdef
  set A := S.filter (fun m => Q < x + m) with hAdef
  set B := S.filter (fun m => ¬ (Q < x + m)) with hBdef
  have hAB : A.card + B.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  -- the small primes of the interval
  have hBcard : B.card ≤ Q + 1 := by
    have hsub : B ⊆ range (Q + 1) := by
      intro m hm
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_range.2 (by omega)
    simpa using Finset.card_le_card hsub
  -- the large primes of the interval, via the sieve
  have hAsub : A ⊆ range y :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmain := card_mul_siftSum_le (N := y) hQ2 hAsub
    (fun p hp hpQ => shifted_primes_avoid x y Q hp hpQ)
  -- lower bound for the sifting sum
  have hlogQ := half_log_sub_log_two_le_log_sqrt hy4
  have hsift0 := log_le_siftSum Q
  have hsift : c * Real.log y ≤ siftSum Q := by
    rw [← hQdef] at hlogQ
    linarith
  -- upper bound for the sieve right-hand side
  have hQsq : (Q : ℝ) ^ 2 ≤ (y : ℝ) := by
    have h : Q ^ 2 ≤ y := Nat.sqrt_le' y
    exact_mod_cast h
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hstep : (A.card : ℝ) * (c * Real.log y) ≤ 4.15 * (y : ℝ) := by
    have h1 : (A.card : ℝ) * (c * Real.log y) ≤ (A.card : ℝ) * siftSum Q :=
      mul_le_mul_of_nonneg_left hsift hAcard0
    have h2 : Real.pi * (y : ℝ) ≤ 3.15 * (y : ℝ) :=
      mul_le_mul_of_nonneg_right hpi hyR.le
    linarith
  have hLpos : (0 : ℝ) < Real.log y := by linarith
  have hA : (A.card : ℝ) ≤ K * (y : ℝ) / Real.log y := by
    rw [le_div_iff₀ hLpos]
    have hcy : c * ((A.card : ℝ) * Real.log y) ≤ c * (K * (y : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left hcy hcpos
  -- the small primes contribute at most `√y + 1`
  have hQle : (Q : ℝ) ≤ Real.sqrt y := by
    nlinarith [Real.sq_sqrt hyR.le, Real.sqrt_nonneg (y : ℝ), Nat.cast_nonneg (α := ℝ) Q]
  have hB : (B.card : ℝ) ≤ Real.sqrt y + 1 := by
    have : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
    linarith
  have hcast : (S.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hAB.symm
  rw [card_primes_Ico_eq, ← hSdef, hcast]
  linarith

/-- **Brun–Titchmarsh, with a non-optimal constant.**  Uniformly in the starting point `x`, the
number of primes in the interval `[x, x + y)` is at most `13 y / log y + √y + 1`, as soon as
`log y ≥ 4`. -/
theorem card_primes_Ico_le (x : ℕ) {y : ℕ} (hy : 4 ≤ Real.log y) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ 13 * y / Real.log y + Real.sqrt y + 1 := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  exact card_primes_Ico_le_of_const (c := 0.326) (K := 13) x hy (by norm_num)
    (by linarith) (by norm_num)

/-- The same bound with the sharper constant `9`, for `log y ≥ 24`: the loss from `√y` in place of
`y` inside the sieve is a fixed additive `log 2`, so it costs less the larger `y` is. -/
theorem card_primes_Ico_le_of_log_ge_24 (x : ℕ) {y : ℕ} (hy : 24 ≤ Real.log y) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ 9 * y / Real.log y + Real.sqrt y + 1 := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  exact card_primes_Ico_le_of_const (c := 0.471) (K := 9) x (by linarith) (by norm_num)
    (by linarith) (by norm_num)

/-- **A Chebyshev-type upper bound for the prime counting function**, the case `x = 0` of
`card_primes_Ico_le`: `π(N) ≤ 13 N / log N + √N + 1` once `log N ≥ 4`.  In particular the primes
have density zero. -/
theorem card_primes_range_le {N : ℕ} (hN : 4 ≤ Real.log N) :
    (((range N).filter Nat.Prime).card : ℝ)
      ≤ 13 * N / Real.log N + Real.sqrt N + 1 := by
  have h := card_primes_Ico_le 0 hN
  rwa [Nat.zero_add, ← Finset.range_eq_Ico] at h

end BrunTitchmarsh

end RiemannHypothesis
