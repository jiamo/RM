/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BrunTitchmarshSharp
import RiemannHypothesis.LargeSieveMV

/-!
# Brun–Titchmarsh with the constant `2 + ε`

`RiemannHypothesis/LargeSieveMV.lean` proves the large sieve with the Montgomery–Vaughan constant
`N + δ⁻¹`.  This file carries that constant down the chain of the repository, which until now
ran on Gallagher's `δ⁻¹ + π N`:

* `large_sieve_farey_mv` and `large_sieve_farey_pairs_mv` — the large sieve at the Farey fractions
  of order `Q`, with `Q² + N` in place of `Q² + π N`;
* `card_le_sifted_squarefree_mv` — Montgomery's sieve with `Q² + N`;
* `card_mul_siftSum_le_mv`, `card_mul_siftSumCoprime_le_mv` — its two specializations used by
  Brun–Titchmarsh;
* `card_primes_Ico_le_of_level_mv` — `#{p prime : x ≤ p < x + y} ≤ (Q² + y)/log Q + Q + 1`;
* `card_primes_Ico_le_two` — **Brun–Titchmarsh with the constant `2 + ε`**: for every `ε > 0`
  there is `Y` with `#{p prime : x ≤ p < x + y} ≤ (2 + ε) y / log y` for all `y ≥ Y` and all `x`;
* `card_primes_Ico_mod_le_of_level_mv`, `card_primes_Ico_mod_le_two` — the same in an arithmetic
  progression, with `(2 + ε) (q/φ(q)) Y / log Y`, `Y = ⌊y/q⌋ + 1`;
* `card_primes_range_le_two` — `π(N) ≤ (2 + ε) N / log N` for large `N`.

## Proof

Each theorem is the corresponding theorem of `LargeSieveFarey`, `LargeSieveSquarefree`,
`BrunTitchmarsh`, `BrunTitchmarshProgressions` and `BrunTitchmarshSharp`, with the same proof,
started from `large_sieve_mv` instead of `large_sieve_gallagher`; the factor `π` disappears from
every constant.  In the optimization `level_bound_le_two` (level `Q = ⌊√y / log y⌋`) the main term
is now `(Q² + y)/log Q ≤ (2 + ε/2) y / log y`.  The existing theorems are untouched.

## Scope

What is proved is `2 + ε` for `y ≥ Y(ε)`.  Montgomery and Vaughan prove the exact constant `2`
for every `y > 1`; that needs an explicit treatment of the lower-order terms and is not claimed.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace BrunTitchmarshTwo

open KusminLandau LargeSieve LargeSieveFarey LargeSieveSifted LargeSieveSquarefree LargeSieveMV
  BrunTitchmarsh

/-- **The large sieve over a set of rationals of bounded denominator.**  For a finite set `s`
of rationals in `[0, 1)` all of whose denominators are at most `Q`,
`∑_{x ∈ s} ‖∑_{n < N} a n e(n x)‖² ≤ (Q² + N) ∑_{n < N} ‖a n‖²`. -/
theorem large_sieve_farey_mv {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ x ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  set δ : ℝ := 1 / ((Q : ℝ) ^ 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    have h4 : (2 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) h4
  have hinv : δ⁻¹ = (Q : ℝ) ^ 2 := by
    rw [hδdef, one_div, inv_inv]
  have hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ intDist ((x : ℝ) - (y : ℝ)) := fun x hx y hy hxy =>
    inv_sq_le_intDist_sub (hmem x hx) (hmem y hy) (hden x hx) (hden y hy) hxy
  have := large_sieve_mv (s := s) (t := fun x : ℚ => (x : ℝ)) hδ hδ2 hsep a N
  rw [hinv] at this
  refine this.trans (le_of_eq ?_)
  ring

/-- **The arithmetic large sieve**, in its classical double-sum form over reduced fractions. -/
theorem large_sieve_farey_pairs_mv {Q : ℕ} (hQ : 2 ≤ Q) (a : ℕ → ℂ) (N : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  classical
  have hmemq : ∀ q ∈ Icc 1 Q, ∀ x ∈ ((range q).filter (fun b => Nat.Coprime b q)).image
      (fun b : ℕ => (b : ℚ) / q), x.den = q ∧ x ∈ Set.Ico (0 : ℚ) 1 := by
    intro q hq x hx
    rw [Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Finset.mem_filter, Finset.mem_range] at hb
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    exact ⟨den_natCast_div hq0 hb.2, mem_Ico_natCast_div hq0 hb.1⟩
  have hdisj : Set.PairwiseDisjoint (↑(Icc 1 Q) : Set ℕ)
      (fun q : ℕ => ((range q).filter (fun b => Nat.Coprime b q)).image
        (fun b : ℕ => (b : ℚ) / q)) := by
    intro q hq q' hq' hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hmemq q (Finset.mem_coe.mp hq) x hx).1
    have h2 := (hmemq q' (Finset.mem_coe.mp hq') x hx').1
    exact hne (h1 ▸ h2 ▸ rfl)
  have hmemS : ∀ x ∈ (Icc 1 Q).biUnion (fun q : ℕ =>
      ((range q).filter (fun b => Nat.Coprime b q)).image (fun b : ℕ => (b : ℚ) / q)),
      x ∈ Set.Ico (0 : ℚ) 1 := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    exact (hmemq q hq x hxq).2
  have hdenS : ∀ x ∈ (Icc 1 Q).biUnion (fun q : ℕ =>
      ((range q).filter (fun b => Nat.Coprime b q)).image (fun b : ℕ => (b : ℚ) / q)),
      x.den ≤ Q := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    rw [(hmemq q hq x hxq).1]
    exact (Finset.mem_Icc.mp hq).2
  have key := large_sieve_farey_mv hQ hmemS hdenS a N
  rw [Finset.sum_biUnion hdisj] at key
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  rw [Finset.sum_image (fun b _ b' _ h => by
    field_simp at h
    exact_mod_cast h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  norm_num

/-- **Montgomery's sieve.**  If `A ⊆ [0, N)` meets at most `w p` residue classes modulo every
prime `p ≤ Q`, then `|A| ∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/(w p) ≤ Q² + N`. -/
theorem card_le_sifted_squarefree_mv {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (w : ℕ → ℕ) (hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p) (hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p)
    (hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ (Q : ℝ) ^ 2 + N := by
  classical
  set a : ℕ → ℂ := fun n => if n ∈ A then 1 else 0 with ha
  have hsumA : ∀ f : ℕ → ℂ, ∑ n ∈ range N, a n * f n = ∑ n ∈ A, f n := by
    intro f
    simp only [ha, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hA]
  have hnorm : ∑ n ∈ range N, ‖a n‖ ^ 2 = (A.card : ℝ) := by
    have hpt : ∀ n ∈ range N, ‖a n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      intro n _
      by_cases h : n ∈ A <;> simp [ha, h]
    rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.inter_eq_right.2 hA,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hls := large_sieve_farey_pairs_mv hQ a N
  rw [hnorm] at hls
  have hinner : ∀ q ∈ Icc 1 Q, ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
        = ‖indSum A q b‖ ^ 2 := by
    intro q _ b _
    rw [hsumA]
    rfl
  have hls' : ∑ q ∈ Icc 1 Q, redSq A q ≤ ((Q : ℝ) ^ 2 + N) * (A.card : ℝ) := by
    refine le_trans (le_of_eq ?_) hls
    exact (Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun b hb =>
      (hinner q hq b hb).symm)
  have hsub : squarefreeUpTo Q ⊆ Icc 1 Q := by
    intro q hq
    obtain ⟨⟨h1, h2⟩, _⟩ := mem_squarefreeUpTo.mp hq
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  have hnn : ∀ q ∈ Icc 1 Q, q ∉ squarefreeUpTo Q → (0 : ℝ) ≤ redSq A q :=
    fun q _ _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hrestrict : ∑ q ∈ squarefreeUpTo Q, redSq A q ≤ ∑ q ∈ Icc 1 Q, redSq A q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hlow : (A.card : ℝ) ^ 2
        * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ ∑ q ∈ squarefreeUpTo Q, redSq A q := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨⟨h1, h2⟩, hsf⟩ := mem_squarefreeUpTo.mp hq
    have hmem : ∀ p ∈ q.primeFactors, p.Prime ∧ p ≤ Q := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      exact ⟨hpp, le_trans (Nat.le_of_dvd (by omega) hpd) h2⟩
    exact sq_card_mul_prod_le_redSq A w hsf
      (fun p hp => hwpos p (hmem p hp).1 (hmem p hp).2)
      (fun p hp => hwle p (hmem p hp).1 (hmem p hp).2)
      (fun p hp => hAw p (hmem p hp).1 (hmem p hp).2)
  have hmain : (A.card : ℝ) ^ 2
        * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ ((Q : ℝ) ^ 2 + N) * (A.card : ℝ) :=
    le_trans hlow (le_trans hrestrict hls')
  rcases Nat.eq_zero_or_pos A.card with hcard | hcard
  · have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 + N := by positivity
    simp [hcard, hQ0]
  · have hcR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hcard
    refine le_of_mul_le_mul_right ?_ hcR
    calc ((A.card : ℝ)
            * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p))
          * (A.card : ℝ)
        = (A.card : ℝ) ^ 2
            * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) := by ring
      _ ≤ ((Q : ℝ) ^ 2 + N) * (A.card : ℝ) := hmain

/-- **The large sieve for a set that avoids one residue class modulo every prime `p ≤ Q`.** -/
theorem card_mul_siftSum_le_mv {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * siftSum Q ≤ (Q : ℝ) ^ 2 + N := by
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
  have hmain := card_le_sifted_squarefree_mv hQ hA (fun p => p - 1)
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

/-- **Brun–Titchmarsh at an arbitrary sieve level `Q ≥ 2`.**  Uniformly in the starting point `x`,

`#{p prime : x ≤ p < x + y} ≤ (Q² + y)/log Q + Q + 1`.

The primes of the interval that exceed `Q` avoid a residue class modulo every prime `p ≤ Q`, so
the large sieve applies to them; the primes at most `Q` are at most `Q + 1` in number. -/
theorem card_primes_Ico_le_of_level_mv (x y : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + y) / Real.log Q + Q + 1 := by
  classical
  set S := (range y).filter (fun m => (x + m).Prime) with hSdef
  set A := S.filter (fun m => Q < x + m) with hAdef
  set B := S.filter (fun m => ¬ (Q < x + m)) with hBdef
  have hAB : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
  have hBcard : B.card ≤ Q + 1 := by
    have hsub : B ⊆ range (Q + 1) := by
      intro m hm
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_range.2 (by omega)
    simpa using Finset.card_le_card hsub
  have hAsub : A ⊆ range y :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmain := card_mul_siftSum_le_mv (N := y) hQ hAsub
    (fun p hp hpQ => shifted_primes_avoid x y Q hp hpQ)
  have hlogpos : 0 < Real.log Q := by
    have h2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 1) (by linarith : (1:ℝ) < (Q : ℝ))
    simpa using this
  have hsift : Real.log Q ≤ siftSum Q := log_le_siftSum Q
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hA : (A.card : ℝ) ≤ ((Q : ℝ) ^ 2 + y) / Real.log Q := by
    rw [le_div_iff₀ hlogpos]
    calc (A.card : ℝ) * Real.log Q ≤ (A.card : ℝ) * siftSum Q :=
          mul_le_mul_of_nonneg_left hsift hAcard0
      _ ≤ (Q : ℝ) ^ 2 + y := hmain
  have hB : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
  have hcast : (S.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hAB.symm
  rw [card_primes_Ico_eq, ← hSdef, hcast]
  linarith

set_option maxHeartbeats 1000000 in
-- the numeric chain of the proof is long, and does not fit in the default heartbeat budget
/-- **The numeric heart of the optimization**, at the sieve level `Q = ⌊√y / log y⌋`, for `ε ≤ 1`
and with the threshold made explicit: `log y ≥ (1000/ε)² + 10⁶` suffices.  For every `c ≥ 1`,

`(Q² + y) c / log Q + Q + 1 ≤ (2 + ε) c y / log y`.

The factor `c` is `1` for the interval form and `q/φ(q)` for the arithmetic-progression form. -/
theorem level_bound_le_two {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      2 ≤ ⌊Real.sqrt y / Real.log y⌋₊ ∧
      ∀ c : ℝ, 1 ≤ c →
        (((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ) ^ 2 + y) * c
              / Real.log ((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ)
            + ((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ) + 1
          ≤ (2 + eps) * c * y / Real.log y := by
  classical
  set T : ℝ := (1000 / eps) ^ 2 + 10 ^ 6 with hT
  refine ⟨max 3 ⌈Real.exp T⌉₊, le_max_left _ _, ?_⟩
  intro y hy
  -- the height is at least `exp T`, so `t = log y ≥ T`
  have hyexp : Real.exp T ≤ (y : ℝ) := by
    have h1 : ((⌈Real.exp T⌉₊ : ℕ) : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast le_trans (le_max_right 3 _) hy
    exact (Nat.le_ceil _).trans h1
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (Real.exp_pos T) hyexp
  set t : ℝ := Real.log y with htdef
  have hTt : T ≤ t := by
    have := Real.log_le_log (Real.exp_pos T) hyexp
    rwa [Real.log_exp] at this
  -- `u = √t` is large, and `eps · u ≥ 1000`
  set u : ℝ := Real.sqrt t with hudef
  have ht6 : (10 : ℝ) ^ 6 ≤ t := by
    have h0 : (0 : ℝ) ≤ (1000 / eps) ^ 2 := sq_nonneg _
    rw [hT] at hTt; linarith
  have htpos : (0 : ℝ) < t := by nlinarith
  have hu2 : u ^ 2 = t := Real.sq_sqrt htpos.le
  have hupos : (0 : ℝ) < u := Real.sqrt_pos.mpr htpos
  have hu1000 : (1000 : ℝ) ≤ u := by nlinarith [hu2, ht6, hupos]
  have hepsu : (1000 : ℝ) ≤ eps * u := by
    have hsq : (1000 / eps) ^ 2 ≤ t := by rw [hT] at hTt; nlinarith
    have hnn : (0 : ℝ) ≤ 1000 / eps := by positivity
    have hle : (1000 / eps) ≤ u := by nlinarith [hu2, hupos, hnn]
    calc (1000 : ℝ) = eps * (1000 / eps) := by field_simp
      _ ≤ eps * u := mul_le_mul_of_nonneg_left hle heps.le
  -- the sieve level `Q = ⌊√y / log y⌋`
  set s : ℝ := Real.sqrt y with hsdef
  have hs2 : s ^ 2 = (y : ℝ) := Real.sq_sqrt hy0.le
  have hspos : (0 : ℝ) < s := Real.sqrt_pos.mpr hy0
  have hlogs : Real.log s = t / 2 := by rw [hsdef, Real.log_sqrt hy0.le]
  have hs_ge : t ^ 2 / 16 ≤ s := sq_log_le_sixteen_mul_sqrt hy0 (by linarith)
  set Q : ℕ := ⌊s / t⌋₊ with hQdef
  set q : ℝ := (Q : ℝ) with hqdef
  have hst_pos : (0 : ℝ) < s / t := by positivity
  have hst_big : (62500 : ℝ) ≤ s / t := by
    rw [le_div_iff₀ htpos]
    nlinarith [hs_ge, ht6, htpos]
  have hq_le : q ≤ s / t := Nat.floor_le hst_pos.le
  have hq_ge : s / t - 1 ≤ q := by
    have h := Nat.lt_floor_add_one (s / t)
    rw [← hQdef, ← hqdef] at h
    linarith
  have hq_big : (62499 : ℝ) ≤ q := by linarith
  have hQ2 : 2 ≤ Q := by
    by_contra hcon
    push Not at hcon
    have hq1 : q ≤ 1 := by
      rw [hqdef]
      exact_mod_cast Nat.lt_succ_iff.mp (by omega : Q < 2)
    linarith
  have hqpos : (0 : ℝ) < q := by linarith
  -- `log Q ≥ t/2 − log t − 1`
  have hhalf : s / (2 * t) ≤ q := by
    have h2 : s / (2 * t) = s / t / 2 := by rw [div_div, mul_comm]
    rw [h2]; linarith
  have hhalf_pos : (0 : ℝ) < s / (2 * t) := by positivity
  have hlogq : t / 2 - Real.log t - 1 ≤ Real.log q := by
    have hmono : Real.log (s / (2 * t)) ≤ Real.log q := Real.log_le_log hhalf_pos hhalf
    have hexpand : Real.log (s / (2 * t)) = t / 2 - Real.log 2 - Real.log t := by
      rw [Real.log_div hspos.ne' (by positivity), Real.log_mul (by norm_num) htpos.ne', hlogs]
      ring
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [hexpand] at hmono
    linarith
  have hlogt : Real.log t ≤ 2 * u := by
    have h := log_le_two_mul_sqrt htpos
    rwa [← hudef] at h
  have hDpos : (0 : ℝ) < Real.log q := by
    have h1 : Real.log 1 < Real.log q := Real.log_lt_log (by norm_num) (by linarith)
    simpa using h1
  have hApos : (0 : ℝ) ≤ (y : ℝ) / t := by positivity
  have hq_sq : q ^ 2 ≤ (y : ℝ) / t ^ 2 := by
    have h1 : q ^ 2 ≤ (s / t) ^ 2 := by nlinarith [hq_le, hqpos]
    have h2 : (s / t) ^ 2 = (y : ℝ) / t ^ 2 := by rw [div_pow, hs2]
    linarith [h2.symm.le, h2.le]
  -- the main term
  have hpart1 : (q ^ 2 + y) / Real.log q ≤ (2 + eps / 2) * ((y : ℝ) / t) := by
    rw [div_le_iff₀ hDpos]
    have hkey : (1 : ℝ) / t + (2 + eps / 2) * (Real.log t + 1) ≤ eps / 4 * t := by
      have h7 : 2 + eps / 2 ≤ 7 := by linarith
      have h1t : (1 : ℝ) / t ≤ 1 := by rw [div_le_one htpos]; linarith
      have hnn : (0 : ℝ) ≤ Real.log t + 1 := by
        nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)]
      have hlt1 : (2 + eps / 2) * (Real.log t + 1) ≤ 7 * (2 * u + 1) :=
        mul_le_mul h7 (by linarith) hnn (by norm_num)
      have hfin : 14 * u + 8 ≤ eps / 4 * t := by
        have hid : eps / 4 * t = u / 4 * (eps * u) := by rw [← hu2]; ring
        have h1 : u / 4 * 1000 ≤ u / 4 * (eps * u) :=
          mul_le_mul_of_nonneg_left hepsu (by positivity)
        rw [hid]; linarith
      linarith
    have hkey' : (1 : ℝ) / t + t
        ≤ (2 + eps / 2) * (t / 2 - Real.log t - 1) := by
      have hexpand : (2 + eps / 2) * (t / 2 - Real.log t - 1)
          = t + eps / 4 * t - (2 + eps / 2) * (Real.log t + 1) := by ring
      rw [hexpand]; linarith
    have hstep2 : (y : ℝ) / t ^ 2 + y
        ≤ (2 + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1) := by
      have hrw : (2 + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1)
          = ((y : ℝ) / t) * ((2 + eps / 2) * (t / 2 - Real.log t - 1)) := by ring
      have hrw2 : (y : ℝ) / t ^ 2 + y = ((y : ℝ) / t) * (1 / t + t) := by
        field_simp
      rw [hrw, hrw2]
      exact mul_le_mul_of_nonneg_left hkey' hApos
    have hstep3 : (2 + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1)
        ≤ (2 + eps / 2) * ((y : ℝ) / t) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    linarith [hq_sq, hstep2, hstep3]
  -- the primes below the sieve level
  have hpart2 : q + 1 ≤ eps / 2 * ((y : ℝ) / t) := by
    have hmul : (0 : ℝ) ≤ t * (t - 16) := mul_nonneg htpos.le (by linarith)
    have hst : t ≤ s := by linarith [hs_ge, hmul]
    have hepss : (4 : ℝ) ≤ eps * s := by
      have h2 : eps * (t ^ 2 / 16) ≤ eps * s := mul_le_mul_of_nonneg_left hs_ge heps.le
      have h3 : eps * (t ^ 2 / 16) = u ^ 3 / 16 * (eps * u) := by rw [← hu2]; ring
      have h4 : u ^ 3 / 16 * 1000 ≤ u ^ 3 / 16 * (eps * u) :=
        mul_le_mul_of_nonneg_left hepsu (by positivity)
      have hA : (1000 : ℝ) * 1000 ≤ u * u := mul_le_mul hu1000 hu1000 (by norm_num) (by linarith)
      have hB : (1000 : ℝ) * 1000 * 1000 ≤ u * u * u :=
        mul_le_mul hA hu1000 (by norm_num) (by positivity)
      have h5 : (4 : ℝ) ≤ u ^ 3 / 16 * 1000 := by linarith [hB]
      linarith
    have hnum : (0 : ℝ) ≤ eps / 2 * (y : ℝ) - s - t := by
      have h6 : s / 2 * 4 ≤ s / 2 * (eps * s) :=
        mul_le_mul_of_nonneg_left hepss (by positivity)
      have h7 : eps / 2 * (y : ℝ) = s / 2 * (eps * s) := by rw [← hs2]; ring
      linarith
    have hfrac : eps / 2 * ((y : ℝ) / t) - (s / t + 1) = (eps / 2 * (y : ℝ) - s - t) / t := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ eps / 2 * ((y : ℝ) / t) - (s / t + 1) := by
      rw [hfrac]; exact div_nonneg hnum htpos.le
    linarith [hq_le]
  refine ⟨hQ2, fun c hc => ?_⟩
  have hcnn : (0 : ℝ) ≤ c := by linarith
  have hmain : (q ^ 2 + y) * c / Real.log q
      ≤ (2 + eps / 2) * ((y : ℝ) / t) * c := by
    have hrw : (q ^ 2 + y) * c / Real.log q
        = ((q ^ 2 + y) / Real.log q) * c := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hpart1 hcnn
  have hsmall : q + 1 ≤ eps / 2 * ((y : ℝ) / t) * c := by
    have h1 : eps / 2 * ((y : ℝ) / t) * 1 ≤ eps / 2 * ((y : ℝ) / t) * c :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    linarith [hpart2]
  have hgoal : (2 + eps) * c * (y : ℝ) / t
      = (2 + eps / 2) * ((y : ℝ) / t) * c + eps / 2 * ((y : ℝ) / t) * c := by
    field_simp
    ring
  rw [hgoal]
  linarith [hmain, hsmall]

/-- Brun–Titchmarsh with the constant `2 + ε`, for `ε ≤ 1` and with `3 ≤ Y`. -/
theorem card_primes_Ico_le_two_aux {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 + eps) * y / Real.log y := by
  obtain ⟨Y, hY3, hY⟩ := level_bound_le_two heps heps1
  refine ⟨Y, hY3, fun y hy x => ?_⟩
  obtain ⟨hQ2, hbound⟩ := hY y hy
  refine (card_primes_Ico_le_of_level_mv x y hQ2).trans ?_
  have h := hbound 1 le_rfl
  simpa using h

/-- **Brun–Titchmarsh with the constant `2 + ε`.**  For every `ε > 0` there is a threshold `Y`
such that, for every `y ≥ Y` and every starting point `x`,

`#{p prime : x ≤ p < x + y} ≤ (2 + ε) y / log y`.

Montgomery and Vaughan prove the exact constant `2` for every `y > 1`; this is the weaker
`2 + ε` for `y ≥ Y(ε)`. -/
theorem card_primes_Ico_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 + eps) * y / Real.log y := by
  rcases le_total eps 1 with hle | hge
  · obtain ⟨Y, -, hY⟩ := card_primes_Ico_le_two_aux heps hle
    exact ⟨Y, hY⟩
  · obtain ⟨Y, hY3, hY⟩ := card_primes_Ico_le_two_aux (eps := 1) one_pos le_rfl
    refine ⟨Y, fun y hy x => (hY y hy x).trans ?_⟩
    have hy3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hY3 hy
    have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
    have hynn : (0 : ℝ) ≤ (y : ℝ) := by linarith
    gcongr

/-- **The large sieve for a set that avoids one residue class modulo every prime `p ≤ Q` that does
not divide `q`.** -/
theorem card_mul_siftSumCoprime_le_mv {N Q q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * siftSumCoprime q Q ≤ (Q : ℝ) ^ 2 + N := by
  classical
  set w : ℕ → ℕ := fun p => if p ∣ q then p else p - 1 with hw
  have hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p := by
    intro p hp _
    have := hp.two_le
    simp only [hw]
    split <;> omega
  have hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p := by
    intro p hp _
    have := hp.two_le
    simp only [hw]
    split <;> omega
  have hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p := by
    intro p hp hpQ
    by_cases hd : p ∣ q
    · simp only [hw, if_pos hd]
      have hsub : A.image (fun n => n % p) ⊆ range p := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_range.2 (Nat.mod_lt _ hp.pos)
      simpa using Finset.card_le_card hsub
    · simp only [hw, if_neg hd]
      obtain ⟨c, hc, hcA⟩ := havoid p hp hpQ hd
      have hsub : A.image (fun n => n % p) ⊆ (range p).erase c := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_erase.2 ⟨hcA n hn, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
      calc (A.image (fun n => n % p)).card ≤ ((range p).erase c).card := Finset.card_le_card hsub
        _ = p - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_range.2 hc), Finset.card_range]
  have hmain := card_le_sifted_squarefree_mv hQ hA w hwpos hwle hAw
  have hzero : ∀ d ∈ squarefreeUpTo Q,
      d ∉ (squarefreeUpTo Q).filter (fun d => Nat.Coprime d q) →
      ∏ p ∈ d.primeFactors, (((p : ℝ) - w p) / w p) = 0 := by
    intro d hd hnot
    have hnc : ¬ Nat.Coprime d q := fun hcop => hnot (Finset.mem_filter.2 ⟨hd, hcop⟩)
    obtain ⟨⟨hd1, hd2⟩, -⟩ := mem_squarefreeUpTo.mp hd
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd d q) hnc
    have hpd : p ∣ d := hpdvd.trans (Nat.gcd_dvd_left d q)
    have hpq : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right d q)
    refine Finset.prod_eq_zero (i := p) (Nat.mem_primeFactors.2 ⟨hp, hpd, by omega⟩) ?_
    simp only [hw, if_pos hpq]
    simp
  have hcongr : ∀ d ∈ (squarefreeUpTo Q).filter (fun d => Nat.Coprime d q),
      ∏ p ∈ d.primeFactors, (((p : ℝ) - w p) / w p)
        = ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
    intro d hd
    obtain ⟨hdmem, hcop⟩ := Finset.mem_filter.mp hd
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpq : ¬ p ∣ q := by
      intro hcon
      have hdvd : p ∣ Nat.gcd d q := Nat.dvd_gcd hpd hcon
      rw [hcop] at hdvd
      exact hpp.ne_one (Nat.dvd_one.mp hdvd)
    simp only [hw, if_neg hpq]
    have hp2 : 2 ≤ p := hpp.two_le
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ p := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [hc, show (p : ℝ) - ((p : ℝ) - 1) = 1 by ring]
  have hsum : ∑ d ∈ squarefreeUpTo Q, ∏ p ∈ d.primeFactors, (((p : ℝ) - w p) / w p)
      = siftSumCoprime q Q := by
    rw [siftSumCoprime, ← Finset.sum_subset (Finset.filter_subset _ _) hzero]
    exact Finset.sum_congr rfl hcongr
  rw [hsum] at hmain
  exact hmain

/-- **Brun–Titchmarsh in arithmetic progressions, at an arbitrary sieve level `Q ≥ 2`.**  Write
`Y = ⌊y/q⌋ + 1`.  Uniformly in the starting point `x` and in the residue `a < q`, the number of
primes in `[x, x + y)` congruent to `a` modulo `q` is at most
`(Q² + Y) q / (φ(q) log Q) + Q + 1`.

The level is free: `Q = ⌊√Y / log Y⌋` gives the constant `2 + ε` of
`card_primes_Ico_mod_le_two`. -/
theorem card_primes_Ico_mod_le_of_level_mv {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x y : ℕ) {Q : ℕ}
    (hQlevel : 2 ≤ Q) :
    (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + ((y / q + 1 : ℕ) : ℝ)) * q
            / ((q.totient : ℝ) * Real.log Q)
          + Q + 1 := by
  classical
  set Y := y / q + 1 with hY
  set r := modOffset x q a with hr
  set b := x + r with hb
  set S := (Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a) with hS
  set T := (range Y).filter (fun t => (b + q * t).Prime) with hT
  set A := T.filter (fun t => Q < b + q * t) with hA
  set B := T.filter (fun t => ¬ Q < b + q * t) with hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hYpos : 0 < Y := by rw [hY]; exact Nat.succ_pos _
  have hQ2 : 2 ≤ Q := hQlevel
  have hrlt : r < q := modOffset_lt hq x a
  -- every prime of the progression is `b + q t` for a parameter `t < Y`
  have hparam : ∀ n ∈ S, n = b + q * ((n - b) / q) ∧ (n - b) / q < Y := by
    intro n hn
    obtain ⟨hnI, hnp, hna⟩ := Finset.mem_filter.mp hn
    obtain ⟨hx1, hx2⟩ := Finset.mem_Ico.mp hnI
    obtain ⟨t, ht⟩ := exists_param hq ha hx1 hna
    rw [← hr, ← hb] at ht
    have hdiv : (n - b) / q = t := by
      rw [ht, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
    have hqt : q * t < y := by
      have h2 : b + q * t < x + y := by rw [← ht]; exact hx2
      have h3 : x ≤ b := by omega
      omega
    have htY : t < Y := by
      have h1 : t * q ≤ y := by rw [Nat.mul_comm]; exact hqt.le
      have h2 : t ≤ y / q := (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr h1
      omega
    exact ⟨by rw [hdiv]; exact ht, by rw [hdiv]; exact htY⟩
  have hScard : S.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun n => (n - b) / q) ?_ ?_
    · intro n hn
      obtain ⟨heq, hlt⟩ := hparam n hn
      obtain ⟨-, hnp, -⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, ?_⟩
      rw [← heq]
      exact hnp
    · intro n1 h1 n2 h2 heq
      simp only at heq
      rw [(hparam n1 h1).1, (hparam n2 h2).1, heq]
  have hAB : A.card + B.card = T.card := Finset.card_filter_add_card_filter_not _
  -- the primes of the progression below the sieve level
  have hBcard : B.card ≤ Q + 1 := by
    have hsub : B ⊆ range (Q + 1) := by
      intro t ht
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp ht
      have h1 : b + q * t ≤ Q := by simpa using Nat.not_lt.mp (by simpa using hle)
      have h2 : t ≤ q * t := Nat.le_mul_of_pos_left t (by omega)
      exact Finset.mem_range.2 (by omega)
    simpa using Finset.card_le_card hsub
  -- the primes of the progression above the sieve level, via the sieve
  have hAsub : A ⊆ range Y := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmain := card_mul_siftSumCoprime_le_mv (N := Y) (q := q) hQ2 hAsub
    (fun p hp hpQ hpq => progression_avoid b Y Q hp hpQ hpq)
  have hsift0 := totient_log_le_siftSumCoprime hq Q
  set L := Real.log ((Q : ℕ) : ℝ) with hL
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (by omega : 0 < q)
    exact_mod_cast h
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  clear_value A B T S L b r Y
  have hstep : (A.card : ℝ) * ((q.totient : ℝ) / q * L) ≤ (Q : ℝ) ^ 2 + (Y : ℝ) := by
    have h1 : (A.card : ℝ) * ((q.totient : ℝ) / q * L) ≤ (A.card : ℝ) * siftSumCoprime q Q :=
      mul_le_mul_of_nonneg_left hsift0 hAcard0
    linarith
  have hAle : (A.card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + (Y : ℝ)) * q / ((q.totient : ℝ) * L) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q.totient : ℝ) * L)]
    have hid : (A.card : ℝ) * ((q.totient : ℝ) / q * L) * q
        = (A.card : ℝ) * ((q.totient : ℝ) * L) := by field_simp
    nlinarith [hstep, hqR]
  have hBle : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
  have hScast : (S.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    have h : S.card ≤ A.card + B.card := by omega
    exact_mod_cast h
  linarith

/-- The progression form for `ε ≤ 1`, with `3 ≤ Y₀`. -/
theorem card_primes_Ico_mod_le_two_aux {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y₀ : ℕ, 3 ≤ Y₀ ∧ ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ) := by
  obtain ⟨Y₀, hY3, hY⟩ := level_bound_le_two heps heps1
  refine ⟨Y₀, hY3, fun q a hq ha x y hy => ?_⟩
  set n : ℕ := y / q + 1 with hn
  obtain ⟨hQ2, hbound⟩ := hY n hy
  set Q : ℕ := ⌊Real.sqrt (n : ℝ) / Real.log (n : ℝ)⌋₊ with hQ
  -- the factor `c = q/φ(q) ≥ 1`
  have hqpos : 0 < q := hq
  have hphi : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hphiR : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast hphi
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hle : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hc : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := (one_le_div hphiR).mpr hle
  have hbase := card_primes_Ico_mod_le_of_level_mv hq ha x y (Q := Q) hQ2
  refine hbase.trans ?_
  have hrw : ((Q : ℝ) ^ 2 + ((y / q + 1 : ℕ) : ℝ)) * q
        / ((q.totient : ℝ) * Real.log (Q : ℝ))
      = ((Q : ℝ) ^ 2 + (n : ℝ)) * ((q : ℝ) / (q.totient : ℝ))
        / Real.log (Q : ℝ) := by
    rw [← hn]
    field_simp
  rw [hrw]
  exact hbound ((q : ℝ) / (q.totient : ℝ)) hc

/-- **Brun–Titchmarsh in arithmetic progressions with the constant `2 + ε`.**  For every
`ε > 0` there is a threshold `Y₀` such that, whenever `⌊y/q⌋ + 1 ≥ Y₀`, the number of primes of
`[x, x + y)` in any fixed residue class `a` modulo `q` is at most

`(2 + ε) (q/φ(q)) Y / log Y`,  with `Y = ⌊y/q⌋ + 1`,

uniformly in the starting point `x`, in the modulus `q` and in the residue `a`. -/
theorem card_primes_Ico_mod_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y₀ : ℕ, ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ) := by
  rcases le_total eps 1 with hle | hge
  · obtain ⟨Y₀, -, hY⟩ := card_primes_Ico_mod_le_two_aux heps hle
    exact ⟨Y₀, hY⟩
  · obtain ⟨Y₀, hY3, hY⟩ := card_primes_Ico_mod_le_two_aux (eps := 1) one_pos le_rfl
    refine ⟨Y₀, fun q a hq ha x y hy => (hY q a hq ha x y hy).trans ?_⟩
    have hn3 : (3 : ℝ) ≤ ((y / q + 1 : ℕ) : ℝ) := by exact_mod_cast le_trans hY3 hy
    have hlogpos : 0 < Real.log ((y / q + 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hphi : 0 < q.totient := Nat.totient_pos.mpr hq
    have hphiR : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast hphi
    have hcnn : (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := by positivity
    gcongr

/-- **A Chebyshev-type upper bound with the constant `2`**, the case `x = 0` of
`card_primes_Ico_le_two`: for every `ε > 0`, `π(N) ≤ (2 + ε) N / log N` for all large `N`. -/
theorem card_primes_range_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ N : ℕ, Y ≤ N →
      (((range N).filter Nat.Prime).card : ℝ) ≤ (2 + eps) * N / Real.log N := by
  obtain ⟨Y, hY⟩ := card_primes_Ico_le_two heps
  refine ⟨Y, fun N hN => ?_⟩
  have h := hY N hN 0
  rwa [Nat.zero_add, ← Finset.range_eq_Ico] at h

end BrunTitchmarshTwo

end RiemannHypothesis
