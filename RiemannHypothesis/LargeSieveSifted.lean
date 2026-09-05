/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieveFarey

/-!
# The large sieve for sifted sets

`RiemannHypothesis.LargeSieveFarey` proves the analytic large sieve at the Farey fractions,

`∑_{q ≤ Q} ∑_{b mod q, (b,q) = 1} ‖∑_{n < N} a n e(n b / q)‖² ≤ (Q² + π N) ∑_{n < N} ‖a n‖²`.

This file draws from it the *sieve* consequence that its open boundary does not claim: a bound for
the size of a set of integers that occupies few residue classes modulo every prime.

## The mechanism

Let `A ⊆ [0, N)` and take `a` to be its indicator, so that the right-hand side is `(Q² + π N)|A|`
and the exponential sum at `b/q` is `S(b/q) = ∑_{n ∈ A} e(n b / q)`.  Orthogonality of the additive
characters modulo `q` gives Parseval's identity

`∑_{b < q} ‖S(b/q)‖² = q ∑_{r < q} (#{n ∈ A : n ≡ r})²`,

whose term `b = 0` is `|A|²`.  If `A` meets at most `w` classes modulo `q`, Cauchy–Schwarz gives
`∑_r (#{n ∈ A : n ≡ r})² ≥ |A|²/w`, so

`∑_{0 < b < q} ‖S(b/q)‖² ≥ |A|² (q − w)/w`.

For a *prime* `q = p` the fractions `b/p` with `0 < b < p` are exactly the reduced ones, so summing
over the primes `p ≤ Q` and comparing with the large sieve gives Montgomery's inequality

`|A| ∑_{p ≤ Q} (p − w p)/(w p) ≤ Q² + π N`.

## Main results

* `sum_e2pi_mul_div` — orthogonality of the additive characters modulo `q`;
* `sum_normSq_indSum` — Parseval's identity for the indicator of `A`;
* `sq_card_le_mul_sum_sq_fiber` — the Cauchy–Schwarz lower bound for the fibre counts;
* `sq_card_mul_le_sum_prime` — the lower bound at a prime modulus;
* `card_le_sifted` — **the large sieve for sifted sets**, in the displayed form above;
* `card_le_sifted_half` — a set meeting at most half the classes modulo every prime `p ≤ Q`
  satisfies `|A| · #{p ≤ Q} ≤ Q² + π N`;
* `card_image_mod_le_of_isSquare`, `card_le_of_isSquare` — the classical example: the squares meet
  at most `(p + 1)/2` classes modulo an odd prime, so the sieve applies to them.

## Scope

Only prime moduli are used.  The full arithmetic large sieve sums over the squarefree `q ≤ Q`,
where the sifting density `∏_{p ∣ q} (p − w p)/(w p)` is multiplicative by the Chinese remainder
theorem; that multiplicative step is *not* formalized here, and without it the sifting function is
a sum over primes rather than over squarefree moduli, which is what an application of Selberg or
Bombieri–Vinogradov strength would need.  The constant `Q² + π N` is inherited, with its factor
`π`, from `M2-LARGE-SIEVE-GALLAGHER`, and is not the sharp `Q² + N − 1`.  For the squares the
resulting bound is weaker than the trivial `√N`; the example is there to show that the hypothesis
of the sieve is satisfied by a natural set, not to improve on counting squares.  Nothing about `ζ`
follows: no mean value theorem is improved, no zero-density estimate is obtained and no zero is
located.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveSifted

open KusminLandau LargeSieve LargeSieveFarey

/-! ## Orthogonality of the additive characters -/

/-- `e(k) = 1` for an integer `k`. -/
theorem e2pi_intCast (k : ℤ) : e2pi (k : ℝ) = 1 := by
  simp only [e2pi]
  rw [show ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
      = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul]
  simp [Complex.exp_two_pi_mul_I]

/-- `e(m/q) = 1` exactly when `q` divides `m`. -/
theorem e2pi_div_eq_one_iff {q : ℕ} (hq : 0 < q) (m : ℤ) :
    e2pi ((m : ℝ) / q) = 1 ↔ (q : ℤ) ∣ m := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · intro h
    rw [e2pi, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hn' : ((2 * Real.pi * ((m : ℝ) / q) : ℝ) : ℂ) * Complex.I
        = ((((n : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have h2 := Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hn')
    have h3 : (2 * Real.pi) * ((m : ℝ) / q) = (2 * Real.pi) * (n : ℝ) := by linarith
    have h4 := mul_left_cancel₀ (by positivity : (0 : ℝ) < 2 * Real.pi).ne' h3
    rw [div_eq_iff hqR.ne'] at h4
    exact ⟨n, by exact_mod_cast h4.trans (mul_comm _ _)⟩
  · rintro ⟨k, rfl⟩
    have h1 : (((q : ℤ) * k : ℤ) : ℝ) / (q : ℝ) = (k : ℝ) := by
      push_cast
      field_simp
    rw [h1]
    exact e2pi_intCast k

/-- **Orthogonality of the additive characters modulo `q`**: the sum of `e(m b / q)` over a
complete residue system `b` is `q` when `q ∣ m` and `0` otherwise. -/
theorem sum_e2pi_mul_div {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∑ b ∈ range q, e2pi ((m : ℝ) * b / q) = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  classical
  have hz : ∀ b : ℕ, e2pi ((m : ℝ) * b / q) = e2pi ((m : ℝ) / q) ^ b := by
    intro b
    rw [show (m : ℝ) * b / q = (b : ℝ) * ((m : ℝ) / q) by ring, e2pi_nat_mul]
  simp only [hz]
  by_cases hdvd : (q : ℤ) ∣ m
  · rw [if_pos hdvd, (e2pi_div_eq_one_iff hq m).2 hdvd]
    simp
  · rw [if_neg hdvd]
    have hne : e2pi ((m : ℝ) / q) ≠ 1 := fun h => hdvd ((e2pi_div_eq_one_iff hq m).1 h)
    have hpow : e2pi ((m : ℝ) / q) ^ q = 1 := by
      rw [← e2pi_nat_mul, show (q : ℝ) * ((m : ℝ) / q) = (m : ℝ) by field_simp]
      exact e2pi_intCast m
    rw [geom_sum_eq hne q, hpow]
    simp

/-! ## Parseval's identity for an indicator -/

/-- The exponential sum of the indicator of `A` at the fraction `b/q`. -/
def indSum (A : Finset ℕ) (q b : ℕ) : ℂ := ∑ n ∈ A, e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))

/-- The number of elements of `A` in the residue class `r` modulo `q`. -/
def fiberCard (A : Finset ℕ) (q r : ℕ) : ℕ := (A.filter (fun n => n % q = r)).card

/-- The term `b = 0`. -/
theorem indSum_zero (A : Finset ℕ) (q : ℕ) : indSum A q 0 = (A.card : ℂ) := by
  simp [indSum, e2pi]

/-- The fibres modulo `q` partition `A`. -/
theorem sum_fiberCard (A : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ r ∈ range q, fiberCard A q r = A.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hq))).symm

/-- **Parseval's identity**: the mean square of the exponential sums of an indicator over the `q`
fractions `b/q` counts the pairs of elements of `A` congruent modulo `q`. -/
theorem sum_normSq_indSum (A : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ b ∈ range q, ‖indSum A q b‖ ^ 2
      = (q : ℝ) * ∑ r ∈ range q, ((fiberCard A q r : ℝ)) ^ 2 := by
  classical
  have hb : ∀ b ∈ range q, ((‖indSum A q b‖ : ℂ)) ^ 2
      = ∑ n ∈ A, ∑ n' ∈ A, e2pi ((((n : ℤ) - (n' : ℤ) : ℤ) : ℝ) * b / q) := by
    intro b _
    have h : ((‖indSum A q b‖ : ℂ)) ^ 2 = indSum A q b * (starRingEnd ℂ) (indSum A q b) := by
      rw [Complex.mul_conj']
    rw [h, indSum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    rw [conj_e2pi, ← e2pi_add]
    congr 1
    push_cast
    ring
  have hswap : ∑ b ∈ range q, ∑ n ∈ A, ∑ n' ∈ A,
        e2pi ((((n : ℤ) - (n' : ℤ) : ℤ) : ℝ) * b / q)
      = ∑ n ∈ A, ∑ n' ∈ A, ∑ b ∈ range q,
        e2pi ((((n : ℤ) - (n' : ℤ) : ℤ) : ℝ) * b / q) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_comm
  have step : ∀ n ∈ A, ∑ n' ∈ A, ∑ b ∈ range q,
      e2pi ((((n : ℤ) - (n' : ℤ) : ℤ) : ℝ) * b / q)
        = (q : ℂ) * (fiberCard A q (n % q) : ℂ) := by
    intro n _
    have hinner : ∀ n' ∈ A, ∑ b ∈ range q, e2pi ((((n : ℤ) - (n' : ℤ) : ℤ) : ℝ) * b / q)
        = if n' % q = n % q then (q : ℂ) else 0 := by
      intro n' _
      rw [sum_e2pi_mul_div hq]
      congr 1
      simp only [eq_iff_iff]
      constructor
      · intro hd
        exact (Nat.modEq_iff_dvd (n := q) (a := n') (b := n)).2 (by exact_mod_cast hd)
      · intro hmod
        exact_mod_cast (Nat.modEq_iff_dvd (n := q) (a := n') (b := n)).1 hmod
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp [fiberCard, mul_comm]
  have hfib : ∑ n ∈ A, (q : ℂ) * (fiberCard A q (n % q) : ℂ)
      = (q : ℂ) * ∑ r ∈ range q, ((fiberCard A q r : ℂ)) ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (t := range q) (g := fun n => n % q)
      (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hq)) (fun n => (fiberCard A q (n % q) : ℂ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hconst : ∀ n ∈ A.filter (fun n => n % q = r), (fiberCard A q (n % q) : ℂ)
        = (fiberCard A q r : ℂ) := by
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    simp [fiberCard, sq]
  have key : ((∑ b ∈ range q, ‖indSum A q b‖ ^ 2 : ℝ) : ℂ)
      = (((q : ℝ) * ∑ r ∈ range q, ((fiberCard A q r : ℝ)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_congr rfl hb, hswap, Finset.sum_congr rfl step, hfib]
  exact_mod_cast key

/-! ## The Cauchy–Schwarz lower bound -/

/-- If `A` meets at most `w` residue classes modulo `q`, then `|A|² ≤ w ∑_r (fibre count)²`. -/
theorem sq_card_le_mul_sum_sq_fiber (A : Finset ℕ) {q w : ℕ} (hq : 0 < q)
    (hw : (A.image (fun n => n % q)).card ≤ w) :
    (A.card : ℝ) ^ 2 ≤ (w : ℝ) * ∑ r ∈ range q, ((fiberCard A q r : ℝ)) ^ 2 := by
  classical
  set R := A.image (fun n => n % q) with hR
  have hRsub : R ⊆ range q := by
    intro r hr
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.2 (Nat.mod_lt _ hq)
  have hzero : ∀ r ∈ range q, r ∉ R → (fiberCard A q r : ℝ) = 0 := by
    intro r _ hrR
    have hempty : A.filter (fun n => n % q = r) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
      obtain ⟨hnA, hnr⟩ := Finset.mem_filter.mp hn
      exact hrR (Finset.mem_image.2 ⟨n, hnA, hnr⟩)
    simp [fiberCard, hempty]
  have hsum : (A.card : ℝ) = ∑ r ∈ R, (fiberCard A q r : ℝ) := by
    have h1 := sum_fiberCard A hq
    have h2 : ∑ r ∈ range q, (fiberCard A q r : ℝ) = (A.card : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h1
    rw [← h2, Finset.sum_subset hRsub fun r hr hrR => hzero r hr hrR]
  have hcs : (∑ r ∈ R, (fiberCard A q r : ℝ)) ^ 2
      ≤ (R.card : ℝ) * ∑ r ∈ R, ((fiberCard A q r : ℝ)) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hRw : (R.card : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hnn : (0 : ℝ) ≤ ∑ r ∈ R, ((fiberCard A q r : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  have hle : ∑ r ∈ R, ((fiberCard A q r : ℝ)) ^ 2 ≤ ∑ r ∈ range q, ((fiberCard A q r : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hRsub fun r _ _ => sq_nonneg _
  calc (A.card : ℝ) ^ 2 = (∑ r ∈ R, (fiberCard A q r : ℝ)) ^ 2 := by rw [hsum]
    _ ≤ (R.card : ℝ) * ∑ r ∈ R, ((fiberCard A q r : ℝ)) ^ 2 := hcs
    _ ≤ (w : ℝ) * ∑ r ∈ range q, ((fiberCard A q r : ℝ)) ^ 2 :=
        mul_le_mul hRw hle hnn (le_trans (Nat.cast_nonneg _) hRw)

/-! ## The lower bound at a prime modulus -/

/-- For a prime `p`, the reduced fractions with denominator `p` are the `b/p` with `0 < b < p`. -/
theorem filter_coprime_prime {p : ℕ} (hp : p.Prime) :
    (range p).filter (fun b => Nat.Coprime b p) = Ico 1 p := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hb, hcop⟩
    refine ⟨?_, hb⟩
    rcases Nat.eq_zero_or_pos b with rfl | h
    · exfalso
      have hg : Nat.gcd 0 p = 1 := hcop
      rw [Nat.gcd_zero_left] at hg
      have := hp.one_lt
      omega
    · exact h
  · rintro ⟨h1, hb⟩
    refine ⟨hb, ?_⟩
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega

/-- **The lower bound at a prime modulus.**  If `A` meets at most `w` classes modulo `p`, the
reduced exponential sums with denominator `p` have mean square at least `|A|²(p − w)/w`. -/
theorem sq_card_mul_le_sum_prime (A : Finset ℕ) {p w : ℕ} (hp : p.Prime) (hw : 0 < w)
    (hAw : (A.image (fun n => n % p)).card ≤ w) :
    (A.card : ℝ) ^ 2 * (((p : ℝ) - w) / w)
      ≤ ∑ b ∈ (range p).filter (fun b => Nat.Coprime b p), ‖indSum A p b‖ ^ 2 := by
  classical
  have hp0 : 0 < p := hp.pos
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  set S : ℝ := ∑ r ∈ range p, ((fiberCard A p r : ℝ)) ^ 2 with hS
  have hpar := sum_normSq_indSum A hp0
  have hsplit : ∑ b ∈ range p, ‖indSum A p b‖ ^ 2
      = ‖indSum A p 0‖ ^ 2 + ∑ b ∈ Ico 1 p, ‖indSum A p b‖ ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp0]
  have hzero : ‖indSum A p 0‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    rw [indSum_zero]
    simp
  have hcs := sq_card_le_mul_sum_sq_fiber A hp0 hAw
  have hIco : ∑ b ∈ Ico 1 p, ‖indSum A p b‖ ^ 2 = (p : ℝ) * S - (A.card : ℝ) ^ 2 := by
    have := hsplit
    rw [hpar, hzero] at this
    linarith [this]
  have hpR : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [filter_coprime_prime hp, hIco, ← mul_div_assoc, div_le_iff₀ hwR]
  nlinarith [mul_le_mul_of_nonneg_left hcs hpR]

/-! ## The sieve -/

/-- The primes at most `Q`. -/
def primesUpTo (Q : ℕ) : Finset ℕ := (range (Q + 1)).filter Nat.Prime

theorem mem_primesUpTo {Q p : ℕ} : p ∈ primesUpTo Q ↔ p ≤ Q ∧ p.Prime := by
  simp [primesUpTo]

/-- **The large sieve for sifted sets.**  If `A ⊆ [0, N)` meets at most `w p` residue classes
modulo every prime `p ≤ Q`, then `|A| ∑_{p ≤ Q} (p − w p)/(w p) ≤ Q² + π N`. -/
theorem card_le_sifted {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N) (w : ℕ → ℕ)
    (hwpos : ∀ p ∈ primesUpTo Q, 0 < w p)
    (hw : ∀ p ∈ primesUpTo Q, (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p)
      ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
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
  have hls := large_sieve_farey_pairs hQ a N
  rw [hnorm] at hls
  have hinner : ∀ q ∈ Icc 1 Q, ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
        = ‖indSum A q b‖ ^ 2 := by
    intro q _ b _
    rw [hsumA]
    rfl
  have hls' : ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      ‖indSum A q b‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := by
    refine le_trans (le_of_eq ?_) hls
    exact (Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun b hb =>
      (hinner q hq b hb).symm)
  have hsub : primesUpTo Q ⊆ Icc 1 Q := by
    intro p hp
    obtain ⟨hpQ, hpp⟩ := mem_primesUpTo.mp hp
    exact Finset.mem_Icc.2 ⟨hpp.one_lt.le, hpQ⟩
  have hnn : ∀ q ∈ Icc 1 Q, q ∉ primesUpTo Q →
      (0 : ℝ) ≤ ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ‖indSum A q b‖ ^ 2 :=
    fun q _ _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hprimes : ∑ p ∈ primesUpTo Q, ∑ b ∈ (range p).filter (fun b => Nat.Coprime b p),
      ‖indSum A p b‖ ^ 2
      ≤ ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        ‖indSum A q b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hlow : (A.card : ℝ) ^ 2 * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p)
      ≤ ∑ p ∈ primesUpTo Q, ∑ b ∈ (range p).filter (fun b => Nat.Coprime b p),
        ‖indSum A p b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    exact sq_card_mul_le_sum_prime A (mem_primesUpTo.mp hp).2 (hwpos p hp) (hw p hp)
  have hmain : (A.card : ℝ) ^ 2 * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := le_trans hlow (le_trans hprimes hls')
  rcases Nat.eq_zero_or_pos A.card with hcard | hcard
  · have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 + Real.pi * N := by positivity
    simp [hcard, hQ0]
  · have hcR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hcard
    have : ((A.card : ℝ) * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p)) * (A.card : ℝ)
        ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := by
      calc ((A.card : ℝ) * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p)) * (A.card : ℝ)
          = (A.card : ℝ) ^ 2 * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) := by ring
        _ ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := hmain
    exact le_of_mul_le_mul_right this hcR

/-- **A set meeting at most half the residue classes modulo every prime `p ≤ Q` is small.** -/
theorem card_le_sifted_half {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (hhalf : ∀ p ∈ primesUpTo Q, 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) * ((primesUpTo Q).card : ℝ) ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
  classical
  set w : ℕ → ℕ := fun p => max 1 ((A.image (fun n => n % p)).card) with hwdef
  have hwpos : ∀ p ∈ primesUpTo Q, 0 < w p :=
    fun p _ => lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
  have hw : ∀ p ∈ primesUpTo Q, (A.image (fun n => n % p)).card ≤ w p :=
    fun p _ => le_max_right _ _
  have hhalf' : ∀ p ∈ primesUpTo Q, 2 * w p ≤ p := by
    intro p hp
    have h2 : 2 ≤ p := (mem_primesUpTo.mp hp).2.two_le
    have := hhalf p hp
    simp only [hwdef]
    rcases max_cases 1 ((A.image (fun n => n % p)).card) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> omega
  have hterm : ∀ p ∈ primesUpTo Q, (1 : ℝ) ≤ ((p : ℝ) - w p) / w p := by
    intro p hp
    have hwp : (0 : ℝ) < (w p : ℝ) := by exact_mod_cast hwpos p hp
    have h2 : (2 : ℝ) * (w p : ℝ) ≤ (p : ℝ) := by exact_mod_cast hhalf' p hp
    rw [le_div_iff₀ hwp]
    linarith
  have hcard : ((primesUpTo Q).card : ℝ) ≤ ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) := by
    calc ((primesUpTo Q).card : ℝ) = ∑ _p ∈ primesUpTo Q, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) := Finset.sum_le_sum hterm
  have hmain := card_le_sifted hQ hA w hwpos hw
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  calc (A.card : ℝ) * ((primesUpTo Q).card : ℝ)
      ≤ (A.card : ℝ) * ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) :=
        mul_le_mul_of_nonneg_left hcard hA0
    _ ≤ (Q : ℝ) ^ 2 + Real.pi * N := hmain

/-! ## The classical example: the squares -/

/-- The squares meet at most `(p + 1)/2` residue classes modulo an odd prime `p`. -/
theorem card_image_mod_le_of_isSquare {A : Finset ℕ} {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hA : ∀ n ∈ A, IsSquare n) :
    (A.image (fun n => n % p)).card ≤ (p + 1) / 2 := by
  classical
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  have hsub : A.image (fun n => n % p) ⊆ (range ((p + 1) / 2)).image (fun x => x * x % p) := by
    intro r hr
    obtain ⟨n, hnA, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨s, hs⟩ := hA n hnA
    obtain ⟨x, hxp, hnx⟩ : ∃ x, x < p ∧ n % p = x * x % p :=
      ⟨s % p, Nat.mod_lt _ hp.pos, by rw [hs, Nat.mul_mod]⟩
    by_cases hle : x < (p + 1) / 2
    · exact Finset.mem_image.2 ⟨x, Finset.mem_range.2 hle, hnx.symm⟩
    · refine Finset.mem_image.2 ⟨p - x, Finset.mem_range.2 (by omega), ?_⟩
      have hmod : (p - x) * (p - x) % p = x * x % p := by
        have hxle : x ≤ p := le_of_lt hxp
        have hz : ((x * x : ℕ) : ℤ) - (((p - x) * (p - x) : ℕ) : ℤ) = (2 * (x : ℤ) - p) * p := by
          have : (((p - x : ℕ)) : ℤ) = (p : ℤ) - (x : ℤ) := by
            push_cast [Nat.cast_sub hxle]
            ring
          rw [Nat.cast_mul, Nat.cast_mul, this]
          ring
        have hdvd : ((p : ℕ) : ℤ) ∣ ((x * x : ℕ) : ℤ) - (((p - x) * (p - x) : ℕ) : ℤ) :=
          ⟨2 * (x : ℤ) - p, by rw [hz]; ring⟩
        exact ((Nat.modEq_iff_dvd (n := p) (a := x * x) (b := (p - x) * (p - x))).2
          (by simpa using hdvd.neg_right)).symm
      rw [← hmod] at hnx
      exact hnx.symm
  calc (A.image (fun n => n % p)).card
      ≤ ((range ((p + 1) / 2)).image (fun x => x * x % p)).card := Finset.card_le_card hsub
    _ ≤ (range ((p + 1) / 2)).card := Finset.card_image_le
    _ = (p + 1) / 2 := Finset.card_range _

/-- **The sieve applied to a set of squares.**  For `A ⊆ [0, N)` consisting of squares,
`|A| · #{odd primes p ≤ Q} ≤ 3 (Q² + π N)`. -/
theorem card_le_of_isSquare {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (hsq : ∀ n ∈ A, IsSquare n) :
    (A.card : ℝ) * (((primesUpTo Q).erase 2).card : ℝ)
      ≤ 3 * ((Q : ℝ) ^ 2 + Real.pi * N) := by
  classical
  set w : ℕ → ℕ := fun p => if p = 2 then 2 else (p + 1) / 2 with hwdef
  have hwpos : ∀ p ∈ primesUpTo Q, 0 < w p := by
    intro p hp
    have h2 := (mem_primesUpTo.mp hp).2.two_le
    simp only [hwdef]
    split <;> omega
  have hw : ∀ p ∈ primesUpTo Q, (A.image (fun n => n % p)).card ≤ w p := by
    intro p hp
    obtain ⟨hpQ, hpp⟩ := mem_primesUpTo.mp hp
    by_cases h2 : p = 2
    · subst h2
      simp only [hwdef, if_pos rfl]
      have : A.image (fun n => n % 2) ⊆ range 2 := by
        intro r hr
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hr
        exact Finset.mem_range.2 (Nat.mod_lt _ (by norm_num))
      calc (A.image (fun n => n % 2)).card ≤ (range 2).card := Finset.card_le_card this
        _ = 2 := Finset.card_range 2
    · simp only [hwdef, if_neg h2]
      exact card_image_mod_le_of_isSquare hpp h2 hsq
  have hmain := card_le_sifted hQ hA w hwpos hw
  have hterm : ∀ p ∈ (primesUpTo Q).erase 2, (1 / 3 : ℝ) ≤ ((p : ℝ) - w p) / w p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpQ, hpp⟩ := mem_primesUpTo.mp hmem
    have hp2 : 2 < p := lt_of_le_of_ne hpp.two_le (Ne.symm hne)
    have hodd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hpp with h | h
      · omega
      · exact h
    have hwval : (w p : ℝ) = ((p : ℝ) + 1) / 2 := by
      simp only [hwdef, if_neg hne]
      have : (p + 1) / 2 * 2 = p + 1 := by omega
      have h2 : ((((p + 1) / 2 : ℕ) : ℝ)) * 2 = (p : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hwpos' : (0 : ℝ) < (w p : ℝ) := by
      rw [hwval]
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      linarith
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    rw [le_div_iff₀ hwpos', hwval]
    linarith
  have hnn : ∀ p ∈ primesUpTo Q, p ∉ (primesUpTo Q).erase 2 →
      (0 : ℝ) ≤ ((p : ℝ) - w p) / w p := by
    intro p hp hp2
    have hpe : p = 2 := by
      by_contra hne
      exact hp2 (Finset.mem_erase.2 ⟨hne, hp⟩)
    subst hpe
    simp [hwdef]
  have hsum : ((((primesUpTo Q).erase 2).card : ℝ)) / 3
      ≤ ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) := by
    have hsub : (primesUpTo Q).erase 2 ⊆ primesUpTo Q := Finset.erase_subset _ _
    have hle : ∑ p ∈ (primesUpTo Q).erase 2, (1 / 3 : ℝ)
        ≤ ∑ p ∈ (primesUpTo Q).erase 2, (((p : ℝ) - w p) / w p) := Finset.sum_le_sum hterm
    have hext : ∑ p ∈ (primesUpTo Q).erase 2, (((p : ℝ) - w p) / w p)
        ≤ ∑ p ∈ primesUpTo Q, (((p : ℝ) - w p) / w p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hconst : ∑ _p ∈ (primesUpTo Q).erase 2, (1 / 3 : ℝ)
        = ((((primesUpTo Q).erase 2).card : ℝ)) / 3 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [hconst ▸ hle, hext]
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hsum hA0
  have hfin : (A.card : ℝ) * ((((primesUpTo Q).erase 2).card : ℝ) / 3)
      ≤ (Q : ℝ) ^ 2 + Real.pi * N := le_trans this hmain
  linarith [hfin]

/-- The same bound for the set of *all* squares below `N`, with no hypothesis left to the
caller. -/
theorem card_squares_lt_le {N Q : ℕ} (hQ : 2 ≤ Q) :
    ((((range N).filter (fun n => IsSquare n)).card : ℝ)) * (((primesUpTo Q).erase 2).card : ℝ)
      ≤ 3 * ((Q : ℝ) ^ 2 + Real.pi * N) := by
  classical
  refine card_le_of_isSquare hQ (Finset.filter_subset _ _) fun n hn => ?_
  exact (Finset.mem_filter.mp hn).2

end LargeSieveSifted

end RiemannHypothesis
