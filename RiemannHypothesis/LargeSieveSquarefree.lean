/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieveSifted

/-!
# The large sieve for sifted sets, over squarefree moduli

`RiemannHypothesis.LargeSieveSifted` proves the sieve consequence of the large sieve for *prime*
moduli only: if `A ⊆ [0, N)` meets at most `w p` residue classes modulo every prime `p ≤ Q`, then

`|A| ∑_{p ≤ Q} (p − w p)/(w p) ≤ Q² + π N`.

Its open boundary records what is missing: the sifting density is multiplicative, so the classical
statement — Montgomery's sieve — sums over all *squarefree* `q ≤ Q` the product
`∏_{p ∣ q} (p − w p)/(w p)`, which is enormously larger than the sum over primes alone (for a set
missing half the classes modulo every prime, the sum over primes is `π(Q)` while the sum over
squarefree moduli is at least the number of squarefree integers up to `Q`, which is `≫ Q`).

This file proves that statement.

## The mechanism

Write `S(x) = ∑_{n ∈ A} e(n x)` and, for a modulus `q`,
`F(q) = ∑_{b mod q, (b,q) = 1} ‖S(b/q)‖²`.  The large sieve at the Farey fractions bounds
`∑_{q ≤ Q} F(q)` by `(Q² + π N)|A|`, so everything is a lower bound for `F(q)`.

The lower bound is multiplicative, and is proved by induction on the number of prime factors of a
squarefree `q`.  For `q = p m` with `p` prime and `p ∤ m`, the numbers
`b = (c m + d p) mod p m` with `0 < c < p` and `d` reduced mod `m` are distinct reduced residues
mod `q`, and `b/q ≡ c/p + d/m (mod 1)`.  For a fixed `d`, group `A` by its residue mod `p`:

`S(c/p + d/m) = ∑_{r < p} g(r) e(r c/p)`,  `g(r) = ∑_{n ∈ A, n ≡ r (p)} e(n d/m)`,

so `S(c/p + d/m)` is the discrete Fourier transform of `g` at `c`, and `g` is supported on the
`w p` classes that `A` meets modulo `p`.  Parseval and Cauchy–Schwarz then give, exactly as in the
prime case but now for a complex-valued `g`,

`∑_{0 < c < p} ‖ĝ(c)‖² ≥ ((p − w p)/(w p)) ‖ĝ(0)‖² = ((p − w p)/(w p)) ‖S(d/m)‖²`,

whence `F(p m) ≥ ((p − w p)/(w p)) F(m)`, and the induction closes.

## Main results

* `sum_normSq_dft` — Parseval's identity for the discrete Fourier transform of an arbitrary
  complex-valued function on `ℤ/q`;
* `sq_norm_expSum_mul_le_sum_prime` — the prime step: `‖S(x)‖² (p − w)/w ≤ ∑_{0<c<p} ‖S(c/p+x)‖²`;
* `redSq_prime_mul_le` — multiplicativity: `((p − w p)/(w p)) F(m) ≤ F(p m)` for `p ∤ m`;
* `sq_card_mul_prod_le_redSq` — `F(q) ≥ |A|² ∏_{p ∣ q} (p − w p)/(w p)` for squarefree `q`;
* `card_le_sifted_squarefree` — **Montgomery's sieve**:
  `|A| ∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/(w p) ≤ Q² + π N`;
* `card_le_sifted_squarefree_half` — a set meeting at most half the classes modulo every prime
  `p ≤ Q` satisfies `|A| · #{q ≤ Q squarefree} ≤ Q² + π N`;
* `card_squarefreeUpTo_ge` — at least a quarter of the moduli up to `Q` are squarefree;
* `card_le_of_sifted_half_sqrt` — the consequence that prime moduli alone do not give: a set
  below `N` meeting at most half the classes modulo every prime `p ≤ √N` has at most `34 √N`
  elements.

## Scope

The constant `Q² + π N` is inherited, with its factor `π`, from `M2-LARGE-SIEVE-GALLAGHER`, and is
not the sharp `Q² + N − 1`; the constant `34` in the `√N` bound is correspondingly generous.
Nothing beyond squarefree moduli is proved: the sifting density at a prime power is not treated,
because the large sieve is applied only at reduced fractions and the inductive step uses `p ∤ m`.
No Selberg-type optimization of the sifting weights and no Bombieri–Vinogradov consequence is
drawn, and nothing about `ζ` follows.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveSquarefree

open KusminLandau LargeSieve LargeSieveFarey LargeSieveSifted

/-- The exponential sum of the indicator of `A` at a real point. -/
def expSum (A : Finset ℕ) (x : ℝ) : ℂ := ∑ n ∈ A, e2pi ((n : ℝ) * x)

/-- The mean square of the exponential sums of the indicator of `A` over the reduced fractions
with denominator `q`. -/
def redSq (A : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ‖indSum A q b‖ ^ 2

/-- The part of the exponential sum coming from one residue class modulo `p`. -/
def fiberSum (A : Finset ℕ) (p : ℕ) (x : ℝ) (r : ℕ) : ℂ :=
  ∑ n ∈ A.filter (fun n => n % p = r), e2pi ((n : ℝ) * x)

theorem indSum_eq_expSum (A : Finset ℕ) (q b : ℕ) :
    indSum A q b = expSum A ((b : ℝ) / q) := rfl

theorem expSum_zero (A : Finset ℕ) : expSum A 0 = (A.card : ℂ) := by
  simp [expSum, e2pi]

/-- `e(θ + m) = e(θ)` for a natural number `m`. -/
theorem e2pi_add_nat (θ : ℝ) (m : ℕ) : e2pi (θ + m) = e2pi θ := by
  simpa using (e2pi_sub_int (θ + m) (m : ℤ)).symm

/-- `e(θ − m) = e(θ)` for a natural number `m`. -/
theorem e2pi_sub_nat (θ : ℝ) (m : ℕ) : e2pi (θ - m) = e2pi θ := by
  simpa using e2pi_sub_int θ (m : ℤ)

/-! ## Parseval's identity for the discrete Fourier transform -/

/-- **Parseval's identity** for an arbitrary complex-valued function on the residues mod `q`. -/
theorem sum_normSq_dft {q : ℕ} (hq : 0 < q) (g : ℕ → ℂ) :
    ∑ c ∈ range q, ‖∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q)‖ ^ 2
      = (q : ℝ) * ∑ r ∈ range q, ‖g r‖ ^ 2 := by
  classical
  have hexp : ∀ c ∈ range q, ((‖∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q)‖ : ℝ) : ℂ) ^ 2
      = ∑ r ∈ range q, ∑ r' ∈ range q,
          g r * (starRingEnd ℂ) (g r') * e2pi ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * c / q) := by
    intro c _
    have h : ((‖∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q)‖ : ℝ) : ℂ) ^ 2
        = (∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q))
          * (starRingEnd ℂ) (∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q)) := by
      rw [Complex.mul_conj']
    rw [h, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [map_mul, conj_e2pi]
    rw [show g r * e2pi ((r : ℝ) * c / q) * ((starRingEnd ℂ) (g r') * e2pi (-((r' : ℝ) * c / q)))
        = g r * (starRingEnd ℂ) (g r')
          * (e2pi ((r : ℝ) * c / q) * e2pi (-((r' : ℝ) * c / q))) by ring, ← e2pi_add]
    congr 2
    push_cast
    ring
  have hswap : ∑ c ∈ range q, ∑ r ∈ range q, ∑ r' ∈ range q,
        g r * (starRingEnd ℂ) (g r') * e2pi ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * c / q)
      = ∑ r ∈ range q, ∑ r' ∈ range q, ∑ c ∈ range q,
        g r * (starRingEnd ℂ) (g r') * e2pi ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * c / q) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hinner : ∀ r ∈ range q, ∀ r' ∈ range q,
      ∑ c ∈ range q, g r * (starRingEnd ℂ) (g r')
          * e2pi ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * c / q)
        = if r' = r then g r * (starRingEnd ℂ) (g r') * q else 0 := by
    intro r hr r' hr'
    rw [← Finset.mul_sum, sum_e2pi_mul_div hq]
    have hiff : ((q : ℤ) ∣ ((r : ℤ) - (r' : ℤ))) ↔ r' = r := by
      constructor
      · intro hd
        have hmod : r' ≡ r [MOD q] :=
          (Nat.modEq_iff_dvd (n := q) (a := r') (b := r)).2 (by exact_mod_cast hd)
        have h1 := Finset.mem_range.mp hr
        have h2 := Finset.mem_range.mp hr'
        simpa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using hmod
      · rintro rfl
        simp
    by_cases hrr : r' = r
    · rw [if_pos (hiff.2 hrr), if_pos hrr]
    · rw [if_neg (fun hd => hrr (hiff.1 hd)), if_neg hrr, mul_zero]
  have hdiag : ∑ r ∈ range q, ∑ r' ∈ range q,
        (if r' = r then g r * (starRingEnd ℂ) (g r') * q else 0)
      = ∑ r ∈ range q, ((‖g r‖ : ℝ) : ℂ) ^ 2 * q := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_ite_eq' (range q) r (fun r' => g r * (starRingEnd ℂ) (g r') * q), if_pos hr,
      Complex.mul_conj']
  have key : ((∑ c ∈ range q, ‖∑ r ∈ range q, g r * e2pi ((r : ℝ) * c / q)‖ ^ 2 : ℝ) : ℂ)
      = (((q : ℝ) * ∑ r ∈ range q, ‖g r‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_congr rfl hexp, hswap,
      Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun r' hr' => hinner r hr r' hr')),
      hdiag, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  exact_mod_cast key

/-! ## The prime step -/

/-- Splitting `A` into its residue classes mod `p` writes the exponential sum at `c/p + x` as the
discrete Fourier transform, at `c`, of the fibre sums. -/
theorem expSum_add_div_eq (A : Finset ℕ) {p : ℕ} (hp : 0 < p) (c : ℕ) (x : ℝ) :
    expSum A ((c : ℝ) / p + x) = ∑ r ∈ range p, fiberSum A p x r * e2pi ((r : ℝ) * c / p) := by
  classical
  rw [expSum, ← Finset.sum_fiberwise_of_maps_to (t := range p) (g := fun n => n % p)
    (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hp))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [fiberSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hr : n % p = r := (Finset.mem_filter.mp hn).2
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = p * k + r :=
    ⟨n / p, by rw [← hr]; exact (Nat.div_add_mod n p).symm⟩
  have hsplit : (n : ℝ) * ((c : ℝ) / p + x)
      = ((r : ℝ) * c / p + (n : ℝ) * x) + ((k * c : ℕ) : ℝ) := by
    have hnR : (n : ℝ) = (p : ℝ) * (k : ℝ) + (r : ℝ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hk
    push_cast
    rw [hnR]
    field_simp
    ring
  rw [hsplit, e2pi_add_nat, e2pi_add, mul_comm]

/-- The fibre sums add up to the whole exponential sum. -/
theorem sum_fiberSum (A : Finset ℕ) {p : ℕ} (hp : 0 < p) (x : ℝ) :
    ∑ r ∈ range p, fiberSum A p x r = expSum A x := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to (s := A) (t := range p) (g := fun n => n % p)
    (f := fun n => e2pi ((n : ℝ) * x)) (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hp))
  simpa [fiberSum, expSum] using h

/-- A fibre sum vanishes on a class that `A` does not meet. -/
theorem fiberSum_eq_zero (A : Finset ℕ) {p : ℕ} (x : ℝ) {r : ℕ}
    (hr : r ∉ A.image (fun n => n % p)) : fiberSum A p x r = 0 := by
  classical
  have hempty : A.filter (fun n => n % p = r) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
    obtain ⟨hnA, hnr⟩ := Finset.mem_filter.mp hn
    exact hr (Finset.mem_image.2 ⟨n, hnA, hnr⟩)
  simp [fiberSum, hempty]

/-- **The prime step.**  If `A` meets at most `w` classes modulo the prime `p`, then shifting the
argument by the `p − 1` nonzero fractions `c/p` recovers `‖S(x)‖² (p − w)/w`. -/
theorem sq_norm_expSum_mul_le_sum_prime (A : Finset ℕ) {p w : ℕ} (hp : p.Prime) (hw : 0 < w)
    (hAw : (A.image (fun n => n % p)).card ≤ w) (x : ℝ) :
    ‖expSum A x‖ ^ 2 * (((p : ℝ) - w) / w)
      ≤ ∑ c ∈ Ico 1 p, ‖expSum A ((c : ℝ) / p + x)‖ ^ 2 := by
  classical
  have hp0 : 0 < p := hp.pos
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  set g : ℕ → ℂ := fiberSum A p x with hg
  set R := A.image (fun n => n % p) with hR
  have hRsub : R ⊆ range p := by
    intro r hr
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.2 (Nat.mod_lt _ hp0)
  have hSum : ∑ r ∈ range p, g r = expSum A x := sum_fiberSum A hp0 x
  have hSumR : expSum A x = ∑ r ∈ R, g r := by
    rw [← hSum, Finset.sum_subset hRsub fun r _ hrR => fiberSum_eq_zero A x hrR]
  set T : ℝ := ∑ r ∈ range p, ‖g r‖ ^ 2 with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hpar : ∑ c ∈ range p, ‖expSum A ((c : ℝ) / p + x)‖ ^ 2 = (p : ℝ) * T := by
    rw [← sum_normSq_dft hp0 g]
    exact Finset.sum_congr rfl fun c _ => by rw [expSum_add_div_eq A hp0 c x]
  have hsplit : ∑ c ∈ range p, ‖expSum A ((c : ℝ) / p + x)‖ ^ 2
      = ‖expSum A x‖ ^ 2 + ∑ c ∈ Ico 1 p, ‖expSum A ((c : ℝ) / p + x)‖ ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp0]
    norm_num
  have hcs : ‖expSum A x‖ ^ 2 ≤ (w : ℝ) * T := by
    have hnormle : ‖expSum A x‖ ≤ ∑ r ∈ R, ‖g r‖ := by
      rw [hSumR]
      exact norm_sum_le _ _
    have hsq : ‖expSum A x‖ ^ 2 ≤ (∑ r ∈ R, ‖g r‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnormle 2
    have hCS : (∑ r ∈ R, ‖g r‖) ^ 2 ≤ (R.card : ℝ) * ∑ r ∈ R, ‖g r‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hRw : (R.card : ℝ) ≤ (w : ℝ) := by exact_mod_cast hAw
    have hsub : ∑ r ∈ R, ‖g r‖ ^ 2 ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hRsub fun _ _ _ => sq_nonneg _
    have hRnn : (0 : ℝ) ≤ ∑ r ∈ R, ‖g r‖ ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
    calc ‖expSum A x‖ ^ 2 ≤ (∑ r ∈ R, ‖g r‖) ^ 2 := hsq
      _ ≤ (R.card : ℝ) * ∑ r ∈ R, ‖g r‖ ^ 2 := hCS
      _ ≤ (w : ℝ) * T := mul_le_mul hRw hsub hRnn (le_trans (Nat.cast_nonneg _) hRw)
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← mul_div_assoc, div_le_iff₀ hwR]
  nlinarith [mul_le_mul_of_nonneg_left hcs hpnn, hpar, hsplit]

/-! ## Multiplicativity of the lower bound -/

/-- The reduced fractions with denominator `p m`, `p` prime not dividing `m`, contain the
fractions `c/p + d/m` with `0 < c < p` and `d` reduced modulo `m`. -/
theorem redSq_prime_mul_le (A : Finset ℕ) {p m w : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬ p ∣ m) (hw : 0 < w) (hAw : (A.image (fun n => n % p)).card ≤ w) :
    (((p : ℝ) - w) / w) * redSq A m ≤ redSq A (p * m) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < p * m := Nat.mul_pos hp0 hm
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  set D := (range m).filter (fun d => Nat.Coprime d m) with hD
  set S := (Ico 1 p) ×ˢ D with hS
  set ι : ℕ × ℕ → ℕ := fun z => (z.1 * m + z.2 * p) % (p * m) with hι
  have hmodp : ∀ z : ℕ × ℕ, ι z % p = (z.1 * m) % p := by
    intro z
    rw [hι, Nat.mod_mod_of_dvd _ (dvd_mul_right p m), Nat.add_mul_mod_self_right]
  have hmodm : ∀ z : ℕ × ℕ, ι z % m = (z.2 * p) % m := by
    intro z
    rw [hι, Nat.mod_mod_of_dvd _ (dvd_mul_left m p), add_comm, Nat.add_mul_mod_self_right]
  have hmaps : ∀ z ∈ S, ι z ∈ (range (p * m)).filter (fun b => Nat.Coprime b (p * m)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    obtain ⟨hc1, hcp⟩ := Finset.mem_Ico.mp hz1
    obtain ⟨_, hdm⟩ := Finset.mem_filter.mp hz2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq0), ?_⟩
    have hcp' : Nat.Coprime (ι z) p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      have hdvd' : p ∣ z.1 * m := by
        have h1 : p ∣ z.1 * m + z.2 * p := (Nat.dvd_mod_iff (dvd_mul_right p m)).1 hdvd
        have h2 : p ∣ z.2 * p := dvd_mul_left p z.2
        simpa using Nat.dvd_sub h1 h2
      rcases (Nat.Prime.dvd_mul hp).1 hdvd' with h | h
      · have := Nat.le_of_dvd (by omega) h
        omega
      · exact hpm h
    have hcm' : Nat.Coprime (ι z) m := by
      have h1 : Nat.Coprime (z.2 * p) m := Nat.Coprime.mul_left hdm hcop
      have h2 : Nat.Coprime (ι z % m) m := by
        rw [hmodm z]; exact (ZMod.coprime_mod_iff_coprime _ _).2 h1
      exact (ZMod.coprime_mod_iff_coprime _ _).1 h2
    exact Nat.Coprime.mul_right hcp' hcm'
  have hinj : ∀ z ∈ S, ∀ z' ∈ S, ι z = ι z' → z = z' := by
    intro z hz z' hz' heq
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    obtain ⟨hz1', hz2'⟩ := Finset.mem_product.mp hz'
    obtain ⟨_, hcp⟩ := Finset.mem_Ico.mp hz1
    obtain ⟨_, hcp'⟩ := Finset.mem_Ico.mp hz1'
    have hdm := Finset.mem_range.mp (Finset.mem_filter.mp hz2).1
    have hdm' := Finset.mem_range.mp (Finset.mem_filter.mp hz2').1
    have h1 : z.1 = z'.1 := by
      have hmod : z.1 * m ≡ z'.1 * m [MOD p] := by
        have h := congrArg (fun t => t % p) heq
        simp only [hmodp] at h
        exact h
      have := Nat.ModEq.cancel_right_of_coprime (m := p) (by simpa [Nat.Coprime] using hcop) hmod
      have h2 : z.1 % p = z'.1 % p := this
      rwa [Nat.mod_eq_of_lt hcp, Nat.mod_eq_of_lt hcp'] at h2
    have h2 : z.2 = z'.2 := by
      have hmod : z.2 * p ≡ z'.2 * p [MOD m] := by
        have h := congrArg (fun t => t % m) heq
        simp only [hmodm] at h
        exact h
      have := Nat.ModEq.cancel_right_of_coprime (m := m)
        (by simpa [Nat.Coprime] using Nat.Coprime.symm hcop) hmod
      have h3 : z.2 % m = z'.2 % m := this
      rwa [Nat.mod_eq_of_lt hdm, Nat.mod_eq_of_lt hdm'] at h3
    exact Prod.ext h1 h2
  have hval : ∀ z : ℕ × ℕ, indSum A (p * m) (ι z)
      = expSum A ((z.1 : ℝ) / p + (z.2 : ℝ) / m) := by
    intro z
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    set k := (z.1 * m + z.2 * p) / (p * m) with hk
    have hnat : (p * m) * k + ι z = z.1 * m + z.2 * p := Nat.div_add_mod _ _
    have hbR : ((ι z : ℕ) : ℝ) / ((p : ℝ) * m)
        = (z.1 : ℝ) / p + (z.2 : ℝ) / m - (k : ℝ) := by
      have hcast : ((p : ℝ) * m) * (k : ℝ) + ((ι z : ℕ) : ℝ)
          = (z.1 : ℝ) * m + (z.2 : ℝ) * p := by exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hnat
      field_simp
      nlinarith [hcast]
    rw [indSum_eq_expSum, expSum, expSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have harg : (n : ℝ) * ((ι z : ℕ) : ℝ) / ((p * m : ℕ) : ℝ)
        = (n : ℝ) * ((z.1 : ℝ) / p + (z.2 : ℝ) / m) - ((n * k : ℕ) : ℝ) := by
      push_cast
      field_simp at hbR ⊢
      nlinarith [hbR]
    rw [show (n : ℝ) * (((ι z : ℕ) : ℝ) / ((p * m : ℕ) : ℝ))
        = (n : ℝ) * ((ι z : ℕ) : ℝ) / ((p * m : ℕ) : ℝ) by ring, harg, e2pi_sub_nat]
  have himg : S.image ι ⊆ (range (p * m)).filter (fun b => Nat.Coprime b (p * m)) := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps z hz
  have h1 : ∑ b ∈ S.image ι, ‖indSum A (p * m) b‖ ^ 2 ≤ redSq A (p * m) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => sq_nonneg _
  have h2 : ∑ b ∈ S.image ι, ‖indSum A (p * m) b‖ ^ 2
      = ∑ z ∈ S, ‖indSum A (p * m) (ι z)‖ ^ 2 := Finset.sum_image hinj
  have h3 : ∑ z ∈ S, ‖indSum A (p * m) (ι z)‖ ^ 2
      = ∑ d ∈ D, ∑ c ∈ Ico 1 p, ‖expSum A ((c : ℝ) / p + (d : ℝ) / m)‖ ^ 2 := by
    rw [hS, Finset.sum_product]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [hval (c, d)]
  have h4 : (((p : ℝ) - w) / w) * redSq A m
      ≤ ∑ d ∈ D, ∑ c ∈ Ico 1 p, ‖expSum A ((c : ℝ) / p + (d : ℝ) / m)‖ ^ 2 := by
    rw [redSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have := sq_norm_expSum_mul_le_sum_prime A hp hw hAw ((d : ℝ) / m)
    rw [indSum_eq_expSum]
    linarith [this]
  linarith [h1, h2 ▸ h3 ▸ h4]

theorem redSq_one (A : Finset ℕ) : redSq A 1 = (A.card : ℝ) ^ 2 := by
  classical
  rw [redSq]
  have h : (range 1).filter (fun b => Nat.Coprime b 1) = {0} := by decide
  rw [h, Finset.sum_singleton, indSum_zero]
  simp

/-- **The multiplicative lower bound.**  For squarefree `q`, the reduced mean square at
denominator `q` is at least `|A|²` times the sifting density `∏_{p ∣ q} (p − w p)/(w p)`. -/
theorem sq_card_mul_prod_le_redSq (A : Finset ℕ) (w : ℕ → ℕ) {q : ℕ} (hq : Squarefree q)
    (hwpos : ∀ p ∈ q.primeFactors, 0 < w p) (hwle : ∀ p ∈ q.primeFactors, w p ≤ p)
    (hAw : ∀ p ∈ q.primeFactors, (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) ≤ redSq A q := by
  classical
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    have hq0 : q ≠ 0 := hq.ne_zero
    by_cases hq1 : q = 1
    · subst hq1
      simp [redSq_one]
    · set p := q.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime hq1
      have hpdvd : p ∣ q := Nat.minFac_dvd q
      set m := q / p with hmdef
      have hqm : q = p * m := (Nat.mul_div_cancel' hpdvd).symm
      have hm0 : m ≠ 0 := by
        intro h
        rw [h, Nat.mul_zero] at hqm
        exact hq0 hqm
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hpm : ¬ p ∣ m := by
        intro hd
        obtain ⟨k, hk⟩ := hd
        have hpp : p * p ∣ q := ⟨k, by rw [hqm, hk]; ring⟩
        have hu := hq p hpp
        rw [Nat.isUnit_iff] at hu
        exact hp.one_lt.ne' hu
      have hmsf : Squarefree m := hq.squarefree_of_dvd ⟨p, by rw [hqm]; ring⟩
      have hmlt : m < q := by
        have h1 : 1 < p := hp.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < p * m := by exact Nat.mul_lt_mul_of_lt_of_le h1 le_rfl hmpos
          _ = q := hqm.symm
      have hfac : q.primeFactors = insert p m.primeFactors := by
        rw [hqm, Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors]
        rfl
      have hpnotmem : p ∉ m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)
      have hsub : m.primeFactors ⊆ q.primeFactors := by
        rw [hfac]; exact Finset.subset_insert _ _
      have hpmem : p ∈ q.primeFactors := by rw [hfac]; exact Finset.mem_insert_self _ _
      have hIH := IH m hmlt hmsf (fun r hr => hwpos r (hsub hr)) (fun r hr => hwle r (hsub hr))
        (fun r hr => hAw r (hsub hr))
      have hwp : (0 : ℝ) < (w p : ℝ) := by exact_mod_cast hwpos p hpmem
      have hwlep : (w p : ℝ) ≤ (p : ℝ) := by exact_mod_cast hwle p hpmem
      have hfnn : (0 : ℝ) ≤ ((p : ℝ) - w p) / w p := div_nonneg (by linarith) hwp.le
      have hstep := redSq_prime_mul_le A hp hmpos hpm (hwpos p hpmem) (hAw p hpmem)
      calc (A.card : ℝ) ^ 2 * ∏ r ∈ q.primeFactors, (((r : ℝ) - w r) / w r)
          = (((p : ℝ) - w p) / w p)
              * ((A.card : ℝ) ^ 2 * ∏ r ∈ m.primeFactors, (((r : ℝ) - w r) / w r)) := by
            rw [hfac, Finset.prod_insert hpnotmem]; ring
        _ ≤ (((p : ℝ) - w p) / w p) * redSq A m := by
            exact mul_le_mul_of_nonneg_left hIH hfnn
        _ ≤ redSq A (p * m) := hstep
        _ = redSq A q := by rw [← hqm]

/-! ## The sieve -/

/-- The squarefree numbers in `[1, Q]`. -/
def squarefreeUpTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Squarefree

theorem mem_squarefreeUpTo {Q q : ℕ} : q ∈ squarefreeUpTo Q ↔ (1 ≤ q ∧ q ≤ Q) ∧ Squarefree q := by
  simp [squarefreeUpTo, Finset.mem_Icc, and_assoc]

/-- **Montgomery's sieve.**  If `A ⊆ [0, N)` meets at most `w p` residue classes modulo every
prime `p ≤ Q`, then `|A| ∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/(w p) ≤ Q² + π N`. -/
theorem card_le_sifted_squarefree {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (w : ℕ → ℕ) (hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p) (hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p)
    (hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
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
  have hls' : ∑ q ∈ Icc 1 Q, redSq A q ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := by
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
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) :=
    le_trans hlow (le_trans hrestrict hls')
  rcases Nat.eq_zero_or_pos A.card with hcard | hcard
  · have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 + Real.pi * N := by positivity
    simp [hcard, hQ0]
  · have hcR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hcard
    refine le_of_mul_le_mul_right ?_ hcR
    calc ((A.card : ℝ)
            * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p))
          * (A.card : ℝ)
        = (A.card : ℝ) ^ 2
            * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) := by ring
      _ ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (A.card : ℝ) := hmain

/-- **A set meeting at most half the residue classes modulo every prime `p ≤ Q` is small**, now
with the count of *all* squarefree moduli up to `Q` in place of the count of primes. -/
theorem card_le_sifted_squarefree_half {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (hhalf : ∀ p, p.Prime → p ≤ Q → 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) * ((squarefreeUpTo Q).card : ℝ) ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
  classical
  set w : ℕ → ℕ := fun p => max 1 ((A.image (fun n => n % p)).card) with hwdef
  have hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p :=
    fun p _ _ => lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
  have hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p :=
    fun p _ _ => le_max_right _ _
  have htwo : ∀ p, p.Prime → p ≤ Q → 2 * w p ≤ p := by
    intro p hp hpQ
    have h2 : 2 ≤ p := hp.two_le
    have := hhalf p hp hpQ
    simp only [hwdef]
    rcases max_cases 1 ((A.image (fun n => n % p)).card) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> omega
  have hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p := by
    intro p hp hpQ
    have := htwo p hp hpQ
    omega
  have hterm : ∀ p, p.Prime → p ≤ Q → (1 : ℝ) ≤ ((p : ℝ) - w p) / w p := by
    intro p hp hpQ
    have hwp : (0 : ℝ) < (w p : ℝ) := by exact_mod_cast hwpos p hp hpQ
    have h2 : (2 : ℝ) * (w p : ℝ) ≤ (p : ℝ) := by exact_mod_cast htwo p hp hpQ
    rw [le_div_iff₀ hwp]
    linarith
  have hprod : ∀ q ∈ squarefreeUpTo Q,
      (1 : ℝ) ≤ ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) := by
    intro q hq
    obtain ⟨⟨h1, h2⟩, _⟩ := mem_squarefreeUpTo.mp hq
    refine Finset.one_le_prod fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    exact hterm p hpp (le_trans (Nat.le_of_dvd (by omega) hpd) h2)
  have hcard : ((squarefreeUpTo Q).card : ℝ)
      ≤ ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) := by
    calc ((squarefreeUpTo Q).card : ℝ) = ∑ _q ∈ squarefreeUpTo Q, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) :=
          Finset.sum_le_sum hprod
  have hmain := card_le_sifted_squarefree hQ hA w hwpos hwle hAw
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  calc (A.card : ℝ) * ((squarefreeUpTo Q).card : ℝ)
      ≤ (A.card : ℝ) * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p) :=
        mul_le_mul_of_nonneg_left hcard hA0
    _ ≤ (Q : ℝ) ^ 2 + Real.pi * N := hmain

/-! ## Counting the squarefree moduli

The sifting sum over squarefree moduli is at least the *number* of squarefree `q ≤ Q`, and that
number is `≫ Q`; the sieve therefore gives `|A| ≪ √N` for a set that misses half the classes
modulo every prime `p ≤ √N`, in place of the `N / log N` that prime moduli alone give. -/

/-- The multiples of `d²` in `[1, Q]` number at most `Q / d²`. -/
theorem card_filter_sq_dvd_le (Q d : ℕ) :
    ((Icc 1 Q).filter (fun q => d ^ 2 ∣ q)).card ≤ Q / d ^ 2 := by
  classical
  have hcard : (Icc 1 (Q / d ^ 2)).card = Q / d ^ 2 := by
    rw [Nat.card_Icc]
    generalize Q / d ^ 2 = k
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun q => q / d ^ 2) ?_ ?_
  · intro q hq
    obtain ⟨hq1, hdvd⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hq1
    have hd : 0 < d ^ 2 := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have hq0 : q = 0 := by simpa using hdvd
        omega
      · positivity
    refine Finset.mem_Icc.2 ⟨?_, Nat.div_le_div_right h2⟩
    exact Nat.one_le_div_iff hd |>.2 (Nat.le_of_dvd (by omega) hdvd)
  · intro q hq q' hq' heq
    obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hdvd'⟩ := Finset.mem_filter.mp hq'
    have heq' : q / d ^ 2 = q' / d ^ 2 := heq
    rw [← Nat.div_mul_cancel hdvd, ← Nat.div_mul_cancel hdvd', heq']

/-- Every non-squarefree `q ∈ [1, Q]` is divisible by the square of some `d ∈ [2, Q]`. -/
theorem card_not_squarefree_le (Q : ℕ) :
    (((Icc 1 Q).filter (fun q => ¬ Squarefree q)).card : ℝ)
      ≤ ∑ d ∈ Icc 2 Q, (Q : ℝ) / (d : ℝ) ^ 2 := by
  classical
  have hsub : (Icc 1 Q).filter (fun q => ¬ Squarefree q)
      ⊆ (Icc 2 Q).biUnion (fun d => (Icc 1 Q).filter (fun q => d ^ 2 ∣ q)) := by
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
  have h1 : ((Icc 1 Q).filter (fun q => ¬ Squarefree q)).card
      ≤ ∑ d ∈ Icc 2 Q, ((Icc 1 Q).filter (fun q => d ^ 2 ∣ q)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have h2 : ∀ d ∈ Icc 2 Q,
      (((Icc 1 Q).filter (fun q => d ^ 2 ∣ q)).card : ℝ) ≤ (Q : ℝ) / (d : ℝ) ^ 2 := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) ^ 2 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      positivity
    have hnat := card_filter_sq_dvd_le Q d
    have hdiv : ((Q / d ^ 2 : ℕ) : ℝ) ≤ (Q : ℝ) / (d : ℝ) ^ 2 := by
      rw [le_div_iff₀ hdpos]
      have := Nat.div_mul_le_self Q (d ^ 2)
      calc ((Q / d ^ 2 : ℕ) : ℝ) * (d : ℝ) ^ 2 = ((Q / d ^ 2 * d ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (Q : ℝ) := by exact_mod_cast this
    exact le_trans (by exact_mod_cast hnat) hdiv
  calc (((Icc 1 Q).filter (fun q => ¬ Squarefree q)).card : ℝ)
      ≤ ((∑ d ∈ Icc 2 Q, ((Icc 1 Q).filter (fun q => d ^ 2 ∣ q)).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∑ d ∈ Icc 2 Q, (((Icc 1 Q).filter (fun q => d ^ 2 ∣ q)).card : ℝ) := by push_cast; ring
    _ ≤ ∑ d ∈ Icc 2 Q, (Q : ℝ) / (d : ℝ) ^ 2 := Finset.sum_le_sum h2

/-- `∑_{2 ≤ d ≤ n} 1/d² ≤ 3/4 − 1/n`, by the telescoping bound `1/d² ≤ 1/(d−1) − 1/d`. -/
theorem sum_inv_sq_le : ∀ n : ℕ, 2 ≤ n →
    ∑ d ∈ Icc 2 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / (n : ℝ) := by
  intro n
  induction n with
  | zero => omega
  | succ k IH =>
    intro hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · omega
      · norm_num
    · have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have hstep : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
        have hpos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
        have hmul : (k : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
        calc (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) :=
              one_div_le_one_div_of_le hpos hmul
          _ = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by field_simp; ring
      have hsplit : ∑ d ∈ Icc 2 (k + 1), (1 : ℝ) / (d : ℝ) ^ 2
          = (∑ d ∈ Icc 2 k, (1 : ℝ) / (d : ℝ) ^ 2) + 1 / ((k : ℝ) + 1) ^ 2 := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      have := IH hk2
      rw [hsplit]
      push_cast
      linarith

/-- **At least a quarter of the moduli up to `Q` are squarefree.** -/
theorem card_squarefreeUpTo_ge (Q : ℕ) : (Q : ℝ) / 4 ≤ ((squarefreeUpTo Q).card : ℝ) := by
  classical
  rcases Nat.lt_or_ge Q 2 with hQ | hQ
  · rcases Nat.eq_zero_or_pos Q with rfl | hQ1
    · simp [squarefreeUpTo]
    · have hmem : (1 : ℕ) ∈ squarefreeUpTo Q :=
        mem_squarefreeUpTo.2 ⟨⟨le_rfl, hQ1⟩, squarefree_one⟩
      have hpos : 1 ≤ (squarefreeUpTo Q).card := Finset.card_pos.2 ⟨1, hmem⟩
      have hposR : (1 : ℝ) ≤ ((squarefreeUpTo Q).card : ℝ) := by exact_mod_cast hpos
      have hQR : (Q : ℝ) ≤ 1 := by exact_mod_cast (by omega : Q ≤ 1)
      linarith
  · have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hsum : ∑ d ∈ Icc 2 Q, (Q : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 * (Q : ℝ) := by
      have h := sum_inv_sq_le Q hQ
      have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
      have hmul : ∑ d ∈ Icc 2 Q, (Q : ℝ) / (d : ℝ) ^ 2
          = (Q : ℝ) * ∑ d ∈ Icc 2 Q, (1 : ℝ) / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [hmul]
      nlinarith [one_div_pos.2 hQpos]
    have hsplit : ((Icc 1 Q).filter (fun q => Squarefree q)).card
        + ((Icc 1 Q).filter (fun q => ¬ Squarefree q)).card = Q := by
      rw [Finset.card_filter_add_card_filter_not (fun q => Squarefree q), Nat.card_Icc]
      omega
    have hsf : squarefreeUpTo Q = (Icc 1 Q).filter (fun q => Squarefree q) := rfl
    have hle := card_not_squarefree_le Q
    have hcast : (((Icc 1 Q).filter (fun q => Squarefree q)).card : ℝ)
        + (((Icc 1 Q).filter (fun q => ¬ Squarefree q)).card : ℝ) = (Q : ℝ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hsplit
    rw [hsf]
    linarith

/-- **The large sieve for a set missing half the classes**, with the linear lower bound for the
number of squarefree moduli inserted: `|A| Q/4 ≤ Q² + π N`. -/
theorem card_mul_le_of_sifted_half {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (hhalf : ∀ p, p.Prime → p ≤ Q → 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) * ((Q : ℝ) / 4) ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  calc (A.card : ℝ) * ((Q : ℝ) / 4)
      ≤ (A.card : ℝ) * ((squarefreeUpTo Q).card : ℝ) :=
        mul_le_mul_of_nonneg_left (card_squarefreeUpTo_ge Q) hA0
    _ ≤ (Q : ℝ) ^ 2 + Real.pi * N := card_le_sifted_squarefree_half hQ hA hhalf

/-- **A set below `N` that meets at most half the residue classes modulo every prime `p ≤ √N`
has at most `34 √N` elements.**  This is the classical consequence of the large sieve that the
sum over prime moduli alone does not give: over primes the same hypothesis only yields
`|A| ≪ N / log N`. -/
theorem card_le_of_sifted_half_sqrt {N : ℕ} (hN : 4 ≤ N) {A : Finset ℕ} (hA : A ⊆ range N)
    (hhalf : ∀ p, p.Prime → p ≤ Nat.sqrt N → 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) ≤ 34 * Real.sqrt N := by
  set Q := Nat.sqrt N with hQdef
  have hQ2 : 2 ≤ Q := by
    have h : Nat.sqrt 4 ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
    have h4 : Nat.sqrt 4 = 2 := by norm_num
    omega
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hsqrtN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hQle : (Q : ℝ) ≤ Real.sqrt N := by
    have h : Q ^ 2 ≤ N := Nat.sqrt_le' N
    have h' : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast h
    nlinarith [Real.sq_sqrt hNR.le, Real.sqrt_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) Q]
  have hQgt : Real.sqrt N < (Q : ℝ) + 1 := by
    have h : N < (Q + 1) ^ 2 := Nat.lt_succ_sqrt' N
    have h' : (N : ℝ) < ((Q : ℝ) + 1) ^ 2 := by exact_mod_cast h
    nlinarith [Real.sq_sqrt hNR.le, Real.sqrt_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) Q]
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt N := by
    have h : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [Real.sq_sqrt hNR.le, Real.sqrt_nonneg (N : ℝ)]
  have hQhalf : Real.sqrt N / 2 ≤ (Q : ℝ) := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hmain := card_mul_le_of_sifted_half hQ2 hA hhalf
  have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt hNR.le, Nat.cast_nonneg (α := ℝ) Q]
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hbound : (A.card : ℝ) * ((Real.sqrt N / 2) / 4) ≤ 4.15 * (N : ℝ) := by
    have h1 : (A.card : ℝ) * ((Real.sqrt N / 2) / 4) ≤ (A.card : ℝ) * ((Q : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      linarith
    nlinarith
  have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR.le).symm
  nlinarith [hbound, hsqrtN, hA0]

end LargeSieveSquarefree

end RiemannHypothesis
