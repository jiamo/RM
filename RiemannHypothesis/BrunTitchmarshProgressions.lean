/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BrunTitchmarsh

/-!
# Brun–Titchmarsh in arithmetic progressions

`RiemannHypothesis.BrunTitchmarsh` sifts the primes of an interval by every prime `p ≤ Q`. Here
the same sieve is run inside an arithmetic progression `n ≡ a (mod q)`: the primes of the
progression are reparametrized by `n = x + r + q t`, and for every prime `p ≤ Q` that does not
divide `q` the parameter `t` avoids one residue class modulo `p` — the one that would make `n`
divisible by `p`. The moduli that survive the sieve are therefore those coprime to `q`, and the
sifting sum is `siftSumCoprime q Q`.

## Main results

* `siftSumCoprime` — the sifting sum over the squarefree moduli `d ≤ Q` coprime to `q`;
* `coprime_harmonic_le_siftSumCoprime` — the reciprocals of the `n ≤ Q` coprime to `q` sum to at
  most `siftSumCoprime q Q`;
* `totient_mul_harmonic_le_coprime_harmonic` — the block bound
  `(φ(q)/q) ∑_{j ≤ J} 1/j ≤ ∑_{n ≤ J q, (n, q) = 1} 1/n`;
* `qPart`, `sum_inv_le_coprime_mul_smooth`, `sum_inv_smooth_le` — the splitting of an integer
  into its part coprime to `q` and its `q`-part, and the Euler factor `∏_{p ∣ q} p/(p − 1)` it
  produces;
* `totient_log_le_coprime_harmonic` — `(φ(q)/q) log Q ≤ ∑_{n ≤ Q, (n, q) = 1} 1/n`;
* `totient_log_le_siftSumCoprime` — `(φ(q)/q) log Q ≤ siftSumCoprime q Q`;
* `card_mul_siftSumCoprime_le` — the sieve for a set `A ⊆ [0, N)` that avoids one residue class
  modulo every prime `p ≤ Q` not dividing `q`;
* `card_primes_Ico_mod_le` — **Brun–Titchmarsh in progressions**: with `Y = ⌊y/q⌋ + 1` and
  `Q = ⌊√Y⌋`, the number of primes in `[x, x + y)` congruent to `a` modulo `q` is at most
  `4.15 q Y / (φ(q) log Q) + √Y + 1`, uniformly in `x` and `a`;
* `card_primes_range_mod_le` — the case `x = 0`, an upper bound for `π(N; q, a)`.

## Scope

The constant is not sharp, for the reasons recorded in `RiemannHypothesis.BrunTitchmarsh`: it
carries the factor `π` of this repository's large sieve, and the rigid sieve level `Q = ⌊√Y⌋`
halves the logarithm, so `4.15 q Y / (φ(q) log Q)` is of the shape `8.3 y / (φ(q) log(y/q))`
rather than the sharp `2 y / (φ(q) log(y/q))`. No Bombieri–Vinogradov consequence is drawn, and
nothing about `ζ` follows.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace BrunTitchmarsh

open LargeSieveSquarefree

/-! ## The sifting sum over moduli coprime to `q` -/

/-- The sifting sum of the large sieve at the weights `w p = p − 1` for `p ∤ q` and `w p = p` for
`p ∣ q`, that is `∑_{d ≤ Q squarefree, (d, q) = 1} ∏_{p ∣ d} 1/(p − 1)`. -/
def siftSumCoprime (q Q : ℕ) : ℝ :=
  ∑ d ∈ (squarefreeUpTo Q).filter (fun d => Nat.Coprime d q),
    ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)

/-- The reciprocals of the `n ≤ Q` coprime to `q` sum to at most `siftSumCoprime q Q`: the radical
of such an `n` is squarefree, coprime to `q` and at most `n`. -/
theorem coprime_harmonic_le_siftSumCoprime (q Q : ℕ) :
    ∑ n ∈ (Icc 1 Q).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n ≤ siftSumCoprime q Q := by
  classical
  have hsub : (Icc 1 Q).filter (fun n => Nat.Coprime n q) ⊆
      ((squarefreeUpTo Q).filter (fun d => Nat.Coprime d q)).biUnion
        (fun d => (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors)) := by
    intro n hn
    obtain ⟨hnI, hcop⟩ := Finset.mem_filter.mp hn
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
    have hdcop : Nat.Coprime d q := Nat.Coprime.coprime_dvd_left hdvd hcop
    refine Finset.mem_biUnion.2 ⟨d, Finset.mem_filter.2
      ⟨mem_squarefreeUpTo.2 ⟨⟨hdpos, le_trans hdle hn2⟩, hdsf⟩, hdcop⟩, ?_⟩
    exact Finset.mem_filter.2 ⟨hnI, by rw [hdpf]⟩
  calc ∑ n ∈ (Icc 1 Q).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n
      ≤ ∑ n ∈ ((squarefreeUpTo Q).filter (fun d => Nat.Coprime d q)).biUnion
          (fun d => (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors)), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ d ∈ (squarefreeUpTo Q).filter (fun d => Nat.Coprime d q),
          ∑ m ∈ (Icc 1 Q).filter (fun m => m.primeFactors = d.primeFactors), (1 : ℝ) / m :=
        sum_biUnion_le_sum_sum _ _ (fun n => by positivity) _
    _ ≤ siftSumCoprime q Q :=
        Finset.sum_le_sum fun d _ => sum_inv_primeFactors_eq_le Q d.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- `Icc 1 m` as a half-open interval. -/
theorem Icc_one_eq_Ico_one_succ (m : ℕ) : Icc 1 m = Ico 1 (m + 1) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- Any block of `q` consecutive integers contains exactly `φ(q)` integers coprime to `q`. -/
theorem block_coprime_card (b q : ℕ) :
    ((Ico b (b + q)).filter (fun n => Nat.Coprime n q)).card = q.totient := by
  classical
  rw [← Nat.filter_coprime_Ico_eq_totient q b]
  congr 1
  exact Finset.filter_congr fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩

/-- The block bound: each interval of `q` consecutive integers contains `φ(q)` integers coprime to
`q`, all of them at most the right endpoint, so
`(φ(q)/q) ∑_{j ≤ J} 1/j ≤ ∑_{n ≤ J q, (n, q) = 1} 1/n`. -/
theorem totient_mul_harmonic_le_coprime_harmonic {q : ℕ} (hq : 1 ≤ q) (J : ℕ) :
    ((q.totient : ℝ) / q) * ∑ j ∈ Icc 1 J, (1 : ℝ) / j
      ≤ ∑ n ∈ (Icc 1 (J * q)).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsplit : ∑ n ∈ (Icc 1 ((J + 1) * q)).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n
        = (∑ n ∈ (Icc 1 (J * q)).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n)
          + ∑ n ∈ (Ico (J * q + 1) (J * q + 1 + q)).filter (fun n => Nat.Coprime n q),
              (1 : ℝ) / n := by
      rw [Icc_one_eq_Ico_one_succ (J * q),
        show Icc 1 ((J + 1) * q) = Ico 1 (J * q + 1 + q) by
          rw [Icc_one_eq_Ico_one_succ]; congr 1; ring]
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ J * q + 1)
          (by omega : J * q + 1 ≤ J * q + 1 + q)]
    have hblock : ((q.totient : ℝ) / q) * (1 / ((J : ℝ) + 1))
        ≤ ∑ n ∈ (Ico (J * q + 1) (J * q + 1 + q)).filter (fun n => Nat.Coprime n q),
            (1 : ℝ) / n := by
      have hterm : ∀ n ∈ (Ico (J * q + 1) (J * q + 1 + q)).filter (fun n => Nat.Coprime n q),
          (1 : ℝ) / (((J : ℝ) + 1) * q) ≤ (1 : ℝ) / n := by
        intro n hn
        obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hnI
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hle : (n : ℝ) ≤ ((J : ℝ) + 1) * q := by
          have hn' : n ≤ (J + 1) * q := by nlinarith [Nat.zero_le (J * q)]
          calc (n : ℝ) ≤ (((J + 1) * q : ℕ) : ℝ) := by exact_mod_cast hn'
            _ = ((J : ℝ) + 1) * q := by push_cast; ring
        exact one_div_le_one_div_of_le hnpos hle
      have hcard := block_coprime_card (J * q + 1) q
      calc ((q.totient : ℝ) / q) * (1 / ((J : ℝ) + 1))
          = (q.totient : ℝ) * (1 / (((J : ℝ) + 1) * q)) := by field_simp
        _ = ∑ _n ∈ (Ico (J * q + 1) (J * q + 1 + q)).filter (fun n => Nat.Coprime n q),
              (1 : ℝ) / (((J : ℝ) + 1) * q) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hterm
    rw [hsplit, Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1)]
    push_cast
    nlinarith [ih, hblock]

/-- The block bound gives `(φ(q)/q) log ⌊Q/q⌋ ≤ siftSumCoprime q Q`.  This is superseded by
`totient_log_le_siftSumCoprime`, which has `log Q` in place of `log ⌊Q/q⌋`. -/
theorem totient_log_div_le_siftSumCoprime {q : ℕ} (hq : 1 ≤ q) (Q : ℕ) :
    ((q.totient : ℝ) / q) * Real.log (Q / q : ℕ) ≤ siftSumCoprime q Q := by
  classical
  set J := Q / q with hJ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnn : (0 : ℝ) ≤ (q.totient : ℝ) / q := by positivity
  have hlog : Real.log (J : ℕ) ≤ ∑ j ∈ Icc 1 J, (1 : ℝ) / j := log_le_sum_inv J
  have hsub : (Icc 1 (J * q)).filter (fun n => Nat.Coprime n q)
      ⊆ (Icc 1 Q).filter (fun n => Nat.Coprime n q) :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (Nat.div_mul_le_self Q q))
  have hmono : ∑ n ∈ (Icc 1 (J * q)).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n
      ≤ ∑ n ∈ (Icc 1 Q).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc ((q.totient : ℝ) / q) * Real.log (J : ℕ)
      ≤ ((q.totient : ℝ) / q) * ∑ j ∈ Icc 1 J, (1 : ℝ) / j :=
        mul_le_mul_of_nonneg_left hlog hnn
    _ ≤ _ := le_trans (totient_mul_harmonic_le_coprime_harmonic hq J)
        (le_trans hmono (coprime_harmonic_le_siftSumCoprime q Q))

/-! ## The `q`-part of an integer, and the sharp lower bound for the sifting sum -/

/-- The `q`-part of `n`: the largest divisor of `n` all of whose prime factors divide `q`. -/
def qPart (q n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.filter (fun p => p ∣ q), p ^ n.factorization p

theorem qPart_pos (q n : ℕ) : 0 < qPart q n :=
  Finset.prod_pos fun p hp => Nat.pow_pos
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos

theorem qPart_dvd (q n : ℕ) : qPart q n ∣ n := by
  classical
  have hS : ∀ p ∈ n.primeFactors.filter (fun p => p ∣ q), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  rw [qPart]
  generalize n.primeFactors.filter (fun p => p ∣ q) = S at hS
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      have hpp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ r ∈ S, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
      have hcop : Nat.Coprime (p ^ n.factorization p) (∏ r ∈ S, r ^ n.factorization r) := by
        refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun r hr => ?_)
        exact Nat.Coprime.pow_right _
          ((Nat.coprime_primes hpp (hS' r hr)).2 (by rintro rfl; exact hp hr))
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Nat.ordProj_dvd n p) (ih hS')

theorem primeFactors_qPart_subset {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    (qPart q n).primeFactors ⊆ q.primeFactors := by
  classical
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrd := Nat.dvd_of_mem_primeFactors hr
  rw [qPart, hrp.prime.dvd_finsetProd_iff _] at hrd
  obtain ⟨p, hp, hdvd⟩ := hrd
  have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  have hrpe : r = p := (Nat.prime_dvd_prime_iff_eq hrp hpp).mp (hrp.dvd_of_dvd_pow hdvd)
  subst hrpe
  exact Nat.mem_primeFactors.2 ⟨hrp, (Finset.mem_filter.mp hp).2, hq⟩

/-- Dividing out the `q`-part leaves a number coprime to `q`. -/
theorem coprime_div_qPart {n : ℕ} (hn : n ≠ 0) (q : ℕ) : Nat.Coprime (n / qPart q n) q := by
  classical
  set k := qPart q n with hk
  have hkd : k ∣ n := qPart_dvd q n
  have hmk : k * (n / k) = n := Nat.mul_div_cancel' hkd
  by_contra hcon
  obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hcon
  have hrm : r ∣ n / k := hrdvd.trans (Nat.gcd_dvd_left _ _)
  have hrq : r ∣ q := hrdvd.trans (Nat.gcd_dvd_right _ _)
  have hrn : r ∣ n := by rw [← hmk]; exact Dvd.dvd.mul_left hrm k
  have hrmem : r ∈ n.primeFactors.filter (fun p => p ∣ q) :=
    Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hrp, hrn, hn⟩, hrq⟩
  have hpow : r ^ n.factorization r ∣ k := Finset.dvd_prod_of_mem _ hrmem
  have hfin : r ^ (n.factorization r + 1) ∣ k * (n / k) := by
    rw [pow_succ]; exact mul_dvd_mul hpow hrm
  rw [hmk] at hfin
  have := (Nat.Prime.pow_dvd_iff_le_factorization hrp hn).mp hfin
  omega

/-- Splitting `n` into its part coprime to `q` and its `q`-part factorizes the harmonic sum. -/
theorem sum_inv_le_coprime_mul_smooth {q : ℕ} (hq : q ≠ 0) (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, (1 : ℝ) / n
      ≤ (∑ m ∈ (Icc 1 Q).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m)
        * ∑ k ∈ (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors), (1 : ℝ) / k := by
  classical
  set M := (Icc 1 Q).filter (fun m => Nat.Coprime m q) with hM
  set K := (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors) with hK
  set F : ℕ → ℕ × ℕ := fun n => (n / qPart q n, qPart q n) with hF
  have hsplit : ∀ n, 0 < n → (F n).1 * (F n).2 = n := by
    intro n hn
    simp only [hF]
    exact Nat.div_mul_cancel (qPart_dvd q n)
  have hinj : ∀ m ∈ Icc 1 Q, ∀ n ∈ Icc 1 Q, F m = F n → m = n := by
    intro m hm n hn h
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    rw [← hsplit m (by omega), ← hsplit n (by omega), h]
  have hmem : ∀ n ∈ Icc 1 Q, F n ∈ M ×ˢ K := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hkpos : 0 < qPart q n := qPart_pos q n
    have hkle : qPart q n ≤ n := Nat.le_of_dvd (by omega) (qPart_dvd q n)
    have hmpos : 0 < n / qPart q n := Nat.div_pos hkle hkpos
    have hmle : n / qPart q n ≤ n := Nat.div_le_self _ _
    exact Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hmpos, le_trans hmle hn2⟩,
          coprime_div_qPart (by omega) q⟩,
        Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hkpos, le_trans hkle hn2⟩,
          primeFactors_qPart_subset hq n⟩⟩
  have hval : ∀ n ∈ Icc 1 Q, (1 : ℝ) / n = 1 / ((F n).1 : ℝ) * (1 / ((F n).2 : ℝ)) := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    have hcast : ((n : ℕ) : ℝ) = ((F n).1 : ℝ) * ((F n).2 : ℝ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) (hsplit n (by omega)).symm
    rw [hcast]
    field_simp
  calc ∑ n ∈ Icc 1 Q, (1 : ℝ) / n
      = ∑ n ∈ Icc 1 Q, 1 / ((F n).1 : ℝ) * (1 / ((F n).2 : ℝ)) := Finset.sum_congr rfl hval
    _ = ∑ z ∈ (Icc 1 Q).image F, 1 / (z.1 : ℝ) * (1 / (z.2 : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ z ∈ M ×ˢ K, 1 / (z.1 : ℝ) * (1 / (z.2 : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => by positivity)
        intro z hz
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
        exact hmem n hn
    _ = (∑ m ∈ M, (1 : ℝ) / m) * ∑ k ∈ K, (1 : ℝ) / k := by
        rw [Finset.sum_product, Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]

/-- The reciprocals of the `k ≤ Q` all of whose prime factors divide `q` sum to at most
`∏_{p ∣ q} p/(p − 1)`. -/
theorem sum_inv_smooth_le (q Q : ℕ) :
    ∑ k ∈ (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors), (1 : ℝ) / k
      ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  have hsub : (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors) ⊆
      (q.primeFactors.powerset).biUnion
        (fun S => (Icc 1 Q).filter (fun m => m.primeFactors = S)) := by
    intro k hk
    obtain ⟨hkI, hkS⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_biUnion.2 ⟨k.primeFactors, Finset.mem_powerset.2 hkS,
      Finset.mem_filter.2 ⟨hkI, rfl⟩⟩
  have hstep : ∑ k ∈ (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors), (1 : ℝ) / k
      ≤ ∑ S ∈ q.primeFactors.powerset, ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) := by
    calc ∑ k ∈ (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors), (1 : ℝ) / k
        ≤ ∑ k ∈ (q.primeFactors.powerset).biUnion
            (fun S => (Icc 1 Q).filter (fun m => m.primeFactors = S)), (1 : ℝ) / k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ S ∈ q.primeFactors.powerset,
            ∑ m ∈ (Icc 1 Q).filter (fun m => m.primeFactors = S), (1 : ℝ) / m :=
          sum_biUnion_le_sum_sum _ _ (fun n => by positivity) _
      _ ≤ _ := Finset.sum_le_sum fun S hS => sum_inv_primeFactors_eq_le Q S
            (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp))
  refine hstep.trans (le_of_eq ?_)
  have hpa := Finset.prod_add (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1)) (fun _ => (1 : ℝ))
    q.primeFactors
  simp only [Finset.prod_const_one, mul_one] at hpa
  rw [← hpa]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `∏_{p ∣ q} p/(p − 1) = q/φ(q)`. -/
theorem prod_primeFactors_self_div_sub_one {q : ℕ} (hq : q ≠ 0) :
    ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) = (q : ℝ) / (q.totient : ℝ) := by
  classical
  have hkey := Nat.totient_mul_prod_primeFactors q
  have hA : (0 : ℝ) < ∏ p ∈ q.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hB : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hcast : ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 : (1 : ℕ) ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    push_cast [Nat.cast_sub h1]
    ring
  have hkeyR : (q.totient : ℝ) * (∏ p ∈ q.primeFactors, (p : ℝ))
      = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) hkey
    push_cast at h
    rw [← hcast]
    push_cast
    exact h
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  rw [Finset.prod_div_distrib]
  field_simp
  linarith [hkeyR]

/-- **`(φ(q)/q) log Q ≤ ∑_{n ≤ Q, (n, q) = 1} 1/n`.** -/
theorem totient_log_le_coprime_harmonic {q : ℕ} (hq : 1 ≤ q) (Q : ℕ) :
    ((q.totient : ℝ) / q) * Real.log Q
      ≤ ∑ m ∈ (Icc 1 Q).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m := by
  classical
  have hq0 : q ≠ 0 := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  set SM := ∑ m ∈ (Icc 1 Q).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m with hSM
  have hSM0 : (0 : ℝ) ≤ SM := Finset.sum_nonneg fun m _ => by positivity
  have h1 : Real.log Q * (q.totient : ℝ) ≤ SM * (q : ℝ) := by
    have hlog := log_le_sum_inv Q
    have hsplit := sum_inv_le_coprime_mul_smooth hq0 Q
    have hsm := (sum_inv_smooth_le q Q).trans_eq (prod_primeFactors_self_div_sub_one hq0)
    have hmul : SM * ∑ k ∈ (Icc 1 Q).filter (fun k => k.primeFactors ⊆ q.primeFactors),
        (1 : ℝ) / k ≤ SM * ((q : ℝ) / (q.totient : ℝ)) := mul_le_mul_of_nonneg_left hsm hSM0
    have hle : Real.log Q ≤ SM * ((q : ℝ) / (q.totient : ℝ)) := by
      rw [← hSM] at hsplit
      linarith
    rw [mul_div_assoc'] at hle
    rw [← le_div_iff₀ hphi]
    exact hle
  rw [div_mul_eq_mul_div, div_le_iff₀ hqR]
  linarith

/-- **`(φ(q)/q) log Q ≤ siftSumCoprime q Q`**, the classical lower bound for the sifting sum at
the moduli coprime to `q`. -/
theorem totient_log_le_siftSumCoprime {q : ℕ} (hq : 1 ≤ q) (Q : ℕ) :
    ((q.totient : ℝ) / q) * Real.log Q ≤ siftSumCoprime q Q :=
  (totient_log_le_coprime_harmonic hq Q).trans (coprime_harmonic_le_siftSumCoprime q Q)

/-! ## The sieve at moduli coprime to `q` -/

/-- **The large sieve for a set that avoids one residue class modulo every prime `p ≤ Q` that does
not divide `q`.** -/
theorem card_mul_siftSumCoprime_le {N Q q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * siftSumCoprime q Q ≤ (Q : ℝ) ^ 2 + Real.pi * N := by
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
  have hmain := card_le_sifted_squarefree hQ hA w hwpos hwle hAw
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

/-! ## Reparametrizing a progression -/

/-- The least shift `r < q` with `x + r ≡ a (mod q)`. -/
def modOffset (x q a : ℕ) : ℕ := (a + q - x % q) % q

theorem modOffset_lt {q : ℕ} (hq : 1 ≤ q) (x a : ℕ) : modOffset x q a < q :=
  Nat.mod_lt _ hq

theorem add_modOffset_mod {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x : ℕ) :
    (x + modOffset x q a) % q = a := by
  have hs : x % q < q := Nat.mod_lt _ hq
  rw [modOffset, Nat.add_mod x _ q, Nat.mod_mod]
  rcases Nat.lt_or_ge a (x % q) with h | h
  · rw [Nat.mod_eq_of_lt (by omega : a + q - x % q < q),
      show x % q + (a + q - x % q) = a + q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ha]
  · rw [show a + q - x % q = q + (a - x % q) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : a - x % q < q),
      show x % q + (a - x % q) = a by omega, Nat.mod_eq_of_lt ha]

/-- Every `n ≥ x` in the progression `a (mod q)` is `x + r + q t` for a unique `t`. -/
theorem exists_param {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) {x n : ℕ} (hxn : x ≤ n)
    (hn : n % q = a) : ∃ t, n = x + modOffset x q a + q * t := by
  set r := modOffset x q a with hr
  have hrlt : r < q := modOffset_lt hq x a
  have hmod : (x + r) % q = a := add_modOffset_mod hq ha x
  have hcong : (x + r) ≡ n [MOD q] := by unfold Nat.ModEq; rw [hmod, hn]
  have hle : x + r ≤ n := by
    by_contra hcon
    push Not at hcon
    have h2 : q ∣ (x + r) - n := (Nat.modEq_iff_dvd' hcon.le).mp hcong.symm
    have h3 : 0 < (x + r) - n := by omega
    have := Nat.le_of_dvd h3 h2
    omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hcong
  exact ⟨t, by omega⟩

/-- A prime `p ≤ Q` not dividing `q` misses one residue class among the parameters `t` for which
`b + q t` is a prime exceeding `Q`. -/
theorem progression_avoid (b Y Q : ℕ) {p q : ℕ} (hp : p.Prime) (hpQ : p ≤ Q)
    (hpq : ¬ p ∣ q) :
    ∃ c < p, ∀ t ∈ ((range Y).filter (fun t => (b + q * t).Prime)).filter
        (fun t => Q < b + q * t), t % p ≠ c := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpq
  refine ⟨((-(b : ZMod p)) * (q : ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
  intro t ht hcon
  obtain ⟨htS, hgt⟩ := Finset.mem_filter.mp ht
  obtain ⟨-, hprime⟩ := Finset.mem_filter.mp htS
  have hcast : ((t : ℕ) : ZMod p) = (-(b : ZMod p)) * (q : ZMod p)⁻¹ := by
    conv_lhs => rw [← ZMod.natCast_mod t p, hcon]
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hz : ((b + q * t : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hcast]
    field_simp
    ring
  have hdvd : p ∣ b + q * t := by rwa [ZMod.natCast_eq_zero_iff] at hz
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · exact absurd h hp.ne_one
  · omega

/-! ## Brun–Titchmarsh in progressions -/

/-- **Brun–Titchmarsh in arithmetic progressions, at an arbitrary sieve level `Q ≥ 2`.**  Write
`Y = ⌊y/q⌋ + 1`.  Uniformly in the starting point `x` and in the residue `a < q`, the number of
primes in `[x, x + y)` congruent to `a` modulo `q` is at most
`(Q² + π Y) q / (φ(q) log Q) + Q + 1`.

The level is free: `Q = ⌊√Y⌋` recovers `card_primes_Ico_mod_le`, and
`Q = ⌊√Y / log Y⌋` gives the constant `2π + ε` of
`RiemannHypothesis/BrunTitchmarshSharp.lean`. -/
theorem card_primes_Ico_mod_le_of_level {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x y : ℕ) {Q : ℕ}
    (hQlevel : 2 ≤ Q) :
    (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * ((y / q + 1 : ℕ) : ℝ)) * q
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
  have hmain := card_mul_siftSumCoprime_le (N := Y) (q := q) hQ2 hAsub
    (fun p hp hpQ hpq => progression_avoid b Y Q hp hpQ hpq)
  have hsift0 := totient_log_le_siftSumCoprime hq Q
  set L := Real.log ((Q : ℕ) : ℝ) with hL
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (by omega : 0 < q)
    exact_mod_cast h
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  clear_value A B T S L b r Y
  have hstep : (A.card : ℝ) * ((q.totient : ℝ) / q * L) ≤ (Q : ℝ) ^ 2 + Real.pi * (Y : ℝ) := by
    have h1 : (A.card : ℝ) * ((q.totient : ℝ) / q * L) ≤ (A.card : ℝ) * siftSumCoprime q Q :=
      mul_le_mul_of_nonneg_left hsift0 hAcard0
    linarith
  have hAle : (A.card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * (Y : ℝ)) * q / ((q.totient : ℝ) * L) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q.totient : ℝ) * L)]
    have hid : (A.card : ℝ) * ((q.totient : ℝ) / q * L) * q
        = (A.card : ℝ) * ((q.totient : ℝ) * L) := by field_simp
    nlinarith [hstep, hqR]
  have hBle : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
  have hScast : (S.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    have h : S.card ≤ A.card + B.card := by omega
    exact_mod_cast h
  linarith

/-- **Brun–Titchmarsh in arithmetic progressions, with a non-optimal constant.**  Write
`Y = ⌊y/q⌋ + 1` and `Q = ⌊√Y⌋`.  Uniformly in the starting point `x` and in the residue `a < q`,
the number of primes in `[x, x + y)` congruent to `a` modulo `q` is at most
`4.15 q Y / (φ(q) log Q) + √Y + 1`, as soon as `Q ≥ 2`.  It is the level `Q = ⌊√Y⌋` of
`card_primes_Ico_mod_le_of_level`, for which `Q² ≤ Y` and `π ≤ 3.15`. -/
theorem card_primes_Ico_mod_le {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x y : ℕ)
    (hQsqrt : 2 ≤ Nat.sqrt (y / q + 1)) :
    (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ 4.15 * q * ((y / q + 1 : ℕ) : ℝ)
            / ((q.totient : ℝ) * Real.log (Nat.sqrt (y / q + 1)))
          + Real.sqrt ((y / q + 1 : ℕ) : ℝ) + 1 := by
  set Y := y / q + 1 with hY
  set Q := Nat.sqrt Y with hQdef
  have hbase := card_primes_Ico_mod_le_of_level hq ha x y (Q := Q) hQsqrt
  have hYpos : 0 < Y := Nat.succ_pos _
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQsqrt
  have hLpos : 0 < Real.log Q := Real.log_pos (by linarith)
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (by omega : 0 < q)
    exact_mod_cast h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQsq : (Q : ℝ) ^ 2 ≤ (Y : ℝ) := by exact_mod_cast Nat.sqrt_le' Y
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  -- the numerator is at most `4.15 Y`
  have hnum : ((Q : ℝ) ^ 2 + Real.pi * (Y : ℝ)) * q ≤ 4.15 * q * (Y : ℝ) := by
    have h1 : (Q : ℝ) ^ 2 + Real.pi * (Y : ℝ) ≤ 4.15 * (Y : ℝ) := by nlinarith [hQsq, hpi, hYR]
    nlinarith [h1, hqR]
  have hden : (0 : ℝ) < (q.totient : ℝ) * Real.log Q := by positivity
  have hmain : ((Q : ℝ) ^ 2 + Real.pi * (Y : ℝ)) * q / ((q.totient : ℝ) * Real.log Q)
      ≤ 4.15 * q * (Y : ℝ) / ((q.totient : ℝ) * Real.log Q) :=
    div_le_div_of_nonneg_right hnum hden.le
  -- the primes below the level are at most `√Y + 1`
  have hQle : (Q : ℝ) ≤ Real.sqrt (Y : ℝ) := by
    nlinarith [Real.sq_sqrt hYR.le, Real.sqrt_nonneg (Y : ℝ), Nat.cast_nonneg (α := ℝ) Q]
  linarith

/-- **The prime counting function of an arithmetic progression**, the case `x = 0` of
`card_primes_Ico_mod_le`: with `Y = ⌊N/q⌋ + 1` and `Q = ⌊√Y⌋ ≥ 2`,
`π(N; q, a) ≤ 4.15 q Y / (φ(q) log Q) + √Y + 1`. -/
theorem card_primes_range_mod_le {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (N : ℕ)
    (hQsqrt : 2 ≤ Nat.sqrt (N / q + 1)) :
    (((range N).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ 4.15 * q * ((N / q + 1 : ℕ) : ℝ)
            / ((q.totient : ℝ) * Real.log (Nat.sqrt (N / q + 1)))
          + Real.sqrt ((N / q + 1 : ℕ) : ℝ) + 1 := by
  have h := card_primes_Ico_mod_le hq ha 0 N hQsqrt
  rwa [Nat.zero_add, ← Finset.range_eq_Ico] at h

end BrunTitchmarsh

end RiemannHypothesis
