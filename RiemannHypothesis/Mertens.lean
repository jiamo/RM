/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.Chebyshev
import RiemannHypothesis.ChebyshevLower

/-!
# Mertens' first theorem

`∑_{n ≤ x} Λ(n)/n = log x + O(1)`, with an explicit constant.  This is the first of Mertens'
three theorems (1874) and the standard elementary substitute for the prime number theorem in
the classical proofs; Mathlib contains none of them.

The proof is the classical one:

* `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`, from `∑_{d ∣ n} Λ(d) = log n` by interchanging
  the two summations;
* `N log N − N ≤ ∑_{n ≤ N} log n ≤ N log N`, the lower bound by induction from
  `log(1 + 1/N) ≤ 1/N`;
* replacing `⌊N/d⌋` by `N/d` costs at most `ψ(N) ≤ (log 4 + 4) N` (Chebyshev's upper bound,
  from Mathlib).

Dividing by `N` gives `log N − 1 ≤ ∑_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4`.

## Main results

* `sum_log_eq_sum_vonMangoldt_mul_floor_div` : `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`.
* `mertens_first_nat` : `|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4` for `N ≥ 1`.
* `mertens_first` : the same for a real argument, with constant `log 4 + 4 + log 2`.
* `mertens_first_isBigO` : `∑_{n ≤ x} Λ(n)/n − log x` is bounded.
-/

noncomputable section

open Asymptotics Filter Finset Real
open ArithmeticFunction hiding log

namespace RiemannHypothesis

/-- The summatory function of `Λ(n)/n` up to `x`. -/
def mertensSum (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n

/-- `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`, by interchanging the order of summation in
`∑_{n ≤ N} ∑_{d ∣ n} Λ(d)`. -/
lemma sum_log_eq_sum_vonMangoldt_mul_floor_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  classical
  have h1 : ∀ n ∈ Finset.Ioc 0 N,
      Real.log n = ∑ d ∈ Finset.Ioc 0 N, if d ∣ n then Λ d else 0 := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.1 hn
    rw [← vonMangoldt_sum (n := n), ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn0, le_trans (Nat.le_of_dvd hn0 hd) hnN⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

/-- `∑_{n ≤ N} log n ≤ N log N`. -/
lemma sum_log_le (N : ℕ) : ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ (N : ℝ) * Real.log N := by
  calc ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact Real.log_le_log (by exact_mod_cast (Finset.mem_Ioc.1 hn).1)
          (by exact_mod_cast (Finset.mem_Ioc.1 hn).2)
    _ = (N : ℝ) * Real.log N := by simp

/-- `N log N − N ≤ ∑_{n ≤ N} log n`, by induction from `log(1 + 1/N) ≤ 1/N`. -/
lemma sum_log_ge (N : ℕ) : (N : ℝ) * Real.log N - N ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hkey : (N : ℝ) * Real.log ((N : ℝ) + 1) ≤ (N : ℝ) * Real.log N + 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have he : ((N : ℝ) + 1) / N - 1 = 1 / N := by
        field_simp
        ring
      rw [he] at h
      have h2 := mul_le_mul_of_nonneg_left h hN0.le
      rw [mul_sub, mul_one_div, div_self (ne_of_gt hN0)] at h2
      linarith
    push_cast
    linarith

/-- Replacing `⌊N/d⌋` by `N/d` in `∑_d Λ(d) ⌊N/d⌋` costs between `0` and `ψ(N)`. -/
lemma sum_vonMangoldt_mul_floor_div_le (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d ∧
      (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d
        ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) + Chebyshev.psi N := by
  have hpsi : Chebyshev.psi N = ∑ d ∈ Finset.Ioc 0 N, Λ d := by
    rw [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.mul_sum, hpsi, ← Finset.sum_add_distrib]
  constructor
  · refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.1 hd).1
    have hfloor : (((N / d : ℕ) : ℝ)) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hd0]
      exact_mod_cast Nat.div_mul_le_self N d
    have := mul_le_mul_of_nonneg_left hfloor (vonMangoldt_nonneg (n := d))
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) := this
      _ = (N : ℝ) * (Λ d / d) := by ring
  · refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.1 hd).1
    have hfloor : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hd0]
      have hdn : 0 < d := by exact_mod_cast hd0
      have : N < (N / d + 1) * d := by
        have h1 := Nat.div_add_mod N d
        have h2 := Nat.mod_lt N hdn
        nlinarith [h1, h2]
      calc (N : ℝ) ≤ ((N / d + 1 : ℕ) : ℝ) * d := by exact_mod_cast this.le
        _ = (((N / d : ℕ) : ℝ) + 1) * d := by push_cast; ring
    have := mul_le_mul_of_nonneg_left hfloor (vonMangoldt_nonneg (n := d))
    calc (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
      _ ≤ Λ d * (((N / d : ℕ) : ℝ) + 1) := this
      _ = Λ d * ((N / d : ℕ) : ℝ) + Λ d := by ring

/-- **Mertens' first theorem**, at integer arguments:
`|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4`. -/
theorem mertens_first_nat {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Ioc 0 N, Λ n / n - Real.log N| ≤ Real.log 4 + 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlow, hhigh⟩ := sum_vonMangoldt_mul_floor_div_le N
  rw [← sum_log_eq_sum_vonMangoldt_mul_floor_div N] at hlow hhigh
  have hpsi : Chebyshev.psi N ≤ (Real.log 4 + 4) * N :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have hup := sum_log_le N
  have hdown := sum_log_ge N
  have h1 : (N : ℝ) * (∑ n ∈ Finset.Ioc 0 N, Λ n / n)
      ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith [hhigh, hup, hpsi]
  have h2 : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * (∑ n ∈ Finset.Ioc 0 N, Λ n / n) := by
    nlinarith [hlow, hdown]
  have h1' := le_of_mul_le_mul_left h1 hN0
  have h2' := le_of_mul_le_mul_left h2 hN0
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **Mertens' first theorem**: `∑_{n ≤ x} Λ(n)/n = log x + O(1)`, with the explicit bound
`|∑_{n ≤ x} Λ(n)/n − log x| ≤ log 4 + 4 + log 2` for `x ≥ 1`. -/
theorem mertens_first {x : ℝ} (hx : 1 ≤ x) :
    |mertensSum x - Real.log x| ≤ Real.log 4 + 4 + Real.log 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl1
  have hflle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hhalf : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    rcases le_or_gt 2 x with h2 | h2
    · have := Nat.lt_floor_add_one x
      linarith
    · have : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl1
      linarith
  have hlogdiff : 0 ≤ Real.log x - Real.log ⌊x⌋₊ ∧
      Real.log x - Real.log ⌊x⌋₊ ≤ Real.log 2 := by
    constructor
    · have := Real.log_le_log hfl0 hflle
      linarith
    · have h := Real.log_le_log (by positivity) hhalf
      rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at h
      linarith
  have hmain := mertens_first_nat hfl1
  rw [abs_le] at hmain ⊢
  unfold mertensSum
  constructor <;> [linarith [hmain.1, hlogdiff.2]; linarith [hmain.2, hlogdiff.1,
    Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]]

/-! ### The prime form: `∑_{p ≤ x} log p / p = log x + O(1)`

The difference between `∑_{n ≤ x} Λ(n)/n` and `∑_{p ≤ x} log p / p` is the contribution of the
proper prime powers `p^k`, `k ≥ 2`, which is bounded by an absolute constant. -/

/-- The summatory function `∑_{p ≤ x} log p / p` over primes. -/
def primeLogSum (x : ℝ) : ℝ := ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, Real.log p / p

/-- `log m ≤ 2 √m`. -/
lemma log_le_two_sqrt (m : ℕ) : Real.log m ≤ 2 * Real.sqrt m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hm0.le] at h
  linarith

/-- `∑_{m = 2}^{M} 1/(m √m) ≤ 2`, by telescoping `1/(m√m) ≤ 2/√(m−1) − 2/√m`. -/
lemma sum_one_div_mul_sqrt_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, 1 / ((m : ℝ) * Real.sqrt m) ≤ 2 := by
  have key : ∀ M : ℕ, 1 ≤ M →
      ∑ m ∈ Finset.Icc 2 M, 1 / ((m : ℝ) * Real.sqrt m) ≤ 2 - 2 / Real.sqrt M := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with rfl | hM0
      · norm_num
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
      have ha : 0 < Real.sqrt M := Real.sqrt_pos.2 hMr
      have hb : 0 < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
      have ha2 : Real.sqrt M ^ 2 = (M : ℝ) := Real.sq_sqrt hMr.le
      have hb2 : Real.sqrt ((M : ℝ) + 1) ^ 2 = (M : ℝ) + 1 := Real.sq_sqrt (by linarith)
      have hab : Real.sqrt M ≤ Real.sqrt ((M : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have hstep : 1 / (((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1))
          ≤ 2 / Real.sqrt M - 2 / Real.sqrt ((M : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt ha) (ne_of_gt hb),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [ha, hb, ha2, hb2, hab, sq_nonneg (Real.sqrt ((M : ℝ) + 1) - Real.sqrt M)]
      have hih := ih (by omega)
      push_cast
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have h2 := key M hM
  have hpos : 0 < Real.sqrt M := Real.sqrt_pos.2 (by exact_mod_cast hM)
  have : 0 ≤ 2 / Real.sqrt M := by positivity
  linarith

/-- `∑_{m = 2}^{M} log m / m² ≤ 4`. -/
lemma sum_log_div_sq_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, Real.log m / (m : ℝ) ^ 2 ≤ 4 := by
  have h : ∑ m ∈ Finset.Icc 2 M, Real.log m / (m : ℝ) ^ 2
      ≤ ∑ m ∈ Finset.Icc 2 M, 2 * (1 / ((m : ℝ) * Real.sqrt m)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm2 : 2 ≤ m := (Finset.mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hm2
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    have hs2 : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le
    have hlog := log_le_two_sqrt m
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (1 / ((m : ℝ) * Real.sqrt m)) * (m : ℝ) ^ 2 = 2 * Real.sqrt m := by
      field_simp
      nlinarith [hs2, hs]
    rw [this]
    exact hlog
  refine le_trans h ?_
  rw [← Finset.mul_sum]
  have := sum_one_div_mul_sqrt_le M
  linarith

/-- The geometric tail `∑_{k = 2}^{N} r^k ≤ 2r²` for `0 < r ≤ 1/2`. -/
lemma geom_tail_le {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, r ^ k ≤ 2 * r ^ 2 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Finset.Icc 2 N, r ^ k ≤ 2 * r ^ 2 - 2 * r ^ (N + 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N _ ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hpow : (0 : ℝ) < r ^ (N + 1) := by positivity
      have h1 : 2 * r ^ (N + 2) ≤ r ^ (N + 1) := by
        have hrw : r ^ (N + 2) = r ^ (N + 1) * r := by ring
        rw [hrw]
        nlinarith
      nlinarith [ih, h1]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.ofNat_pos, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
    positivity
  have hpos : (0 : ℝ) < r ^ (N + 1) := by positivity
  linarith [key N hN]

/-- The contribution of the proper prime powers `p^k`, `k ≥ 2`, to `∑_{n ≤ N} Λ(n)/n` is at
most `8`. -/
lemma properPrimePower_sum_le (N : ℕ) :
    ∑ n ∈ {n ∈ Finset.Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime}, Λ n / n ≤ 8 := by
  classical
  set S := {n ∈ Finset.Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime} with hSdef
  set T := Finset.Icc 2 N ×ˢ Finset.Icc 2 N with hTdef
  set g : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac) with hgdef
  have hpow : ∀ n ∈ S, (g n).1 ^ (g n).2 = n := by
    intro n hn
    simp only [hSdef, Finset.mem_filter] at hn
    exact hn.2.1.minFac_pow_factorization_eq
  have hmemT : ∀ n ∈ S, g n ∈ T := by
    intro n hn
    simp only [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, hnN⟩, hpp, hnp⟩ := hn
    have hne1 : n ≠ 1 := by
      rintro rfl
      exact not_isPrimePow_one hpp
    have hp := Nat.minFac_prime hne1
    have hpe : n.minFac ^ n.factorization n.minFac = n := hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ n.factorization n.minFac := by
      by_contra hcon
      push Not at hcon
      rcases (by omega : n.factorization n.minFac = 0 ∨ n.factorization n.minFac = 1) with h0 | h1
      · rw [h0, pow_zero] at hpe
        exact hne1 hpe.symm
      · rw [h1, pow_one] at hpe
        exact hnp (hpe ▸ hp)
    have hple : n.minFac ≤ N := le_trans (Nat.minFac_le hn0) hnN
    have hkle : n.factorization n.minFac ≤ N := by
      have h2 : 2 ^ n.factorization n.minFac ≤ n := by
        calc 2 ^ n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
              Nat.pow_le_pow_left hp.two_le _
          _ = n := hpe
      have := Nat.lt_two_pow_self (n := n.factorization n.minFac)
      omega
    simp only [hTdef, Finset.mem_product, Finset.mem_Icc, hgdef]
    exact ⟨⟨hp.two_le, hple⟩, hk2, hkle⟩
  have hinj : Set.InjOn g ↑S := by
    intro a ha b hb hab
    have ha' := hpow a (by simpa using ha)
    have hb' := hpow b (by simpa using hb)
    rw [← ha', ← hb', hab]
  have hstep1 : ∑ n ∈ S, Λ n / n
      = ∑ t ∈ S.image g, Λ ((t.1 : ℕ) ^ (t.2 : ℕ)) / ((t.1 : ℕ) ^ (t.2 : ℕ) : ℕ) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hpow n hn]
  have hsubset : S.image g ⊆ T := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 ht
    exact hmemT n hn
  have hnonneg : ∀ t : ℕ × ℕ, 0 ≤ Λ ((t.1 : ℕ) ^ (t.2 : ℕ)) / ((t.1 : ℕ) ^ (t.2 : ℕ) : ℕ) := by
    intro t
    exact div_nonneg vonMangoldt_nonneg (by positivity)
  have hstep2 : ∑ t ∈ S.image g, Λ ((t.1 : ℕ) ^ (t.2 : ℕ)) / ((t.1 : ℕ) ^ (t.2 : ℕ) : ℕ)
      ≤ ∑ t ∈ T, Λ ((t.1 : ℕ) ^ (t.2 : ℕ)) / ((t.1 : ℕ) ^ (t.2 : ℕ) : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun t _ _ => hnonneg t)
  have hstep3 : ∑ t ∈ T, Λ ((t.1 : ℕ) ^ (t.2 : ℕ)) / ((t.1 : ℕ) ^ (t.2 : ℕ) : ℕ) ≤ 8 := by
    rw [hTdef, Finset.sum_product]
    have hinner : ∀ p ∈ Finset.Icc 2 N,
        ∑ k ∈ Finset.Icc 2 N, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)
          ≤ 2 * (Real.log p / (p : ℝ) ^ 2) := by
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_Icc.1 hp).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp2
      have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hp1R : (1 : ℝ) ≤ (p : ℝ) := by linarith
      have hple : ∀ k : ℕ, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤ Real.log p * (1 / (p : ℝ)) ^ k := by
        intro k
        have hlam : Λ (p ^ k) ≤ Real.log p := by
          rw [vonMangoldt_apply]
          split_ifs with h
          · refine Real.log_le_log (by exact_mod_cast Nat.minFac_pos (p ^ k)) ?_
            have hk0 : k ≠ 0 := by
              rintro rfl
              rw [pow_zero] at h
              exact not_isPrimePow_one h
            exact_mod_cast Nat.minFac_le_of_dvd hp2 (dvd_pow_self p hk0)
          · exact Real.log_nonneg hp1R
        have hcast : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; ring
        rw [hcast, div_le_iff₀ (pow_pos hp0 k)]
        have hid : Real.log p * (1 / (p : ℝ)) ^ k * (p : ℝ) ^ k = Real.log p := by
          rw [div_pow, one_pow]
          field_simp
        rw [hid]
        exact hlam
      calc ∑ k ∈ Finset.Icc 2 N, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)
          ≤ ∑ k ∈ Finset.Icc 2 N, Real.log p * (1 / (p : ℝ)) ^ k :=
            Finset.sum_le_sum fun k _ => hple k
        _ = Real.log p * ∑ k ∈ Finset.Icc 2 N, (1 / (p : ℝ)) ^ k := by rw [Finset.mul_sum]
        _ ≤ Real.log p * (2 * (1 / (p : ℝ)) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg hp1R)
            refine geom_tail_le (by positivity) ?_ N
            rw [div_le_div_iff₀ hp0 (by norm_num)]
            linarith
        _ = 2 * (Real.log p / (p : ℝ) ^ 2) := by
            rw [div_pow, one_pow]
            ring
    calc ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)
        ≤ ∑ p ∈ Finset.Icc 2 N, 2 * (Real.log p / (p : ℝ) ^ 2) := Finset.sum_le_sum hinner
      _ = 2 * ∑ p ∈ Finset.Icc 2 N, Real.log p / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 8 := by linarith [sum_log_div_sq_le N]
  calc ∑ n ∈ S, Λ n / n = _ := hstep1
    _ ≤ _ := hstep2
    _ ≤ 8 := hstep3

/-- The prime-power correction: `0 ≤ ∑_{n ≤ x} Λ(n)/n − ∑_{p ≤ x} log p / p ≤ 8`. -/
lemma mertensSum_sub_primeLogSum_bounds (x : ℝ) :
    0 ≤ mertensSum x - primeLogSum x ∧ mertensSum x - primeLogSum x ≤ 8 := by
  classical
  set N := ⌊x⌋₊ with hN
  have hsplit : mertensSum x
      = primeLogSum x + ∑ n ∈ {n ∈ Finset.Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime}, Λ n / n := by
    unfold mertensSum primeLogSum
    rw [← hN, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) Nat.Prime]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2]
    · rw [← Finset.sum_filter_add_sum_filter_not
        ({n ∈ Finset.Ioc 0 N | ¬ n.Prime}) IsPrimePow]
      have hzero : ∑ n ∈ {n ∈ {n ∈ Finset.Ioc 0 N | ¬ n.Prime} | ¬ IsPrimePow n}, Λ n / n = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        have : ¬ IsPrimePow n := (Finset.mem_filter.1 hn).2
        rw [vonMangoldt_apply, if_neg this, zero_div]
      rw [hzero, add_zero]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext n
      simp only [Finset.mem_filter]
      tauto
  have hnonneg : 0 ≤ ∑ n ∈ {n ∈ Finset.Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime}, Λ n / n :=
    Finset.sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (by positivity)
  have hle := properPrimePower_sum_le N
  constructor <;> rw [hsplit] <;> linarith

/-- **Mertens' theorem, prime form**: `∑_{p ≤ x} log p / p = log x + O(1)`, with the explicit
bound `|∑_{p ≤ x} log p/p − log x| ≤ log 4 + 12 + log 2` for `x ≥ 1`. -/
theorem mertens_first_prime {x : ℝ} (hx : 1 ≤ x) :
    |primeLogSum x - Real.log x| ≤ Real.log 4 + 12 + Real.log 2 := by
  obtain ⟨h0, h8⟩ := mertensSum_sub_primeLogSum_bounds x
  have hm := mertens_first hx
  rw [abs_le] at hm ⊢
  constructor <;> linarith [hm.1, hm.2]

/-- `∑_{n ≤ x} Λ(n)/n − log x` is bounded, i.e. `O(1)`. -/
theorem mertens_first_isBigO :
    (fun x : ℝ => mertensSum x - Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 4 + Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using mertens_first hx

/-- `∑_{p ≤ x} log p / p − log x` is bounded, i.e. `O(1)`. -/
theorem mertens_first_prime_isBigO :
    (fun x : ℝ => primeLogSum x - Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 12 + Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using mertens_first_prime hx

end RiemannHypothesis
