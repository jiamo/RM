/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AbelDirichlet
import RiemannHypothesis.LiouvilleFunction
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The Liouville criterion

This is a fifth route to the Riemann hypothesis.  Let `λ` be the Liouville function,
`λ(n) = (-1)^Ω(n)`, and let

`L(N) = ∑_{n ≤ N} λ(n)`   (`liouvilleSummatory`).

If `L(N) = O(N^{1/2+ε})` for every `ε > 0` (`LiouvilleBoundForm`) then the Riemann hypothesis
holds (`zeta_of_liouvilleBound`).

## The argument

The arithmetic input is the classical identity

`∑_{d ∣ n} λ(d) = 1` if `n` is a square and `0` otherwise

(`zeta_mul_liouvilleAF`), proved here from multiplicativity by checking prime powers, where
it reduces to `∑_{j ≤ k} (-1)^j`.  Summing the resulting Dirichlet series over squares gives

`ζ(s) · L(λ, s) = ζ(2s)`   for `re s > 1`.

On the other hand the hypothesis `L(N) = O(N^{1/2+ε})` makes the Abel-summed series of `λ`
holomorphic on `re s > 1/2` (`RiemannHypothesis.AbelDirichlet`).  Hence

`(s-1) ζ(s) · F(s) = (s-1) ζ(2s)`

extends from `re s > 1` to the convex half-plane `re s > 1/2`.  A zero of `ζ` at `s` with
`re s > 1/2`, `s ≠ 1` would make the left side vanish, forcing `ζ(2s) = 0` — impossible,
since `re (2s) > 1`.
-/

noncomputable section

open Complex Filter Finset ArithmeticFunction
open scoped Topology

namespace RiemannHypothesis

/-! ## Squares and factorizations -/

lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  have hprod : (n.factorization.prod fun p k => p ^ (k / 2))
      * (n.factorization.prod fun p k => p ^ (k / 2))
      = n.factorization.prod fun p k => p ^ k := by
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨m, hm⟩ := h p
    omega
  rw [hprod, Nat.prod_factorization_pow_eq_self hn]

lemma isSquare_iff_factorization_even {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  refine ⟨?_, isSquare_of_factorization_even hn⟩
  rintro ⟨m, rfl⟩ p
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.factorization_mul hm0 hm0]
  exact ⟨m.factorization p, by simp⟩

lemma isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact pow_ne_zero k hp.pos.ne' hm
    have hcong := congrArg (fun x => Nat.factorization x p) hm
    simp only [Nat.Prime.factorization_pow hp, Nat.factorization_mul hm0 hm0] at hcong
    simp at hcong
    exact ⟨m.factorization p, by omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, by rw [← pow_add]⟩

lemma isSquare_mul_iff_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [isSquare_iff_factorization_even hmn, isSquare_iff_factorization_even hm,
    isSquare_iff_factorization_even hn]
  constructor
  · intro hall
    refine ⟨fun p => ?_, fun p => ?_⟩
    · rcases Nat.eq_zero_or_pos (n.factorization p) with hp | hp
      · have hpm := hall p
        rw [Nat.factorization_mul hm hn] at hpm
        simpa [hp] using hpm
      · have hpn : p ∣ n := Nat.dvd_of_factorization_pos (by omega)
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
          rw [h] at hd
          simp [Nat.dvd_one.mp hd] at hp
        simp [Nat.factorization_eq_zero_of_not_dvd hpm]
    · rcases Nat.eq_zero_or_pos (m.factorization p) with hp | hp
      · have hpn := hall p
        rw [Nat.factorization_mul hm hn] at hpn
        simpa [hp] using hpn
      · have hpm : p ∣ m := Nat.dvd_of_factorization_pos (by omega)
        have hpn : ¬ p ∣ n := by
          intro hpn
          have hd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
          rw [h] at hd
          simp [Nat.dvd_one.mp hd] at hp
        simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  · rintro ⟨h1, h2⟩ p
    rw [Nat.factorization_mul hm hn]
    exact (h1 p).add (h2 p)

/-! ## The arithmetic identity `ζ ⍟ λ = 1_{squares}` -/

open scoped Classical in
/-- The indicator function of the nonzero squares, as a complex arithmetic function. -/
def sqAF : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

/-- The Liouville function as a complex arithmetic function. -/
def liouvilleAF : ArithmeticFunction ℂ := (liouville : ArithmeticFunction ℤ)

open scoped Classical in
lemma sqAF_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    sqAF n = if IsSquare n then 1 else 0 := by
  simp only [sqAF, ArithmeticFunction.coe_mk, hn, ne_eq, not_false_eq_true, true_and]

lemma liouvilleAF_apply {n : ℕ} (hn : n ≠ 0) :
    liouvilleAF n = (-1 : ℂ) ^ ArithmeticFunction.cardFactors n := by
  simp only [liouvilleAF, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.liouville_apply hn]
  push_cast
  ring

lemma norm_liouvilleAF_le (n : ℕ) : ‖liouvilleAF n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [liouvilleAF]
  · rw [liouvilleAF_apply hn]
    simp

open scoped Classical in
lemma isMultiplicative_sqAF : ArithmeticFunction.IsMultiplicative sqAF := by
  constructor
  · simp [sqAF]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [sqAF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [sqAF]
    have hiff : (m * n ≠ 0 ∧ IsSquare (m * n))
        ↔ ((m ≠ 0 ∧ IsSquare m) ∧ (n ≠ 0 ∧ IsSquare n)) := by
      constructor
      · rintro ⟨-, hsq⟩
        obtain ⟨h1, h2⟩ := (isSquare_mul_iff_of_coprime hm hn hmn).mp hsq
        exact ⟨⟨hm, h1⟩, ⟨hn, h2⟩⟩
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
        exact ⟨Nat.mul_ne_zero hm hn, (isSquare_mul_iff_of_coprime hm hn hmn).mpr ⟨h1, h2⟩⟩
    simp only [sqAF, ArithmeticFunction.coe_mk]
    rw [if_congr hiff rfl rfl]
    by_cases h1 : m ≠ 0 ∧ IsSquare m <;> by_cases h2 : n ≠ 0 ∧ IsSquare n <;> simp [h1, h2]

/-- **`∑_{d ∣ n} λ(d)` is the indicator of the squares.** -/
lemma zeta_mul_liouvilleAF :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) * liouvilleAF
      = sqAF := by
  classical
  have hmulL : ArithmeticFunction.IsMultiplicative liouvilleAF :=
    isMultiplicative_liouville.intCast
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_zeta.natCast.mul hmulL) _ isMultiplicative_sqAF).mpr ?_
  intro p k hp
  have hp0 : p ≠ 0 := hp.pos.ne'
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  have hlp : ∀ j : ℕ, liouvilleAF (p ^ j) = (-1 : ℂ) ^ j := by
    intro j
    rw [liouvilleAF_apply (pow_ne_zero j hp0)]
    congr 1
    simp [ArithmeticFunction.cardFactors_apply_prime_pow hp]
  simp only [hlp]
  simp only [sqAF, ArithmeticFunction.coe_mk, isSquare_prime_pow_iff hp, ne_eq]
  rw [neg_one_geom_sum]
  by_cases hk : Even k
  · simp [hk, Nat.even_add_one, hp0]
  · simp [hk, Nat.even_add_one, hp0]

/-! ## The L-series identity `ζ(s) · L(λ,s) = ζ(2s)` -/

lemma lSeriesSummable_liouvilleAF {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => liouvilleAF n) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_liouvilleAF_le n) hs

lemma lSeriesSummable_zetaAF {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) s :=
  ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs

open scoped Classical in
/-- The L-series of the indicator of the squares is `ζ(2s)`. -/
lemma lSeries_sqAF {s : ℂ} (hs : 1 < (2 * s).re) :
    LSeries (fun n => sqAF n) s = riemannZeta (2 * s) := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := fun a b h => by
    simpa using Nat.pow_left_injective (by norm_num) h
  have hsupp : Function.support (LSeries.term (fun n => sqAF n) s) ⊆
      Set.range (fun m : ℕ => m ^ 2) := by
    intro n hn
    simp only [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term] at hn
    have hval : sqAF n ≠ 0 := by
      intro h
      rw [LSeries.term_of_ne_zero hn0, h, zero_div] at hn
      exact hn rfl
    have hsq : n ≠ 0 ∧ IsSquare n := by
      by_contra hc
      simp only [sqAF, ArithmeticFunction.coe_mk, if_neg hc] at hval
      exact hval rfl
    obtain ⟨r, hr⟩ := hsq.2
    exact ⟨r, by rw [hr]; ring⟩
  have hterm : ∀ m : ℕ, LSeries.term (fun n => sqAF n) s (m ^ 2)
      = LSeries.term (1 : ℕ → ℂ) (2 * s) m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term]
    have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm]
    have hsq : sqAF (m ^ 2) = 1 := by
      simp only [sqAF, ArithmeticFunction.coe_mk]
      rw [if_pos ⟨hm2, ⟨m, by ring⟩⟩]
    rw [hsq]
    congr 1
    rw [show ((m ^ 2 : ℕ) : ℂ) = (m : ℂ) ^ (2 : ℕ) by push_cast; ring,
      ← Complex.cpow_natCast (m : ℂ) 2, ← Complex.cpow_mul]
    · push_cast
      ring_nf
    · simp [Complex.log_im, Real.pi_pos]
    · simp [Complex.log_im, Real.pi_pos.le]
  rw [LSeries, ← hinj.tsum_eq hsupp]
  simp only [hterm]
  rw [← LSeries, LSeries_one_eq_riemannZeta hs]

/-- For `re s > 1`, `ζ(s) · L(λ, s) = ζ(2s)`. -/
lemma riemannZeta_mul_lSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * LSeries (fun n => liouvilleAF n) s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by
    rw [show (2 * s).re = 2 * s.re by simp]
    linarith
  have hmul := ArithmeticFunction.LSeries_mul'
    (f := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
    (g := liouvilleAF) (s := s) (lSeriesSummable_zetaAF hs) (lSeriesSummable_liouvilleAF hs)
  have hz : LSeries
      (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) s
      = riemannZeta s := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun _ => ArithmeticFunction.natCoe_apply) s
  rw [zeta_mul_liouvilleAF, lSeries_sqAF h2s, hz] at hmul
  exact hmul.symm

/-! ## The criterion -/

/-- The Liouville function as a complex-valued sequence. -/
def liouvilleC : ℕ → ℂ := fun n => liouvilleAF n

/-- The summatory Liouville function `L(N) = ∑_{n ≤ N} λ(n)`. -/
def liouvilleSummatory (N : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 N, liouville n

/-- **The Liouville bound**: `L(N) = O(N^{1/2+ε})` for every `ε > 0`. -/
def LiouvilleBoundForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
    |(liouvilleSummatory N : ℝ)| ≤ C * (N : ℝ) ^ (1 / 2 + ε)

/-- The Abel-summed Dirichlet series of the Liouville function. -/
def liouvilleAbel (s : ℂ) : ℂ := abelSum liouvilleC s

lemma partialSum_liouvilleC (N : ℕ) :
    partialSum liouvilleC N = ((liouvilleSummatory N : ℤ) : ℂ) := by
  simp [partialSum, liouvilleC, liouvilleAF, liouvilleSummatory]

lemma norm_partialSum_liouvilleC (N : ℕ) :
    ‖partialSum liouvilleC N‖ = |(liouvilleSummatory N : ℝ)| := by
  rw [partialSum_liouvilleC,
    show ((liouvilleSummatory N : ℤ) : ℂ) = (((liouvilleSummatory N : ℤ) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

lemma sqrtCancellation_liouvilleC (hL : LiouvilleBoundForm) : SqrtCancellation liouvilleC := by
  intro ε hε
  obtain ⟨C, hC⟩ := hL ε hε
  exact ⟨C, fun N => by rw [norm_partialSum_liouvilleC]; exact hC N⟩

lemma differentiableOn_liouvilleAbel (hL : LiouvilleBoundForm) :
    DifferentiableOn ℂ liouvilleAbel {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_abelSum_of_sqrtCancellation (sqrtCancellation_liouvilleC hL)

lemma liouvilleAbel_eq (hL : LiouvilleBoundForm) {s : ℂ} (hs : 1 < s.re) :
    liouvilleAbel s = LSeries (fun n => liouvilleAF n) s :=
  abelSum_eq_LSeries_of_sqrtCancellation (sqrtCancellation_liouvilleC hL) (by linarith)
    (lSeriesSummable_liouvilleAF hs)

/-- **The Liouville criterion**: if `∑_{n ≤ N} λ(n) = O(N^{1/2+ε})` for every `ε > 0`, then the
Riemann hypothesis holds. -/
theorem zeta_of_liouvilleBound (hL : LiouvilleBoundForm) : ZetaForm := by
  refine zeta_iff_zeta_strip.mpr (zeta_strip_iff_nonvanishing_right.mpr ?_)
  intro s hs hs1 hzero
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hre2 : ∀ z ∈ U, 1 < (2 * z).re := by
    intro z hz
    have hzre : (1 : ℝ) / 2 < z.re := hz
    rw [show (2 * z).re = 2 * z.re by simp]
    linarith
  have hG : AnalyticOnNhd ℂ (fun z => zetaPoleFree z * liouvilleAbel z) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    exact (differentiable_zetaPoleFree.differentiableOn).mul (differentiableOn_liouvilleAbel hL)
  have hH : AnalyticOnNhd ℂ (fun z : ℂ => (z - 1) * riemannZeta (2 * z)) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro z hz
    have h2 : (2 : ℂ) * z ≠ 1 := by
      intro h
      have := hre2 z hz
      rw [h] at this
      simp at this
    have hzeta : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (2 * w)) z :=
      (differentiableAt_riemannZeta h2).comp z (by fun_prop)
    exact (((differentiableAt_id.sub_const 1).mul hzeta)).differentiableWithinAt
  have hmem2 : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : (fun z => zetaPoleFree z * liouvilleAbel z) =ᶠ[nhds (2 : ℂ)]
      fun z : ℂ => (z - 1) * riemannZeta (2 * z) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    have hz1 : (1 : ℝ) < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      simp at hz1
    rw [zetaPoleFree_of_ne_one hzne, liouvilleAbel_eq hL hz1, mul_assoc,
      riemannZeta_mul_lSeries_liouville hz1]
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq hH hUconn hmem2 hev
  have hsU : s ∈ U := hs
  have hval := heq hsU
  simp only at hval
  rw [zetaPoleFree_of_ne_one hs1, hzero, mul_zero, zero_mul] at hval
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (hre2 s hsU).le
  exact hz2 (by
    rcases mul_eq_zero.mp hval.symm with h | h
    · exact absurd (by linear_combination h) hs1
    · exact h)

end RiemannHypothesis

end
