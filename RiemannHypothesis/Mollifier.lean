/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib
import RiemannHypothesis.MertensSums

/-!
# The mollifier identity

The zero-detection step of the density method rests on the following identity.  Let

`M_y(s) = ∑_{n ≤ y} μ(n) n^{-s}`

be the Möbius mollifier of length `y`.  Multiplying the Dirichlet series of `ζ` by `M_y` produces
the Dirichlet series whose `n`-th coefficient is

`c_n = ∑_{d ∣ n, d ≤ y} μ(d)`,

and the point is that these coefficients *vanish in the initial range*: `c_1 = 1` and `c_n = 0`
for `2 ≤ n ≤ y`, because for such `n` every divisor of `n` is at most `y`, so `c_n` is the full
divisor sum `∑_{d ∣ n} μ(d) = 0`.  Hence

`ζ(s) M_y(s) = 1 + ∑_{n > y} c_n n^{-s}`,

so at a zero of `ζ` the tail Dirichlet polynomial must take the value `−1`: a zero has been
converted into a *large value* of a Dirichlet series with no short terms.

## Main results

* `RiemannHypothesis.Mollifier.mollifier` — the Möbius mollifier `M_y(s) = ∑_{n ≤ y} μ(n) n^{-s}`.
* `RiemannHypothesis.Mollifier.detectCoeff` — the coefficients `c_n = ∑_{d ∣ n, d ≤ y} μ(d)`.
* `RiemannHypothesis.Mollifier.detectCoeff_one`, `detectCoeff_eq_zero_of_le` — the vanishing of
  the coefficients in the initial range, `c_1 = 1` and `c_n = 0` for `2 ≤ n ≤ y`.  This is the
  combinatorial heart of zero detection, and it holds for every `s`.
* `RiemannHypothesis.Mollifier.zeta_mul_mollifier` — `ζ(s) M_y(s)` is the L-series of the
  coefficients `c_n`, for `re s > 1`.
* `RiemannHypothesis.Mollifier.zeta_mul_mollifier_eq_one_add_tail` — **the mollifier identity**
  `ζ(s) M_y(s) = 1 + ∑_{n > y} c_n n^{-s}`, for `re s > 1`.
* `RiemannHypothesis.Mollifier.LSeries_tailCoeff_eq` — the zero-detection statement in the region
  of convergence: the tail equals `ζ(s) M_y(s) − 1`, hence `−1` at a zero of `ζ`.
* `RiemannHypothesis.Mollifier.mollified_partialSum`,
  `RiemannHypothesis.Mollifier.mollified_partialSum_eq_one_add_tail` — a *finite* mollifier
  identity, valid for every `s` with no convergence hypothesis: the product of the mollifier with
  a partial sum of `ζ` is a Dirichlet polynomial whose coefficients vanish for `2 ≤ m ≤ min y K`,
  so it equals `1` plus a Dirichlet polynomial supported on `m > y`.

## Scope

The identity is proved in the half-plane of absolute convergence `re s > 1`, where the Dirichlet
series of `ζ` converges; `ζ` has no zeroes there, so the detection statement
`LSeries_tailCoeff_eq` has no content as a zero-detection statement by itself.  Carrying the
identity into the critical strip, where it is applied, requires replacing the infinite tail by a
finite Dirichlet polynomial with an explicit error term (an approximate functional equation or a
contour shift); that is not done here, and no density estimate follows from this file.  The
finite identity `mollified_partialSum` does hold for all `s`, but on its own it carries no
information about `ζ` outside the region of convergence.
-/

open Finset Complex ArithmeticFunction

namespace RiemannHypothesis

namespace Mollifier

open scoped ArithmeticFunction.Moebius

/-- The truncated Möbius coefficients: `μ(n)` for `1 ≤ n ≤ y`, and `0` beyond. -/
noncomputable def mollCoeff (y n : ℕ) : ℂ := if n ≤ y then (μ n : ℂ) else 0

/-- The Möbius mollifier `M_y(s) = ∑_{n ≤ y} μ(n) n^{-s}`. -/
noncomputable def mollifier (y : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, (μ n : ℂ) * (n : ℂ) ^ (-s)

/-- The coefficients of `ζ M_y`: `c_n = ∑_{d ∣ n, d ≤ y} μ(d)`. -/
noncomputable def detectCoeff (y n : ℕ) : ℂ := ∑ d ∈ n.divisors.filter (fun d => d ≤ y), (μ d : ℂ)

/-- The tail coefficients of `ζ M_y`, i.e. those of `ζ M_y − 1`; they are supported on `n > y`. -/
noncomputable def tailCoeff (y n : ℕ) : ℂ := if y < n then detectCoeff y n else 0

/-! ## The mollifier as an L-series -/

theorem mollCoeff_eq_zero {y n : ℕ} (hn : n ∉ Finset.Icc 1 y) : mollCoeff y n = 0 := by
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with h | h
  · have hn0 : n = 0 := by omega
    simp [mollCoeff, hn0]
  · simp [mollCoeff, h]

theorem LSeriesSummable_mollCoeff (y : ℕ) (s : ℂ) : LSeriesSummable (mollCoeff y) s := by
  refine summable_of_ne_finset_zero (s := Finset.Icc 1 y) fun n hn => ?_
  simp [LSeries.term, mollCoeff_eq_zero hn]

theorem LSeries_mollCoeff (y : ℕ) (s : ℂ) : LSeries (mollCoeff y) s = mollifier y s := by
  rw [LSeries, tsum_eq_sum (s := Finset.Icc 1 y) fun n hn => by
    simp [LSeries.term, mollCoeff_eq_zero hn]]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hny : n ≤ y := (Finset.mem_Icc.mp hn).2
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0, mollCoeff, if_pos hny, Complex.cpow_neg, div_eq_mul_inv]

/-! ## The coefficients of `ζ M_y` -/

theorem convolution_one_mollCoeff (y n : ℕ) :
    LSeries.convolution (1 : ℕ → ℂ) (mollCoeff y) n = detectCoeff y n := by
  classical
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, one_mul]
  rw [Nat.sum_divisorsAntidiagonal (f := fun _ b => mollCoeff y b),
    Nat.sum_div_divisors n (fun d => mollCoeff y d), detectCoeff, Finset.sum_filter]
  exact Finset.sum_congr rfl fun d _ => rfl

theorem detectCoeff_one {y : ℕ} (hy : 1 ≤ y) : detectCoeff y 1 = 1 := by
  classical
  rw [detectCoeff, Nat.divisors_one]
  rw [Finset.filter_true_of_mem (by intro d hd; simp only [Finset.mem_singleton] at hd; omega)]
  simp

theorem detectCoeff_eq_zero_of_le {y n : ℕ} (hn : 2 ≤ n) (hny : n ≤ y) : detectCoeff y n = 0 := by
  classical
  have hfilter : n.divisors.filter (fun d => d ≤ y) = n.divisors := by
    refine Finset.filter_true_of_mem fun d hd => ?_
    have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
    omega
  have hsum : ∑ d ∈ n.divisors, (μ d : ℤ) = 0 := by
    rw [sum_divisors_moebius, if_neg (by omega)]
  rw [detectCoeff, hfilter]
  have : ∑ d ∈ n.divisors, ((μ d : ℤ) : ℂ) = ((∑ d ∈ n.divisors, (μ d : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [this, hsum]
  simp

/-! ## The identity -/

theorem LSeriesSummable_delta (s : ℂ) : LSeriesSummable LSeries.delta s := by
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [LSeries.term_delta, hn]

theorem zeta_mul_mollifier (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mollifier y s = LSeries (detectCoeff y) s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have h2 : LSeriesSummable (mollCoeff y) s := LSeriesSummable_mollCoeff y s
  have hconv : LSeries (LSeries.convolution (1 : ℕ → ℂ) (mollCoeff y)) s
      = LSeries (1 : ℕ → ℂ) s * LSeries (mollCoeff y) s := LSeries_convolution' h1 h2
  rw [LSeries_one_eq_riemannZeta hs, LSeries_mollCoeff] at hconv
  rw [← hconv]
  exact LSeries_congr (fun {n} _ => convolution_one_mollCoeff y n) s

theorem detectCoeff_eq_delta_add_tail {y : ℕ} (hy : 1 ≤ y) (n : ℕ) :
    detectCoeff y n = LSeries.delta n + tailCoeff y n := by
  classical
  rcases Nat.lt_or_ge y n with h | h
  · have hn1 : n ≠ 1 := by omega
    simp [tailCoeff, h, LSeries.delta, hn1]
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [detectCoeff, tailCoeff, LSeries.delta]
    · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0)) with h1 | h2
      · simp [← h1, detectCoeff_one hy, tailCoeff, LSeries.delta, show y ≠ 0 by omega]
      · have hyn : ¬ y < n := by omega
        simp [tailCoeff, hyn, LSeries.delta, detectCoeff_eq_zero_of_le h2 h,
          show n ≠ 1 by omega]

theorem LSeriesSummable_detectCoeff (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (detectCoeff y) s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have h2 : LSeriesSummable (mollCoeff y) s := LSeriesSummable_mollCoeff y s
  have h := h1.convolution h2
  exact (LSeriesSummable_congr s fun {n} _ => (convolution_one_mollCoeff y n)).mp h

theorem LSeriesSummable_tailCoeff {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (tailCoeff y) s := by
  have hd : LSeriesSummable (detectCoeff y) s := LSeriesSummable_detectCoeff y hs
  have hsub := hd.sub (LSeriesSummable_delta s)
  refine (LSeriesSummable_congr s (f := fun n => detectCoeff y n - LSeries.delta n) ?_).mp hsub
  intro n _
  rw [detectCoeff_eq_delta_add_tail hy n]
  ring

/-- **The mollifier identity**: for `re s > 1`,
`ζ(s) M_y(s) = 1 + ∑_{n > y} (∑_{d ∣ n, d ≤ y} μ(d)) n^{-s}`. -/
theorem zeta_mul_mollifier_eq_one_add_tail {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mollifier y s = 1 + LSeries (tailCoeff y) s := by
  have htail : LSeriesSummable (tailCoeff y) s := LSeriesSummable_tailCoeff hy hs
  have hsplit : LSeries (detectCoeff y) s = LSeries LSeries.delta s + LSeries (tailCoeff y) s := by
    rw [← LSeries_add (LSeriesSummable_delta s) htail]
    exact LSeries_congr (fun {n} _ => detectCoeff_eq_delta_add_tail hy n) s
  rw [zeta_mul_mollifier y hs, hsplit, LSeries_delta]
  simp

/-- **Zero detection**, in the half-plane of absolute convergence.  The tail Dirichlet series,
which has no terms of index `≤ y`, equals `ζ(s) M_y(s) − 1`; in particular it takes the value
`−1` at any zero of `ζ`.  (Zeroes are what one wants to apply this to, and they all lie in
`re s ≤ 1`, so making the statement useful requires carrying the identity into the critical
strip, which is not done here.) -/
theorem LSeries_tailCoeff_eq {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    LSeries (tailCoeff y) s = riemannZeta s * mollifier y s - 1 := by
  rw [zeta_mul_mollifier_eq_one_add_tail hy hs]
  ring

/-! ## A finite mollifier identity, valid for every `s`

The identity above lives in the half-plane of absolute convergence.  Truncating the Dirichlet
series of `ζ` at `K` gives an identity between *finite* sums, which therefore holds for every
complex `s`, with no convergence hypothesis:

`(∑_{d ≤ y} μ(d) d^{-s}) (∑_{k ≤ K} k^{-s}) = ∑_{m ≤ yK} c_{y,K}(m) m^{-s}`,

where `c_{y,K}(m) = ∑_{d ∣ m, d ≤ y, m/d ≤ K} μ(d)`.  The coefficients again vanish in the
initial range: `c_{y,K}(1) = 1` and `c_{y,K}(m) = 0` for `2 ≤ m ≤ min y K`.
-/

/-- The coefficients of the mollified partial sum:
`c_{y,K}(m) = ∑_{d ∣ m, d ≤ y, m/d ≤ K} μ(d)`. -/
noncomputable def finiteDetectCoeff (y K m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K), (μ d : ℂ)

theorem finiteDetectCoeff_one {y K : ℕ} (hy : 1 ≤ y) (hK : 1 ≤ K) :
    finiteDetectCoeff y K 1 = 1 := by
  classical
  rw [finiteDetectCoeff, Nat.divisors_one, Finset.filter_true_of_mem]
  · simp
  · intro d hd
    simp only [Finset.mem_singleton] at hd
    subst hd
    exact ⟨hy, by simpa using hK⟩

/-- The coefficients of the mollified partial sum vanish in the initial range `2 ≤ m ≤ min y K`.
This is the zero-detection mechanism in its purely combinatorial form. -/
theorem finiteDetectCoeff_eq_zero_of_le {y K m : ℕ} (hm : 2 ≤ m) (hmy : m ≤ y) (hmK : m ≤ K) :
    finiteDetectCoeff y K m = 0 := by
  classical
  have hfilter : m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K) = m.divisors := by
    refine Finset.filter_true_of_mem fun d hd => ?_
    have hdm := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
    exact ⟨by omega, le_trans (Nat.div_le_self m d) (by omega)⟩
  have hsum : ∑ d ∈ m.divisors, (μ d : ℤ) = 0 := by
    rw [sum_divisors_moebius, if_neg (by omega)]
  rw [finiteDetectCoeff, hfilter]
  have hcast : ∑ d ∈ m.divisors, ((μ d : ℤ) : ℂ) = ((∑ d ∈ m.divisors, (μ d : ℤ) : ℤ) : ℂ) := by
    push_cast; ring
  rw [hcast, hsum]
  simp

theorem natCast_mul_cpow_neg (d k : ℕ) (s : ℂ) :
    ((d * k : ℕ) : ℂ) ^ (-s) = (d : ℂ) ^ (-s) * (k : ℂ) ^ (-s) := by
  rw [Nat.cast_mul, ← Complex.ofReal_natCast d, ← Complex.ofReal_natCast k,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]

theorem sum_moebius_fiber_eq (y K m : ℕ) (hm : 1 ≤ m) :
    ∑ p ∈ (Finset.Icc 1 y ×ˢ Finset.Icc 1 K) with p.1 * p.2 = m, (μ p.1 : ℂ)
      = finiteDetectCoeff y K m := by
  classical
  refine Finset.sum_nbij' (i := fun p => p.1) (j := fun d => (d, m / d)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, hdy⟩, hk1, hkK⟩, hdk⟩ := hp
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨k, hdk.symm⟩, by omega⟩, hdy, ?_⟩
    rw [← hdk, Nat.mul_div_cancel_left _ (by omega)]
    exact hkK
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, hm0⟩, hdy, hdK⟩ := hd
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hmd : 1 ≤ m / d := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdvd)
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hd1, hdy⟩, hmd, hdK⟩, Nat.mul_div_cancel' hdvd⟩
  · rintro ⟨d, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, hdy⟩, hk1, hkK⟩, hdk⟩ := hp
    simp only [Prod.mk.injEq, true_and]
    rw [← hdk, Nat.mul_div_cancel_left _ (by omega)]
  · intro d _
    rfl
  · intro p _
    rfl

/-- **The finite mollifier identity.**  For every complex `s` (no convergence hypothesis), the
Möbius mollifier of length `y` times the partial sum `∑_{k ≤ K} k^{-s}` of `ζ` is the Dirichlet
polynomial with coefficients `c_{y,K}(m) = ∑_{d ∣ m, d ≤ y, m/d ≤ K} μ(d)`, which vanish for
`2 ≤ m ≤ min y K` by `finiteDetectCoeff_eq_zero_of_le`. -/
theorem mollified_partialSum (y K : ℕ) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 y, (μ d : ℂ) * (d : ℂ) ^ (-s)) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = ∑ m ∈ Finset.Icc 1 (y * K), finiteDetectCoeff y K m * (m : ℂ) ^ (-s) := by
  classical
  have hmaps : ∀ p ∈ Finset.Icc 1 y ×ˢ Finset.Icc 1 K, p.1 * p.2 ∈ Finset.Icc 1 (y * K) := by
    rintro ⟨d, k⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hp.1.2 hp.2.2⟩
  have key := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => (μ p.1 : ℂ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-s))
  have hprod : (∑ d ∈ Finset.Icc 1 y, (μ d : ℂ) * (d : ℂ) ^ (-s)) *
      (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = ∑ p ∈ Finset.Icc 1 y ×ˢ Finset.Icc 1 K, (μ p.1 : ℂ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [natCast_mul_cpow_neg]; ring
  rw [hprod, ← key]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_Icc] at hm
  rw [← sum_moebius_fiber_eq y K m hm.1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  rw [hp.2]

/-- The mollified partial sum, written so that the short terms are visible: for `1 ≤ y ≤ K`,
`M_y(s) ∑_{k ≤ K} k^{-s} = 1 + ∑_{y < m ≤ yK} c_{y,K}(m) m^{-s}`.  This holds for every `s`; it
is the finite, unconditional form of zero detection. -/
theorem mollified_partialSum_eq_one_add_tail {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 y, (μ d : ℂ) * (d : ℂ) ^ (-s)) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = 1 + ∑ m ∈ Finset.Ioc y (y * K), finiteDetectCoeff y K m * (m : ℂ) ^ (-s) := by
  classical
  have hyyK : y ≤ y * K := Nat.le_mul_of_pos_right y (by omega)
  have hIcc : Finset.Icc 1 (y * K) = Finset.Ioc 0 (y * K) := by ext m; simp [Finset.mem_Icc]; omega
  rw [mollified_partialSum y K s, hIcc,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) hyyK]
  congr 1
  have hshort : Finset.Ioc 0 y = Finset.Icc 1 y := by ext m; simp [Finset.mem_Icc]; omega
  rw [hshort, Finset.sum_eq_single 1]
  · rw [finiteDetectCoeff_one hy (le_trans hy hyK)]
    simp
  · intro m hm hm1
    have hm' := Finset.mem_Icc.mp hm
    rw [finiteDetectCoeff_eq_zero_of_le (by omega) hm'.2 (le_trans hm'.2 hyK), zero_mul]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hy⟩) h

end Mollifier

end RiemannHypothesis
