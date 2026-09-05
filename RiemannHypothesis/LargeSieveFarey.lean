/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieveGallagher

/-!
# The arithmetic large sieve: exponential sums at Farey fractions

`RiemannHypothesis.LargeSieveGallagher` proves the analytic large sieve

`∑_r ‖∑_{n < N} a n e(n t r)‖² ≤ (δ⁻¹ + π N) ∑_{n < N} ‖a n‖²`

for points `t r` that are `δ`-separated modulo one.  This file specializes it to the classical
set of points: the *Farey fractions* `b / q` with `q ≤ Q`.  Two distinct such fractions in
`[0, 1)` differ by a nonzero rational whose denominator is at most `Q²`, hence by at least
`Q⁻²`, so the Farey fractions of order `Q` are `Q⁻²`-separated and the large sieve gives

`∑_{q ≤ Q} ∑_{b mod q, (b,q) = 1} ‖∑_{n < N} a n e(n b / q)‖² ≤ (Q² + π N) ∑_{n < N} ‖a n‖².`

## Main results

* `one_div_den_le_intDist` — a rational that is not an integer is at distance at least
  `1 / den` from the integers.
* `inv_sq_le_intDist_sub` — two distinct rationals in `[0, 1)` with denominators at most `Q`
  are `Q⁻²`-separated modulo one.
* `large_sieve_farey` — the large sieve over any finite set of rationals in `[0, 1)` with
  denominators at most `Q`.
* `large_sieve_farey_pairs` — **the arithmetic large sieve** in its classical double-sum form,
  over the reduced fractions `b / q` with `1 ≤ q ≤ Q` and `0 ≤ b < q`.
* `card_le_of_large_values_farey` — the number of Farey fractions of order `Q` at which the
  exponential sum is at least `V` in modulus is at most `(Q² + π N) ‖a‖² / V²`.

## Scope

This is the large sieve for exponential sums at rational points; it is *not* the large sieve
for Dirichlet characters (which needs Gauss sums on top of this) and it says nothing about `ζ`.
The constant `Q² + π N` inherits the factor `π` from the Sobolev step of Gallagher's argument;
the sharp constant is `Q² + N − 1`, which needs Selberg's majorant and is not claimed.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveFarey

open KusminLandau LargeSieve LargeSieveGallagher

/-! ## Separation of Farey fractions -/

/-- A nonzero rational is at least `1 / den` in absolute value. -/
theorem one_div_den_le_abs {x : ℚ} (hx : x ≠ 0) : 1 / (x.den : ℚ) ≤ |x| := by
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.pos
  have hnum : (1 : ℤ) ≤ |x.num| := Int.one_le_abs (Rat.num_ne_zero.mpr hx)
  have hq : |x| = (|x.num| : ℚ) / x.den := by
    nth_rewrite 1 [← Rat.num_div_den x]
    rw [abs_div, abs_of_pos hd]
  rw [hq]
  gcongr
  exact_mod_cast hnum

/-- A rational that is not an integer is at distance at least `1 / den` from the integers. -/
theorem one_div_den_le_intDist {x : ℚ} (hx : x.den ≠ 1) : 1 / (x.den : ℝ) ≤ intDist (x : ℝ) := by
  set k : ℤ := round (x : ℝ) with hk
  have hz : x - (k : ℚ) ≠ 0 := by
    intro h
    have : x = (k : ℚ) := by linarith [sub_eq_zero.mp h]
    rw [this] at hx
    simp at hx
  have hdvd : (x - (k : ℚ)).den ∣ x.den := by simp
  have hle : ((x - (k : ℚ)).den : ℝ) ≤ (x.den : ℝ) := by
    have : (x - (k : ℚ)).den ≤ x.den := Nat.le_of_dvd x.pos hdvd
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((x - (k : ℚ)).den : ℝ) := by
    exact_mod_cast (x - (k : ℚ)).pos
  have h1 : 1 / ((x - (k : ℚ)).den : ℚ) ≤ |x - (k : ℚ)| := one_div_den_le_abs hz
  have h2 : 1 / ((x - (k : ℚ)).den : ℝ) ≤ |(x : ℝ) - (k : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    exact this
  have h3 : 1 / (x.den : ℝ) ≤ 1 / ((x - (k : ℚ)).den : ℝ) := by
    apply one_div_le_one_div_of_le hpos hle
  exact h3.trans (h2.trans_eq (by rw [intDist, hk]))

/-- Two distinct rationals in `[0, 1)` with denominators at most `Q` are `Q⁻²`-separated
modulo one. -/
theorem inv_sq_le_intDist_sub {x y : ℚ} {Q : ℕ}
    (hx : x ∈ Set.Ico (0 : ℚ) 1) (hy : y ∈ Set.Ico (0 : ℚ) 1)
    (hxd : x.den ≤ Q) (hyd : y.den ≤ Q) (hxy : x ≠ y) :
    1 / ((Q : ℝ) ^ 2) ≤ intDist ((x : ℝ) - (y : ℝ)) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have habs : |x - y| < 1 := by
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    rw [abs_lt]
    constructor <;> linarith
  have hden1 : (x - y).den ≠ 1 := by
    intro h
    set z : ℚ := x - y with hz
    have h1 : ((z.num : ℚ)) = z := (Rat.den_eq_one_iff z).mp h
    have h2 : (1 : ℤ) ≤ |z.num| := Int.one_le_abs (Rat.num_ne_zero.mpr hsub)
    have : (1 : ℚ) ≤ |z| := by
      rw [← h1, show |((z.num : ℚ))| = ((|z.num| : ℤ) : ℚ) by push_cast [abs_abs]; simp]
      exact_mod_cast h2
    linarith
  have hdvd : (x - y).den ∣ x.den * y.den := Rat.sub_den_dvd x y
  have hle : (x - y).den ≤ Q ^ 2 := by
    have h1 : (x - y).den ≤ x.den * y.den :=
      Nat.le_of_dvd (Nat.mul_pos x.pos y.pos) hdvd
    calc (x - y).den ≤ x.den * y.den := h1
      _ ≤ Q * Q := Nat.mul_le_mul hxd hyd
      _ = Q ^ 2 := by ring
  have key : 1 / (((x - y).den : ℝ)) ≤ intDist ((x : ℝ) - (y : ℝ)) := by
    have := one_div_den_le_intDist hden1
    push_cast at this
    simpa using this
  refine le_trans ?_ key
  apply one_div_le_one_div_of_le
  · exact_mod_cast (x - y).pos
  · exact_mod_cast hle

/-! ## The large sieve at Farey fractions -/

/-- **The large sieve over a set of rationals of bounded denominator.**  For a finite set `s`
of rationals in `[0, 1)` all of whose denominators are at most `Q`,
`∑_{x ∈ s} ‖∑_{n < N} a n e(n x)‖² ≤ (Q² + π N) ∑_{n < N} ‖a n‖²`. -/
theorem large_sieve_farey {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ x ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
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
  have := large_sieve_gallagher (s := s) (t := fun x : ℚ => (x : ℝ)) hδ hδ2 hsep a N
  rwa [hinv] at this

/-- A reduced fraction `b / q` has denominator `q`. -/
theorem den_natCast_div {b q : ℕ} (hq : 0 < q) (h : Nat.Coprime b q) : ((b : ℚ) / q).den = q := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have h' : Nat.Coprime ((b : ℤ)).natAbs ((q : ℤ)).natAbs := by simpa using h
  have := Rat.den_div_eq_of_coprime hq' h'
  have hcast : ((b : ℤ) : ℚ) / ((q : ℤ) : ℚ) = (b : ℚ) / (q : ℚ) := by push_cast; ring
  rw [hcast] at this
  exact_mod_cast this

/-- A fraction `b / q` with `0 ≤ b < q` lies in `[0, 1)`. -/
theorem mem_Ico_natCast_div {b q : ℕ} (hq : 0 < q) (hb : b < q) :
    (b : ℚ) / q ∈ Set.Ico (0 : ℚ) 1 := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hb' : (b : ℚ) < (q : ℚ) := by exact_mod_cast hb
  constructor
  · positivity
  · rw [div_lt_one hq']
    exact hb'

/-- **The arithmetic large sieve**, in its classical double-sum form over reduced fractions. -/
theorem large_sieve_farey_pairs {Q : ℕ} (hQ : 2 ≤ Q) (a : ℕ → ℂ) (N : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
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
  have key := large_sieve_farey hQ hmemS hdenS a N
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

/-- The large-values count at Farey fractions. -/
theorem card_le_of_large_values_farey {s : Finset ℚ} {Q : ℕ} {V : ℝ} (hQ : 2 ≤ Q) (hV : 0 < V)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ x ∈ s, V ≤ ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖) :
    (s.card : ℝ) ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (∑ n ∈ range N, ‖a n‖ ^ 2) / V ^ 2 := by
  have hsum := large_sieve_farey hQ hmem hden a N
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ x ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _x ∈ s, V ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2 :=
        Finset.sum_le_sum fun x hx => by
          have := hbig x hx
          nlinarith [norm_nonneg (∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))), hV]
  rw [le_div_iff₀ (by positivity)]
  linarith

end LargeSieveFarey

end RiemannHypothesis
