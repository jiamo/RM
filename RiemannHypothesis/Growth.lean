/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Eta
import RiemannHypothesis.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Growth of `ζ` inside the critical strip, and the Mertens `3-4-1` product bound

`RiemannHypothesis.Bounds` bounds `ζ` on the half-plane of absolute convergence.  This file
carries the estimates *into* the critical strip, where the Dirichlet series diverges, using
the eta representation of the strip that the repository already has:

`η(s) = (1 - 2^(1-s)) ζ(s)`, with `η` given by an absolutely convergent paired series.

## Main results

* `norm_pairedTerm_le_rpow` : `‖pairedTerm j s‖ ≤ ‖s‖ * (2j+1)^(-(1 + re s))` for `0 ≤ re s`.
* `tsum_oddAddOne_rpow_neg_le` : `∑' j, (2j+1)^(-(1+σ)) ≤ 1 + 1/σ` for `0 < σ`.
* `norm_dirichletEta_le` : `‖η(s)‖ ≤ ‖s‖ * (1 + 1 / re s)` for `0 < re s`.
* `norm_riemannZeta_le_of_mem_strip` : for `0 < re s < 1`,
  `‖ζ(s)‖ ≤ ‖s‖ * (1 + 1/re s) / (2^(1 - re s) - 1)`.
* `norm_riemannZeta_le_linear_of_mem_strip` : the same in asymptotic form — for a fixed
  `σ ∈ (0,1)` there is a constant `C` with `‖ζ(σ + it)‖ ≤ C * (1 + |t|)` for every real `t`.
* `norm_riemannZeta_product_ge_one` : the Mertens `3-4-1` product bound for `ζ`,
  `1 ≤ ‖ζ(1+x)^3 * ζ(1+x+iy)^4 * ζ(1+x+2iy)‖` for `0 < x`.

## What is *not* proved here

The classical convexity bound `|ζ(σ + it)| = O(|t|^((1-σ)/2 + ε))` inside the strip, and the
bound `|ζ(σ + it)| = O(log |t|)` for `1 < σ ≤ 2`, both need the Euler–Maclaurin (approximate
functional equation) machinery; they are *not* proved here.  What is proved is the weaker,
unconditional linear bound `O(|t|)`, which is already enough to know that `ζ` is of finite
order in the strip.  The gap is recorded honestly on the task board (`M1-GROWTH`).

The `3-4-1` bound is *derived* from Mathlib's Dirichlet-character version
(`DirichletCharacter.norm_LFunction_product_ge_one`) specialized to the modulus `1`; it is the
positivity input to the classical zero-free region, and combined with Mathlib's
`riemannZeta_ne_zero_of_one_le_re` it is the reason `ζ` has no zero on the line `re s = 1`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## A clean bound for the paired terms -/

/-- The paired term bound in the form used for summation:
`‖pairedTerm j s‖ ≤ ‖s‖ * (2j+1)^(-(1 + re s))`. -/
lemma norm_pairedTerm_le_rpow (j : ℕ) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ‖pairedTerm j s‖ ≤ ‖s‖ * ((2 * j + 1 : ℝ) ^ (-(1 + s.re))) := by
  have hpos : (0 : ℝ) < 2 * j + 1 := by positivity
  calc ‖pairedTerm j s‖
      ≤ ‖s‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) :=
        norm_pairedTerm_le j hs0
    _ ≤ ‖s‖ * (1 / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) := by
        gcongr
        exact log_pair_le_inv j
    _ = ‖s‖ * ((2 * j + 1 : ℝ) ^ (-(1 + s.re))) := by
        rw [mul_assoc]
        congr 1
        rw [show -(1 + s.re) = -1 + -s.re by ring, Real.rpow_add hpos, Real.rpow_neg_one]
        rw [one_div]

/-! ## The odd-index series -/

/-- The odd-index series is bounded by the full series: `∑' j, (2j+1)^(-(1+σ)) ≤ 1 + 1/σ`
for `0 < σ`. -/
lemma tsum_oddAddOne_rpow_neg_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' j : ℕ, ((2 * j + 1 : ℝ) ^ (-(1 + σ))) ≤ 1 + 1 / σ := by
  have hfull : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + σ))) := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + σ))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hodd : Summable (fun j : ℕ => ((2 * j + 1 : ℝ) ^ (-(1 + σ)))) := by
    refine hfull.of_nonneg_of_le (fun j => Real.rpow_nonneg (by positivity) _) fun j => ?_
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by linarith)
  have hle : ∑' j : ℕ, ((2 * j + 1 : ℝ) ^ (-(1 + σ)))
      ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) := by
    refine Summable.tsum_le_tsum_of_inj (fun j => 2 * j) (fun a b hab => by simpa using hab)
      (fun c _ => Real.rpow_nonneg (by positivity) _) (fun j => ?_) hodd hfull
    push_cast
    exact le_of_eq rfl
  calc ∑' j : ℕ, ((2 * j + 1 : ℝ) ^ (-(1 + σ)))
      ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + σ)) := hle
    _ ≤ 1 + 1 / ((1 + σ) - 1) := tsum_natAddOne_rpow_neg_le (by linarith)
    _ = 1 + 1 / σ := by ring_nf

/-! ## The bound for `η` on the right half-plane -/

/-- **A growth bound for the Dirichlet eta function**: `‖η(s)‖ ≤ ‖s‖ * (1 + 1/re s)` for
`0 < re s`.  In particular `η` grows at most linearly in `|s|` on every vertical line in the
right half-plane. -/
theorem norm_dirichletEta_le {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletEta s‖ ≤ ‖s‖ * (1 + 1 / s.re) := by
  have hbound : ∀ j : ℕ, ‖pairedTerm j s‖ ≤ ‖s‖ * ((2 * j + 1 : ℝ) ^ (-(1 + s.re))) :=
    fun j => norm_pairedTerm_le_rpow j hs.le
  have hodd : Summable (fun j : ℕ => ((2 * j + 1 : ℝ) ^ (-(1 + s.re)))) := by
    have hfull : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + s.re))) := by
      have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re))) :=
        Real.summable_nat_rpow.mpr (by linarith)
      refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    refine hfull.of_nonneg_of_le (fun j => Real.rpow_nonneg (by positivity) _) fun j => ?_
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by linarith)
  have hnormsummable : Summable (fun j : ℕ => ‖pairedTerm j s‖) :=
    (hodd.mul_left ‖s‖).of_nonneg_of_le (fun j => norm_nonneg _) hbound
  calc ‖dirichletEta s‖
      = ‖∑' j : ℕ, pairedTerm j s‖ := rfl
    _ ≤ ∑' j : ℕ, ‖pairedTerm j s‖ := norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' j : ℕ, ‖s‖ * ((2 * j + 1 : ℝ) ^ (-(1 + s.re))) :=
        hnormsummable.tsum_le_tsum hbound (hodd.mul_left ‖s‖)
    _ = ‖s‖ * ∑' j : ℕ, ((2 * j + 1 : ℝ) ^ (-(1 + s.re))) := tsum_mul_left
    _ ≤ ‖s‖ * (1 + 1 / s.re) := by
        exact mul_le_mul_of_nonneg_left (tsum_oddAddOne_rpow_neg_le hs) (norm_nonneg s)

/-! ## The size of the eta factor -/

/-- A lower bound for the factor relating `η` and `ζ`: `2^(1 - re s) - 1 ≤ ‖1 - 2^(1-s)‖`.
The left-hand side is positive exactly when `re s < 1`, which is where the bound is used. -/
lemma norm_one_sub_two_cpow_ge (s : ℂ) :
    (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    change ‖(((2 : ℝ) : ℂ)) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - s)]
    simp
  calc (2 : ℝ) ^ (1 - s.re) - 1
      = ‖(2 : ℂ) ^ (1 - s)‖ - ‖(1 : ℂ)‖ := by rw [hnorm, norm_one]
    _ ≤ ‖(2 : ℂ) ^ (1 - s) - 1‖ := norm_sub_norm_le _ _
    _ = ‖1 - (2 : ℂ) ^ (1 - s)‖ := norm_sub_rev _ _

/-- The eta factor is bounded below by a positive quantity in the critical strip. -/
lemma one_lt_two_rpow_one_sub_re {s : ℂ} (hs : s.re < 1) :
    1 < (2 : ℝ) ^ (1 - s.re) := by
  refine Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)

/-! ## The growth bound for `ζ` in the strip -/

/-- **A growth bound for `ζ` inside the critical strip**: for `0 < re s < 1`,
`‖ζ(s)‖ ≤ ‖s‖ * (1 + 1/re s) / (2^(1 - re s) - 1)`.

The bound is linear in `|s|`, hence linear in the height `|im s|` on every vertical line
strictly inside the strip.  It is far from the classical convexity bound
`O(|t|^((1-σ)/2 + ε))`, but it is unconditional and elementary: it comes from the absolutely
convergent paired eta series and the identity `η = (1 - 2^(1-s)) ζ`. -/
theorem norm_riemannZeta_le_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ * (1 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) := by
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hfac : (0 : ℝ) < (2 : ℝ) ^ (1 - s.re) - 1 := by
    have := one_lt_two_rpow_one_sub_re hs1
    linarith
  have hid : dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
    dirichletEta_eq_mul_riemannZeta hs0 hne
  have hkey : ((2 : ℝ) ^ (1 - s.re) - 1) * ‖riemannZeta s‖ ≤ ‖dirichletEta s‖ := by
    rw [hid, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_one_sub_two_cpow_ge s) (norm_nonneg _)
  rw [le_div_iff₀ hfac, mul_comm]
  exact hkey.trans (norm_dirichletEta_le hs0)

/-- **The linear growth bound on a vertical line in the strip**: for a fixed `σ` with
`0 < σ < 1` there is a constant `C` (explicitly `(1 + 1/σ) / (2^(1-σ) - 1)`) with
`‖ζ(σ + it)‖ ≤ C * (1 + |t|)` for every real `t`. -/
theorem norm_riemannZeta_le_linear_of_mem_strip {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖riemannZeta (σ + t * I)‖ ≤ C * (1 + |t|) := by
  have hfac : (0 : ℝ) < (2 : ℝ) ^ (1 - σ) - 1 := by
    have : 1 < (2 : ℝ) ^ (1 - σ) :=
      Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)
    linarith
  refine ⟨(1 + 1 / σ) / ((2 : ℝ) ^ (1 - σ) - 1), by positivity, fun t => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact hσ0
  have hs1 : s.re < 1 := by rw [hre]; exact hσ1
  have hnorm : ‖s‖ ≤ 1 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him] at h
    have : |σ| ≤ 1 := by rw [abs_of_pos hσ0]; linarith
    linarith
  calc ‖riemannZeta s‖
      ≤ ‖s‖ * (1 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) :=
        norm_riemannZeta_le_of_mem_strip hs0 hs1
    _ = ‖s‖ * ((1 + 1 / σ) / ((2 : ℝ) ^ (1 - σ) - 1)) := by rw [hre]; ring
    _ ≤ (1 + |t|) * ((1 + 1 / σ) / ((2 : ℝ) ^ (1 - σ) - 1)) := by
        gcongr
    _ = (1 + 1 / σ) / ((2 : ℝ) ^ (1 - σ) - 1) * (1 + |t|) := by ring

/-! ## The Mertens `3-4-1` product bound for `ζ` -/

/-- **The Mertens `3-4-1` bound for the Riemann zeta function**: for `0 < x` and any real `y`,
`1 ≤ ‖ζ(1+x)^3 * ζ(1+x+iy)^4 * ζ(1+x+2iy)‖`.

This is the positivity input to the classical proof that `ζ` has no zero on the line
`re s = 1` and to the de la Vallée Poussin zero-free region; the underlying elementary
inequality is `0 ≤ 3 + 4 cos θ + cos 2θ`
(`RiemannHypothesis.three_add_four_cos_add_cos_two_nonneg`).  The proof here specializes
Mathlib's Dirichlet-character version to the modulus `1`, where the L-function is `ζ`. -/
theorem norm_riemannZeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) 1 hx y
  simpa [DirichletCharacter.LFunctionTrivChar, one_pow] using h

end RiemannHypothesis

end
