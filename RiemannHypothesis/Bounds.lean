/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

/-!
# An explicit bound for `ζ` on the half-plane of absolute convergence

The first of the classical growth estimates: on `re s > 1` the Dirichlet series of `ζ`
converges absolutely and is bounded by the corresponding real series, which the
integral comparison bounds by `1 + 1/(σ - 1)`.

## Main results

* `tsum_natAddOne_rpow_neg_le` : `∑' n, (n+1)^(-σ) ≤ 1 + 1/(σ - 1)` for `1 < σ`, by comparing
  the partial sums with `∫ x^(-σ)`.
* `norm_riemannZeta_le_of_one_lt_re` : `‖ζ(s)‖ ≤ 1 + 1/(re s - 1)` for `1 < re s`.

The bound blows up as `re s → 1⁺`, as it must: `ζ` has a pole at `s = 1`.

Also proved here is the elementary trigonometric inequality behind the classical zero-free
region:

* `three_add_four_cos_add_cos_two_nonneg` : `0 ≤ 3 + 4 cos θ + cos 2θ`, since the left-hand
  side is `2 (1 + cos θ)²`.
-/

noncomputable section

open Filter Finset
open scoped Topology

namespace RiemannHypothesis

/-- `x ↦ x ^ (-σ)` is antitone on `[1, b]`. -/
lemma antitoneOn_rpow_neg {σ b : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc 1 b) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)

/-- The partial sums of `∑ (n+1)^(-σ)` are bounded by `1 + 1/(σ - 1)`. -/
lemma sum_range_natAddOne_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ := by linarith
  have hσ1 : 0 < σ - 1 := by linarith
  cases N with
  | zero =>
    simp only [range_zero, sum_empty]
    positivity
  | succ M =>
    have hMle : (1 : ℝ) ≤ 1 + (M : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg M)
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc 1 (1 + (M : ℝ))) :=
      antitoneOn_rpow_neg hσ0
    have hsum := hanti.sum_le_integral
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (M : ℝ)) := by
      rw [Set.uIcc_of_le hMle]
      simp
    have hint : ∫ x in (1 : ℝ)..(1 + (M : ℝ)), x ^ (-σ)
        = ((1 + (M : ℝ)) ^ (-σ + 1) - (1 : ℝ) ^ (-σ + 1)) / (-σ + 1) := by
      rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have hintle : (∫ x in (1 : ℝ)..(1 + (M : ℝ)), x ^ (-σ)) ≤ 1 / (σ - 1) := by
      have hpos : 0 ≤ (1 + (M : ℝ)) ^ (-σ + 1) := Real.rpow_nonneg (by positivity) _
      have hrw : ((1 + (M : ℝ)) ^ (-σ + 1) - (1 : ℝ)) / (-σ + 1)
          = (1 - (1 + (M : ℝ)) ^ (-σ + 1)) / (σ - 1) := by
        rw [show (-σ + 1) = -(σ - 1) by ring, div_neg]
        ring
      rw [hint, Real.one_rpow, hrw]
      exact (div_le_div_iff_of_pos_right hσ1).mpr (by linarith)
    -- peel off the first term of the sum
    have hpeel : ∑ n ∈ range (M + 1), ((n : ℝ) + 1) ^ (-σ)
        = (∑ i ∈ range M, (1 + ((i : ℝ) + 1)) ^ (-σ)) + 1 := by
      rw [sum_range_succ']
      norm_num
      apply sum_congr rfl
      intro i _
      ring_nf
    rw [hpeel]
    have hcast : ∀ i : ℕ, ((1 : ℝ) + ((i : ℝ) + 1)) = 1 + ((i + 1 : ℕ) : ℝ) := by
      intro i; push_cast; ring
    calc (∑ i ∈ range M, (1 + ((i : ℝ) + 1)) ^ (-σ)) + 1
        = (∑ i ∈ range M, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-σ)) + 1 := by
          congr 1
          exact sum_congr rfl fun i _ => by rw [hcast i]
      _ ≤ (∫ x in (1 : ℝ)..(1 + (M : ℝ)), x ^ (-σ)) + 1 := by linarith [hsum]
      _ ≤ 1 / (σ - 1) + 1 := by linarith
      _ = 1 + 1 / (σ - 1) := by ring

/-- The comparison bound for the real series: `∑' n, (n+1)^(-σ) ≤ 1 + 1/(σ - 1)`. -/
lemma tsum_natAddOne_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) ≤ 1 + 1 / (σ - 1) :=
  Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (by positivity) _)
    (sum_range_natAddOne_rpow_neg_le hσ)

/-- **An explicit bound for `ζ` on the half-plane of absolute convergence**:
`‖ζ(s)‖ ≤ 1 + 1/(re s - 1)` for `1 < re s`. -/
theorem norm_riemannZeta_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [norm_div, norm_one]
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rw [one_div]
  have hsummable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re)) := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hnormsummable : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖) := by
    exact hsummable.congr fun n => (hnorm n).symm
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hnormsummable
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s.re) := by simp_rw [hnorm]
    _ ≤ 1 + 1 / (s.re - 1) := tsum_natAddOne_rpow_neg_le hs

/-! ## The trigonometric inequality behind the zero-free region -/

/-- The Mertens inequality `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`, the elementary input
to the classical proof that `ζ` has no zero on the line `re s = 1` and to the de la Vallée
Poussin zero-free region. -/
lemma three_add_four_cos_add_cos_two_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  rw [h]
  positivity

end RiemannHypothesis

end
