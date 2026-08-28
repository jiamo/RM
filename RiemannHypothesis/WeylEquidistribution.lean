/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylQuadratic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Cancellation in quadratic Weyl sums for an irrational coefficient

`RiemannHypothesis.WeylQuadratic` proves Weyl's inequality for the phase `α n²`, but leaves the
diophantine input as a hypothesis: the bound is only useful once the multiples `2αk` are known to
stay away from the integers.  This module supplies that input in the simplest case, `α`
irrational, and draws the classical conclusion.

## Main results

* `intDist_eq_zero_iff` — `‖θ‖ = 0` exactly when `θ` is an integer.
* `exists_pos_le_intDist_of_irrational` — for `α` irrational and any `H`, the finitely many
  numbers `2αk`, `0 < k < H`, are bounded away from the integers: `∃ δ > 0, δ ≤ ‖2αk‖`.
* `norm_quadSum_div_le` — the explicit consequence of Weyl's inequality: for `α` irrational and
  every `H ≥ 1` there is a constant `C` with `‖∑_{n<N} e(α n²)‖² ≤ (N + H)(N + C)/H`.
* `tendsto_norm_quadSum_div_atTop` — **the quadratic Weyl sum is `o(N)`**: for `α` irrational,

      ‖∑_{0 ≤ n < N} e(α n²)‖ / N → 0 .

* `tendsto_norm_quadSum_div_atTop_intCast` — the same for the phase `h α n²` for every nonzero
  integer `h`, which is the family of estimates Weyl's criterion asks for.

## Proof

Fix `H ≥ 1`.  Since `α` is irrational, so is `2αk` for `k ≠ 0`, hence `‖2αk‖ > 0`; taking the
minimum over the finitely many `0 < k < H` gives a uniform `δ > 0`.  Weyl's inequality then reads

    ‖S N‖² ≤ (N + H − 1)(N + (H − 1)/δ)/H,

whose right-hand side is `N²/H · (1 + o(1))`.  So `limsup ‖S N‖²/N² ≤ 1/H` for every `H`, and
letting `H → ∞` gives the limit `0`.  No rate is obtained this way: `δ` depends on `H` (and on the
diophantine nature of `α`) in an uncontrolled manner.
-/

noncomputable section

open Complex Filter Finset Topology

namespace RiemannHypothesis

namespace WeylEquidistribution

open KusminLandau WeylQuadratic

/-- The quadratic Weyl sum `∑_{0 ≤ n < N} e(α n²)`. -/
def quadSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)

/-- The distance to the nearest integer vanishes exactly at the integers. -/
theorem intDist_eq_zero_iff (θ : ℝ) : intDist θ = 0 ↔ ∃ m : ℤ, θ = m := by
  constructor
  · intro h
    exact ⟨round θ, by have := abs_eq_zero.1 h; linarith⟩
  · rintro ⟨m, rfl⟩
    simp [intDist]

/-- An irrational number is at positive distance from the integers. -/
theorem intDist_pos_of_irrational {θ : ℝ} (hθ : Irrational θ) : 0 < intDist θ := by
  refine lt_of_le_of_ne (intDist_nonneg θ) (Ne.symm ?_)
  intro h
  obtain ⟨m, hm⟩ := (intDist_eq_zero_iff θ).1 h
  exact hθ.ne_int m hm

/-- For `α` irrational and `k ≠ 0`, the number `2αk` is irrational. -/
theorem irrational_two_mul_mul {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    Irrational (2 * α * k) := by
  have h2k : (2 * k : ℤ) ≠ 0 := by simpa using hk
  have := hα.mul_intCast h2k
  have hcast : α * ((2 * k : ℤ) : ℝ) = 2 * α * k := by push_cast; ring
  rwa [hcast] at this

/-- The diophantine input Weyl's inequality needs, for an irrational coefficient: the finitely
many numbers `2αk` with `0 < k < H` stay a fixed positive distance away from the integers. -/
theorem exists_pos_le_intDist_of_irrational {α : ℝ} (hα : Irrational α) (H : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, 0 < k → k < (H : ℤ) → δ ≤ intDist (2 * α * k) := by
  classical
  set s : Finset ℤ := Finset.Ioo (0 : ℤ) (H : ℤ) with hs
  rcases s.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, ?_⟩
    intro k hk hk'
    exact absurd (by rw [hs, Finset.mem_Ioo]; exact ⟨hk, hk'⟩ : k ∈ s) (by simp [hempty])
  · refine ⟨s.inf' hne (fun k => intDist (2 * α * k)), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro k hk
      have hk0 : k ≠ 0 := by
        rw [hs, Finset.mem_Ioo] at hk
        exact ne_of_gt hk.1
      exact intDist_pos_of_irrational (irrational_two_mul_mul hα hk0)
    · intro k hk hk'
      exact Finset.inf'_le _ (by rw [hs, Finset.mem_Ioo]; exact ⟨hk, hk'⟩)

/-- Weyl's inequality with the diophantine hypothesis discharged: for `α` irrational and every
`H ≥ 1` there is a constant `C ≥ 0`, depending on `H` and `α`, with
`‖∑_{n<N} e(α n²)‖² ≤ (N + H)(N + C)/H` for every `N`. -/
theorem exists_normSq_quadSum_le {α : ℝ} (hα : Irrational α) {H : ℕ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖quadSum α N‖ ^ 2 ≤ ((N : ℝ) + H) * ((N : ℝ) + C) / H := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_le_intDist_of_irrational hα H
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  refine ⟨((H : ℝ) - 1) / δ, div_nonneg (by linarith) hδ.le, fun N => ?_⟩
  have hkey := normSq_sum_e2pi_quadratic_le_of_le α δ N H hH hδ hbound
  refine hkey.trans ?_
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have h1 : (N : ℝ) + H - 1 ≤ (N : ℝ) + H := by linarith
  have h2 : (0 : ℝ) ≤ (N : ℝ) + ((H : ℝ) - 1) / δ := by
    have : (0 : ℝ) ≤ ((H : ℝ) - 1) / δ := by
      have : (0 : ℝ) ≤ (H : ℝ) - 1 := by
        have : (1 : ℝ) ≤ H := by exact_mod_cast hH
        linarith
      positivity
    positivity
  gcongr

/-- **The quadratic Weyl sum exhibits cancellation.**  For `α` irrational,
`‖∑_{0 ≤ n < N} e(α n²)‖ / N → 0` as `N → ∞`. -/
theorem tendsto_norm_quadSum_div_atTop {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => ‖quadSum α N‖ / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `H` with `1/H < ε²/4`
  obtain ⟨H, hH⟩ := exists_nat_gt (4 / ε ^ 2)
  have hHpos : (0 : ℝ) < H := lt_of_le_of_lt (by positivity) hH
  have hHnat : 0 < H := by exact_mod_cast hHpos
  obtain ⟨C, hC0, hCbound⟩ := exists_normSq_quadSum_le hα hHnat
  -- for `N` large, `(N + H)(N + C)/H ≤ 4N²/H < ε² N²`
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max ((H : ℝ)) C)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hHle : (H : ℝ) ≤ N := by
    have : (H : ℝ) ≤ (N₀ : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN₀)
    exact this.trans (by exact_mod_cast hNN₀)
  have hCle : C ≤ N := by
    have : C ≤ (N₀ : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN₀)
    exact this.trans (by exact_mod_cast hNN₀)
  have hsq : ‖quadSum α N‖ ^ 2 ≤ 4 * (N : ℝ) ^ 2 / H := by
    refine (hCbound N).trans ?_
    have h1 : ((N : ℝ) + H) * ((N : ℝ) + C) ≤ (2 * N) * (2 * N) := by
      have hA : (N : ℝ) + H ≤ 2 * N := by linarith
      have hB : (N : ℝ) + C ≤ 2 * N := by linarith
      have hA0 : (0 : ℝ) ≤ (N : ℝ) + H := by positivity
      have hB0 : (0 : ℝ) ≤ (N : ℝ) + C := by positivity
      exact mul_le_mul hA hB hB0 (by linarith)
    have : ((N : ℝ) + H) * ((N : ℝ) + C) ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    gcongr
  have hlt : 4 * (N : ℝ) ^ 2 / H < ε ^ 2 * (N : ℝ) ^ 2 := by
    have h4 : 4 / (H : ℝ) < ε ^ 2 := by
      rw [div_lt_iff₀ hHpos]
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < ε ^ 2)).1 hH
      linarith [this]
    calc 4 * (N : ℝ) ^ 2 / H = (4 / H) * (N : ℝ) ^ 2 := by ring
      _ < ε ^ 2 * (N : ℝ) ^ 2 := by
          apply mul_lt_mul_of_pos_right h4 (by positivity)
  have hfinal : ‖quadSum α N‖ ^ 2 < (ε * N) ^ 2 := by
    calc ‖quadSum α N‖ ^ 2 ≤ 4 * (N : ℝ) ^ 2 / H := hsq
      _ < ε ^ 2 * (N : ℝ) ^ 2 := hlt
      _ = (ε * N) ^ 2 := by ring
  have hnorm : ‖quadSum α N‖ < ε * N := by
    have h1 : (0 : ℝ) ≤ ‖quadSum α N‖ := norm_nonneg _
    nlinarith [hfinal, h1, mul_pos hε hNpos]
  have : ‖quadSum α N‖ / N < ε := by
    rw [div_lt_iff₀ hNpos]
    linarith [hnorm]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact this

/-- The family of estimates Weyl's criterion asks for: for `α` irrational and every nonzero
integer `h`, the sum `∑_{n<N} e(h α n²)` is `o(N)`. -/
theorem tendsto_norm_quadSum_div_atTop_intCast {α : ℝ} (hα : Irrational α) {h : ℤ} (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => ‖quadSum ((h : ℝ) * α) N‖ / N) atTop (𝓝 0) := by
  have : Irrational ((h : ℝ) * α) := hα.intCast_mul hh
  exact tendsto_norm_quadSum_div_atTop this

end WeylEquidistribution

end RiemannHypothesis
