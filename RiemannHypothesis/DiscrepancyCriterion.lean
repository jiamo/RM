/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Discrepancy
import RiemannHypothesis.WeylPortmanteau

/-!
# Weyl's criterion in discrepancy form

`RiemannHypothesis.Discrepancy` defines the discrepancy

    D_N(x) = sup { |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| : 0 ≤ a ≤ b ≤ 1 }

and bounds it for a badly approximable `α`.  This module proves the *qualitative* statement that
goes with it, and which the earlier interval-by-interval formulations could not express: a
sequence is equidistributed modulo one exactly when its discrepancy tends to `0`.

The forward direction is the substance.  Equidistribution is a statement about each interval
separately, and the naive deduction — "each deviation tends to `0`, hence their supremum does" —
is false in general, a supremum of finitely many null sequences being null but a supremum of
infinitely many not.  What makes the deduction work is the Erdős–Turán inequality of
`M1-WEYL-DISCREPANCY-GENERAL`, which bounds *all* the intervals at once by `20/K` plus finitely
many exponential sums: the first term is made small by the choice of `K`, and only then does one
pass to the limit in the remaining `K⁴ − 1` sums.

## Main results

* `tendsto_discrepancy_of_weylSumsVanish` — if every nonzero frequency exhibits cancellation then
  `D_N(x) → 0`.
* `countsEquidistribute_of_tendsto_discrepancy` — conversely, `D_N(x) → 0` gives the counting
  form of equidistribution, hence equidistribution.
* `equidistributedMod1_iff_tendsto_discrepancy`,
  `weylSumsVanish_iff_tendsto_discrepancy`,
  `countsEquidistribute_iff_tendsto_discrepancy` — **Weyl's criterion in discrepancy form**: the
  four formulations are equivalent.
* `tendsto_discrepancy_quadratic` — for every irrational `α`, `D_N(α n²) → 0`.
* `not_tendsto_discrepancy_const_zero` — the criterion is not vacuous: the constant sequence `0`
  has `D_N ≥ 1/2` and is not equidistributed.

## Scope

No rate is claimed here; the rates are those of `RiemannHypothesis.Discrepancy`, available only
for badly approximable coefficients.  Nothing here concerns `ζ`.
-/

noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount WeylCriterion WeylPortmanteau

/-- A parameter `K ≥ 8` making the first term of the Erdős–Turán bound as small as desired. -/
theorem exists_nat_ge_eight_div_lt {ε : ℝ} (hε : 0 < ε) : ∃ K : ℕ, 8 ≤ K ∧ 20 / (K : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (20 / ε)
  refine ⟨max 8 n, le_max_left _ _, ?_⟩
  have hnR : (n : ℝ) ≤ ((max 8 n : ℕ) : ℝ) := by exact_mod_cast le_max_right 8 n
  have hKpos : (0 : ℝ) < ((max 8 n : ℕ) : ℝ) := by
    have : (8 : ℕ) ≤ max 8 n := le_max_left _ _
    have : (0 : ℕ) < max 8 n := by omega
    exact_mod_cast this
  have h20 : 20 / ε < ((max 8 n : ℕ) : ℝ) := lt_of_lt_of_le hn hnR
  rw [div_lt_iff₀ hKpos]
  rw [div_lt_iff₀ hε] at h20
  linarith

/-- **Weyl's criterion, discrepancy form, forward direction.**  If the exponential sums of `x` at
every nonzero frequency are `o(N)`, then the discrepancy of `x` tends to `0`. -/
theorem tendsto_discrepancy_of_weylSumsVanish {x : ℕ → ℝ} (h : WeylSumsVanish x) :
    Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK8, hKε⟩ := exists_nat_ge_eight_div_lt (show (0 : ℝ) < ε / 2 by linarith)
  have hsum : Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N)
      atTop (𝓝 0) := by
    have hterm : ∀ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
        Tendsto (fun N : ℕ => ‖expSum x (m : ℤ) N‖ / N) atTop (𝓝 0) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm0 : (m : ℤ) ≠ 0 := by
        have : 1 ≤ m := hm.1
        exact_mod_cast Nat.one_le_iff_ne_zero.mp this
      exact h (m : ℤ) hm0
    simpa using tendsto_finsetSum (Finset.Icc (1 : ℕ) (K ^ 4 - 1)) hterm
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨N₀, hN₀⟩ := hsum (ε / 8) (by linarith)
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_left 1 N₀) hN)
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right 1 N₀) hN
  have hbound := discrepancy_le_pow x hK8 hN1
  have hsmall := hN₀ N hNN₀
  rw [Real.dist_eq, sub_zero] at hsmall
  have hsumnn : 0 ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N :=
    sum_norm_expSum_div_nonneg x K N
  rw [abs_of_nonneg hsumnn] at hsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (discrepancy_nonneg x N)]
  calc discrepancy x N
      ≤ 20 / K + 4 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N := hbound
    _ < ε / 2 + 4 * (ε / 8) := by gcongr
    _ = ε := by ring

/-- **The converse.**  If the discrepancy tends to `0` then every subinterval receives its
share. -/
theorem countsEquidistribute_of_tendsto_discrepancy {x : ℕ → ℝ}
    (h : Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0)) : CountsEquidistribute x := by
  intro a b ha hab hb
  have habs : Tendsto (fun N : ℕ => |(countIn x a b N : ℝ) / N - (b - a)|) atTop (𝓝 0) :=
    squeeze_zero (fun N => abs_nonneg _) (fun N => le_discrepancy x ha hab.le hb N) h
  rw [tendsto_iff_dist_tendsto_zero]
  exact habs.congr fun N => (Real.dist_eq _ _).symm

/-- **Weyl's criterion in discrepancy form.** -/
theorem weylSumsVanish_iff_tendsto_discrepancy (x : ℕ → ℝ) :
    WeylSumsVanish x ↔ Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0) :=
  ⟨tendsto_discrepancy_of_weylSumsVanish, fun h =>
    (weylSumsVanish_iff_countsEquidistribute x).2 (countsEquidistribute_of_tendsto_discrepancy h)⟩

/-- Equidistribution modulo one is exactly the vanishing of the discrepancy. -/
theorem equidistributedMod1_iff_tendsto_discrepancy (x : ℕ → ℝ) :
    EquidistributedMod1 x ↔ Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0) := by
  rw [equidistributedMod1_iff_weylSumsVanish, weylSumsVanish_iff_tendsto_discrepancy]

/-- The counting form of equidistribution is exactly the vanishing of the discrepancy. -/
theorem countsEquidistribute_iff_tendsto_discrepancy (x : ℕ → ℝ) :
    CountsEquidistribute x ↔ Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0) := by
  rw [← weylSumsVanish_iff_countsEquidistribute, weylSumsVanish_iff_tendsto_discrepancy]

/-- For every irrational `α` the discrepancy of `α n²` tends to `0`. -/
theorem tendsto_discrepancy_quadratic {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => discrepancy (fun n : ℕ => α * (n : ℝ) ^ 2) N) atTop (𝓝 0) :=
  tendsto_discrepancy_of_weylSumsVanish (weylSumsVanish_quadratic hα)

/-- The criterion is not vacuous: the constant sequence `0` has discrepancy at least `1/2`, so
its discrepancy does not tend to `0` and it is not equidistributed. -/
theorem not_tendsto_discrepancy_const_zero :
    ¬ Tendsto (fun N : ℕ => discrepancy (fun _ : ℕ => (0 : ℝ)) N) atTop (𝓝 0) := by
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1 / 4) (by norm_num)
  have h1 := hN N le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (discrepancy_nonneg (fun _ : ℕ => (0 : ℝ)) N)] at h1
  linarith [half_le_discrepancy_const_zero N]

end WeylDiscrepancy

end RiemannHypothesis
