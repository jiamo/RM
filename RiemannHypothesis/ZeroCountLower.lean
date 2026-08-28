/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroInfinite
import RiemannHypothesis.ZeroSum

/-!
# The counting function `N(T)` is unbounded

`RiemannHypothesis.ZeroCount` bounds the number of nontrivial zeroes of `ζ` of height at most `T`
from above (`ncard_nontrivialZeros_le` : `N(T) = O(T log T)`), and
`RiemannHypothesis.ZeroInfinite` shows that the critical strip contains infinitely many zeroes
(`infinite_nontrivialZeroSet`).  Combining the two gives the complementary qualitative statements
proved here:

* `monotone_ncard_nontrivialZeros` : `T ↦ N(T)` is monotone;
* `exists_mem_nontrivialZeroSet_lt_abs_im` : the imaginary parts of the nontrivial zeroes are
  **unbounded** — for every height `T` there is a zero of `ζ` in the open critical strip with
  `T < |im s|`;
* `exists_le_ncard_nontrivialZeros` : every natural number is attained as a lower bound for `N(T)`
  at some height;
* `tendsto_ncard_nontrivialZeros_atTop` : `N(T) → ∞` as `T → ∞`.

Everything here counts zeroes *without* multiplicity, and no rate is obtained: the proofs go
through the infinitude of the zero set, which is itself proved by contradiction.  The matching
quantitative lower bound `N(T) ≫ T log T` is not proved.
-/

noncomputable section

open Complex Filter Topology

namespace RiemannHypothesis

/-- The counting function `N(T) = #{ρ : ζ ρ = 0, 0 < re ρ < 1, |im ρ| ≤ T}` is monotone. -/
theorem monotone_ncard_nontrivialZeros :
    Monotone fun T : ℝ => (nontrivialZeros T).ncard := by
  intro T₁ T₂ hT
  refine Set.ncard_le_ncard ?_ (finite_nontrivialZeros T₂)
  rintro s ⟨hz, h0, h1, him⟩
  exact ⟨hz, h0, h1, him.trans hT⟩

/-- **The imaginary parts of the nontrivial zeroes are unbounded**: for every height `T` there is
a zero of `ζ` in the open critical strip with `T < |im s|`. -/
theorem exists_mem_nontrivialZeroSet_lt_abs_im (T : ℝ) :
    ∃ s ∈ nontrivialZeroSet, T < |s.im| := by
  by_contra h
  push Not at h
  refine infinite_nontrivialZeroSet (Set.Finite.subset (finite_nontrivialZeros T) ?_)
  intro s hs
  exact mem_nontrivialZeros_of_mem hs (h s hs)

/-- Every natural number is a lower bound for the counting function at some height. -/
theorem exists_le_ncard_nontrivialZeros (n : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ n ≤ (nontrivialZeros T).ncard := by
  classical
  obtain ⟨t, hts, htcard⟩ := infinite_nontrivialZeroSet.exists_subset_card_eq n
  obtain ⟨M, hM⟩ := (t.image fun s : ℂ => |s.im|).exists_le
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  have hsub : (t : Set ℂ) ⊆ nontrivialZeros (max 0 M) := by
    intro s hs
    exact mem_nontrivialZeros_of_mem (hts hs)
      ((hM _ (Finset.mem_image_of_mem _ hs)).trans (le_max_right _ _))
  calc (n : ℕ) = (t : Set ℂ).ncard := by rw [Set.ncard_coe_finset, htcard]
    _ ≤ (nontrivialZeros (max 0 M)).ncard :=
        Set.ncard_le_ncard hsub (finite_nontrivialZeros _)

/-- **The counting function tends to infinity.** -/
theorem tendsto_ncard_nontrivialZeros_atTop :
    Tendsto (fun T : ℝ => ((nontrivialZeros T).ncard : ℝ)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨T, _, hT⟩ := exists_le_ncard_nontrivialZeros ⌈b⌉₊
  refine ⟨T, fun x hx => ?_⟩
  have hmono : (nontrivialZeros T).ncard ≤ (nontrivialZeros x).ncard :=
    monotone_ncard_nontrivialZeros hx
  have hb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have : ((⌈b⌉₊ : ℕ) : ℝ) ≤ ((nontrivialZeros x).ncard : ℝ) := by
    exact_mod_cast hT.trans hmono
  linarith

end RiemannHypothesis
