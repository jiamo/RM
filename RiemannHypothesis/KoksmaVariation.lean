/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Koksma

/-!
# Koksma's inequality with the total variation

`RiemannHypothesis.Koksma` proves Koksma's inequality for a nondecreasing integrand and, as a
corollary, for an integrand *presented* as a difference `f = g - h` of two nondecreasing
functions, the bound then involving the two rises `(g 1 - g 0) + (h 1 - h 0)` of the chosen
presentation.  That left a gap recorded on the task board: no bound was available in terms of the
total variation of `f` itself, which is the functional Koksma's inequality is classically stated
with, and which does not refer to any choice of decomposition.

This module closes that gap, using mathlib's `eVariationOn`.  Write

    V(f) = (eVariationOn f [0,1]).toReal   (`unitVariation`)

for the total variation of `f` on the unit interval.  For every `f` of bounded variation, every
sequence `x` and every `N ≥ 1`,

    |(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ (2 V(f) − |f 1 − f 0|) · D_N(x)   (`koksma_variation`)

and in particular the bound `2 V(f) · D_N(x)` (`koksma_variation_le`).  No continuity is assumed.

## Main results

* `unitVariation` — the total variation of `f` on `[0,1]`, as a real number.
* `unitVariation_of_monotoneOn` — for a nondecreasing `f` it is the rise `f 1 - f 0`.
* `koksma_variation_sub`, `koksma_variation_add` — the two one-sided forms, with the constants
  `2 V(f) − (f 1 − f 0)` and `2 V(f) + (f 1 − f 0)`; they come from the two Jordan
  decompositions `f = V_f − (V_f − f)` and `f = (V_f + f) − V_f`, where
  `V_f x = variationOnFromTo f [0,1] 0 x`.
* `koksma_variation` — their conjunction, with constant `2 V(f) − |f 1 − f 0|`.
* `koksma_variation_le` — the readable form, with constant `2 V(f)`.
* `koksma_lipschitz_two` — for an `L`-Lipschitz integrand the constant is `2 L`, improving the
  constant `3 L` of `koksma_lipschitz`.
* `tendsto_average_of_tendsto_discrepancy_variation` — a sequence whose discrepancy tends to `0`
  integrates *every* function of bounded variation correctly in the limit.
* `tendsto_average_quadratic_variation` — the concrete instance `xₙ = α n²`, `α` irrational.

## What is not proved

The sharp constant of Koksma's inequality is `V(f)`, not `2 V(f)`; the sharp form is proved by
Riemann–Stieltjes integration by parts, machinery which mathlib does not have.  The factor `2`
here is the price of routing through the Jordan decomposition: the rises of the two monotone
pieces add up to `2 V(f) − (f 1 − f 0)`, not to `V(f)`.  For a nondecreasing `f` the constant
below is exactly `f 1 − f 0 = V(f)`, so nothing is lost in that case.
-/

noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace WeylDiscrepancy

/-- The total variation of `f` on the unit interval, as a real number. -/
def unitVariation (f : ℝ → ℝ) : ℝ := (eVariationOn f (Set.Icc (0 : ℝ) 1)).toReal

theorem unitVariation_nonneg (f : ℝ → ℝ) : 0 ≤ unitVariation f := ENNReal.toReal_nonneg

/-- The signed variation from `0` to `1` is the total variation. -/
theorem variationOnFromTo_zero_one (f : ℝ → ℝ) :
    variationOnFromTo f (Set.Icc (0 : ℝ) 1) 0 1 = unitVariation f := by
  rw [variationOnFromTo.eq_of_le f _ zero_le_one, unitVariation, Set.inter_self]

/-- For a nondecreasing integrand the total variation is the rise. -/
theorem unitVariation_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1)) :
    unitVariation f = f 1 - f 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hle : f 0 ≤ f 1 := hf h0 h1 zero_le_one
  have := hf.eVariationOn_eq h0 h1
  rw [Set.inter_self] at this
  rw [unitVariation, this, ENNReal.toReal_ofReal (by linarith)]

/-- The total variation bounds the rise. -/
theorem abs_sub_le_unitVariation {f : ℝ → ℝ}
    (hf : LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    |f 1 - f 0| ≤ unitVariation f := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h := variationOnFromTo.abs_sub_le_sub_of_le hf h0 h0 h1 zero_le_one
  rw [variationOnFromTo.self, variationOnFromTo_zero_one] at h
  simpa using h

/-- **Koksma's inequality with the total variation**, first form.  It comes from the Jordan
decomposition `f = V_f - (V_f - f)`. -/
theorem koksma_variation_sub {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (2 * unitVariation f - (f 1 - f 0)) * discrepancy x N := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hloc : LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1) := hf.locallyBoundedVariationOn
  set p : ℝ → ℝ := variationOnFromTo f (Set.Icc (0 : ℝ) 1) 0 with hp
  have hpmono : MonotoneOn p (Set.Icc (0 : ℝ) 1) := variationOnFromTo.monotoneOn hloc h0
  have hqmono : MonotoneOn (p - f) (Set.Icc (0 : ℝ) 1) :=
    variationOnFromTo.sub_self_monotoneOn hloc h0
  have hp0 : p 0 = 0 := variationOnFromTo.self f _ 0
  have hp1 : p 1 = unitVariation f := variationOnFromTo_zero_one f
  have hfgh : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = p t - (p - f) t := by
    intro t _
    simp
  have h := koksma_sub_monotone hfgh hpmono hqmono x hN
  have hconst : (p 1 - p 0) + ((p - f) 1 - (p - f) 0)
      = 2 * unitVariation f - (f 1 - f 0) := by
    simp only [Pi.sub_apply, hp0, hp1]
    ring
  rwa [hconst] at h

/-- **Koksma's inequality with the total variation**, second form.  It comes from the Jordan
decomposition `f = (V_f + f) - V_f`. -/
theorem koksma_variation_add {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (2 * unitVariation f + (f 1 - f 0)) * discrepancy x N := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hloc : LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1) := hf.locallyBoundedVariationOn
  set p : ℝ → ℝ := variationOnFromTo f (Set.Icc (0 : ℝ) 1) 0 with hp
  have hpmono : MonotoneOn p (Set.Icc (0 : ℝ) 1) := variationOnFromTo.monotoneOn hloc h0
  have hgmono : MonotoneOn (p + f) (Set.Icc (0 : ℝ) 1) :=
    variationOnFromTo.add_self_monotoneOn hloc h0
  have hp0 : p 0 = 0 := variationOnFromTo.self f _ 0
  have hp1 : p 1 = unitVariation f := variationOnFromTo_zero_one f
  have hfgh : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = (p + f) t - p t := by
    intro t _
    simp
  have h := koksma_sub_monotone hfgh hgmono hpmono x hN
  have hconst : ((p + f) 1 - (p + f) 0) + (p 1 - p 0)
      = 2 * unitVariation f + (f 1 - f 0) := by
    simp only [Pi.add_apply, hp0, hp1]
    ring
  rwa [hconst] at h

/-- **Koksma's inequality with the total variation.**  For every integrand of bounded variation on
`[0,1]` — no continuity assumed — the error of the average along the first `N` terms of the
sequence is at most `(2 V(f) − |f 1 − f 0|) D_N(x)`. -/
theorem koksma_variation {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (2 * unitVariation f - |f 1 - f 0|) * discrepancy x N := by
  rcases abs_cases (f 1 - f 0) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]
    exact koksma_variation_sub hf x hN
  · rw [heq]
    have := koksma_variation_add hf x hN
    have hcast : 2 * unitVariation f - -(f 1 - f 0) = 2 * unitVariation f + (f 1 - f 0) := by ring
    rwa [hcast]

/-- **Koksma's inequality with the total variation**, in the readable form `2 V(f) D_N(x)`. -/
theorem koksma_variation_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 2 * unitVariation f * discrepancy x N := by
  refine (koksma_variation hf x hN).trans ?_
  have hD := discrepancy_nonneg x N
  have habs : 0 ≤ |f 1 - f 0| := abs_nonneg _
  nlinarith

/-! ### The Lipschitz case -/

/-- The total variation of an `L`-Lipschitz function on `[0,1]` is at most `L`. -/
theorem unitVariation_le_of_lipschitz {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|) :
    eVariationOn f (Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L := by
  have hlipOn : LipschitzOnWith L.toNNReal f (Set.Icc (0 : ℝ) 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
    exact hlip b a hb ha
  have hcomp := hlipOn.comp_eVariationOn_le (g := id) (s := Set.Icc (0 : ℝ) 1) (Set.mapsTo_id _)
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc (0 : ℝ) 1) = ENNReal.ofReal 1 := by
    simp
  have hfun : (f ∘ (id : ℝ → ℝ)) = f := rfl
  rw [hfun, hid, ENNReal.ofReal_one, mul_one] at hcomp
  exact hcomp

/-- **Koksma's inequality for a Lipschitz integrand**, with the constant `2 L`.  This improves the
constant `3 L` of `koksma_lipschitz`. -/
theorem koksma_lipschitz_two {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 2 * L * discrepancy x N := by
  have hbound := unitVariation_le_of_lipschitz hL hlip
  have hBV : BoundedVariationOn f (Set.Icc (0 : ℝ) 1) :=
    ne_top_of_le_ne_top (by finiteness) hbound
  have hVL : unitVariation f ≤ L := by
    have := ENNReal.toReal_mono (by finiteness) hbound
    rwa [ENNReal.toReal_ofReal hL] at this
  refine (koksma_variation_le hBV x hN).trans ?_
  have hD := discrepancy_nonneg x N
  nlinarith

/-! ### The limiting form -/

/-- A sequence whose discrepancy tends to `0` integrates every function of bounded variation
correctly in the limit. -/
theorem tendsto_average_of_tendsto_discrepancy_variation {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) {x : ℕ → ℝ}
    (hx : Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => 2 * unitVariation f * discrepancy x N) atTop (𝓝 0) := by
    simpa using hx.const_mul (2 * unitVariation f)
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [Real.dist_eq]
  exact koksma_variation_le hf x hN

/-- The concrete instance: for irrational `α` the sequence `α n²` integrates every function of
bounded variation correctly. -/
theorem tendsto_average_quadratic_variation {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (α * n ^ 2))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
  tendsto_average_of_tendsto_discrepancy_variation hf (tendsto_discrepancy_quadratic hα)

end WeylDiscrepancy

end RiemannHypothesis
