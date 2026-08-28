/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCountGeneral

/-!
# Weyl's theorem for a linear sequence

The quadratic case `α n²` was treated in `RiemannHypothesis.WeylEquidistribution` and
`RiemannHypothesis.WeylCriterion`, where the differencing machinery of the van der Corput A
process was needed.  The linear case `α n` needs none of it: the exponential sum is geometric,
and the bound `‖∑_{n < N} e(θ n + c)‖ ≤ 1/(2 ‖θ‖)` for the distance `‖θ‖` of `θ` to the nearest
integer — proved in `RiemannHypothesis.WeylQuadratic` — is already uniform in `N`.

## Main results

* `weylSumsVanish_linear` — for `α` irrational the exponential sums of `α n` at every nonzero
  frequency are `O(1)`, hence `o(N)`.
* `equidistributedMod1_linear` — **the fractional parts of `α n` are equidistributed** for every
  irrational `α`.
* `tendsto_countIn_div_linear` — the counting form: for `0 ≤ a < b ≤ 1`,
  `#{n < N : Int.fract (α n) ∈ [a, b)} / N → b − a`.

## Scope

The bound behind the theorem is `1/(2‖mα‖)`, which is uniform in `N` but not effective in `α`,
so no rate of convergence is claimed.  Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory

namespace RiemannHypothesis

namespace WeylCount

open KusminLandau WeylQuadratic WeylEquidistribution WeylCriterion

/-- For `α` irrational the exponential sums of the linear sequence `α n` are bounded, hence
their normalizations vanish. -/
theorem weylSumsVanish_linear {α : ℝ} (hα : Irrational α) :
    WeylSumsVanish (fun n : ℕ => α * (n : ℝ)) := by
  intro m hm
  have hirr : Irrational ((m : ℝ) * α) := hα.intCast_mul hm
  have hne : intDist ((m : ℝ) * α) ≠ 0 := (intDist_pos_of_irrational hirr).ne'
  set C : ℝ := 1 / (2 * intDist ((m : ℝ) * α)) with hC
  have hbound : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * (α * (n : ℝ)))‖ ≤ C := by
    intro N
    have hsum : ∑ n ∈ Finset.range N, e2pi ((m : ℝ) * (α * (n : ℝ)))
        = ∑ n ∈ Finset.range N, e2pi (((m : ℝ) * α) * (n : ℝ) + 0) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      ring
    rw [hsum]
    exact norm_geomSum_e2pi_le hne N 0
  refine squeeze_zero (fun N => by positivity) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat C)
  gcongr
  exact hbound N

/-- **The fractional parts of `α n` are equidistributed** for every irrational `α`. -/
theorem equidistributedMod1_linear {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => α * (n : ℝ)) :=
  (equidistributedMod1_iff_weylSumsVanish _).2 (weylSumsVanish_linear hα)

/-- **Weyl's theorem for a linear sequence, in its counting form**: for every irrational `α` and
every `0 ≤ a < b ≤ 1`, the proportion of `n < N` with `Int.fract (α n) ∈ [a, b)` tends to
`b − a`. -/
theorem tendsto_countIn_div_linear {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn (fun n : ℕ => α * (n : ℝ)) a b N : ℝ) / N) atTop
      (𝓝 (b - a)) :=
  tendsto_countIn_div_of_le (equidistributedMod1_linear hα) ha hab hb

end WeylCount

end RiemannHypothesis
