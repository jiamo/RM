/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylLinear

/-!
# The counting form of equidistribution for an arbitrary arc of the circle

`RiemannHypothesis.WeylCountGeneral` proves the counting form of equidistribution for every
subinterval `[a, b) ⊆ [0, 1]`.  An arc of the circle `ℝ/ℤ` need not be of that shape: the arc
running from `a` forwards through the point `0` to `b < a` is described in `[0, 1)` by the
*wrap-around* set `[a, 1) ∪ [0, b)`.  Its length is `(1 − a) + b`, and this module proves the
counting statement for it, closing the last gap named in the open boundary of the previous row.

## Main results

* `countIn_eq_zero_of_le` — an empty interval catches nothing.
* `tendsto_countIn_div_of_le'` — the counting statement for `0 ≤ a ≤ b ≤ 1`, the degenerate case
  `a = b` included.
* `countArc`, `countArc_eq_add` — the wrap-around counting function, and its splitting into the
  two ordinary pieces.
* `tendsto_countArc_div` — **the counting form for an arbitrary arc**: for `0 ≤ b ≤ a ≤ 1`,
  `#{n < N : {xₙ} ∈ [a, 1) ∪ [0, b)} / N → (1 − a) + b`.
* `tendsto_countArc_div_quadratic`, `tendsto_countArc_div_linear` — the specializations to
  `α n²` and to `α n` with `α` irrational.

## Scope

As in the previous rows no rate of convergence is claimed, and nothing here concerns `ζ`.
-/

noncomputable section

open Filter Finset Topology

namespace RiemannHypothesis

namespace WeylCount

open WeylCriterion

/-- An interval `[a, b)` with `b ≤ a` is empty, so it catches no term. -/
theorem countIn_eq_zero_of_le (x : ℕ → ℝ) {a b : ℝ} (hba : b ≤ a) (N : ℕ) :
    countIn x a b N = 0 := by
  classical
  unfold countIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n - ⟨h1, h2⟩
  linarith

/-- **The counting form of equidistribution for every `0 ≤ a ≤ b ≤ 1`**, the degenerate interval
`a = b` included. -/
theorem tendsto_countIn_div_of_le' {x : ℕ → ℝ} (h : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [countIn_eq_zero_of_le x (le_refl a)]
  · exact tendsto_countIn_div_of_le h ha hlt hb

/-- The number of `n < N` whose fractional part lies in the wrap-around arc `[a, 1) ∪ [0, b)`. -/
def countArc (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n =>
    (a ≤ Int.fract (x n) ∧ Int.fract (x n) < 1) ∨
      (0 ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card

/-- For `b ≤ a` the two pieces of the arc are disjoint, so the counts add. -/
theorem countArc_eq_add (x : ℕ → ℝ) {a b : ℝ} (hba : b ≤ a) (N : ℕ) :
    countArc x a b N = countIn x a 1 N + countIn x 0 b N := by
  classical
  unfold countArc countIn
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  rintro n - ⟨h1, -⟩ ⟨-, h2⟩
  linarith

/-- **The counting form of equidistribution for an arbitrary arc of the circle**: for
`0 ≤ b ≤ a ≤ 1` the proportion of the first `N` terms whose fractional part lies in the
wrap-around arc `[a, 1) ∪ [0, b)` tends to its length `(1 − a) + b`. -/
theorem tendsto_countArc_div {x : ℕ → ℝ} (h : EquidistributedMod1 x) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Tendsto (fun N : ℕ => (countArc x a b N : ℝ) / N) atTop (𝓝 ((1 - a) + b)) := by
  have hup := tendsto_countIn_div_of_le' h (le_trans hb hba) ha (le_refl (1 : ℝ))
  have hlow := tendsto_countIn_div_of_le' h (le_refl (0 : ℝ)) hb (le_trans hba ha)
  have hsum := hup.add hlow
  rw [show b - 0 = b by ring] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div]
  congr 1
  rw [countArc_eq_add x hba N]
  push_cast
  ring

/-- **Weyl's theorem for `α n²` on an arbitrary arc of the circle.** -/
theorem tendsto_countArc_div_quadratic {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Tendsto (fun N : ℕ => (countArc (fun n : ℕ => α * (n : ℝ) ^ 2) a b N : ℝ) / N) atTop
      (𝓝 ((1 - a) + b)) :=
  tendsto_countArc_div (equidistributedMod1_quadratic hα) hb hba ha

/-- **Weyl's theorem for `α n` on an arbitrary arc of the circle.** -/
theorem tendsto_countArc_div_linear {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Tendsto (fun N : ℕ => (countArc (fun n : ℕ => α * (n : ℝ)) a b N : ℝ) / N) atTop
      (𝓝 ((1 - a) + b)) :=
  tendsto_countArc_div (equidistributedMod1_linear hα) hb hba ha

end WeylCount

end RiemannHypothesis
