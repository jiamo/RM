/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Ceilings of the counting routes, as theorems

Every route of this repository towards a proportion of zeroes on the critical line stops at a
number: `RiemannHypothesis.EightyPercentRoute` stops at `70 %` with multiplicity, and
`RiemannHypothesis.EightyPercentMultiplicity` stops at `86.864 %`.  Until now the reason *why*
a route stops where it stops was recorded only in prose, in the module docstrings and in the
`open_boundary` fields of the task board.  This file turns those reasons into theorems.

The method is the obvious one, and it is the only honest one: a counting route does not use the
zeroes of `ζ`, it uses a handful of **inequalities between counting functions**.  Write those
inequalities down as a constraint system on abstract counts, and then

* prove that the system *implies* the route's conclusion (`onLineMult_ge_of_budget`,
  `onLineMult_ge_of_budgetMult`) — the route is sound; and
* prove that the system is *satisfiable* with the conclusion sharp
  (`exists_windowCounts_budget_sharp`, `exists_windowCounts_budgetMult_sharp`) — so no argument
  that uses only these inequalities can do better.

The two together give an exact ceiling (`budget_ceiling`, `budgetMult_ceiling`): the best
proportion derivable from the distinctness budget `N_d ≥ c·N` together with the off-line budget
`N_off ≤ b·N` is exactly `c − b`, and the best proportion derivable from the *multiplicity*
off-line budget `N_offᵐ ≤ b·N` is exactly `1 − b`.

Substituting the repository's own constants reproduces both of its numbers exactly:

* `c = 5/6` (Theorem C of the vendored library, `RiemannHypothesis.five_sixths_distinct`) and
  `b = 0.13136` (the `ξ′` bad count, `RiemannHypothesis.xiDerivWindowCountBad_le`, transported
  by `SpeiserTransfer`) give the ceiling `5/6 − 0.13136 = 0.70197…`, which is what
  `seventy_percent_on_critical_line_of_speiserTransfer` proves — and it is **less than `4/5`**,
  so the `80 %` target with multiplicity is *not derivable* on that route
  (`eighty_percent_not_derivable_from_budget`);
* the multiplicity-aware off-line budget with the same `b` gives the ceiling
  `1 − 0.13136 = 0.86864`, which is what
  `eighty_six_percent_on_critical_line_mult_of_speiserTransferMult` proves.

Finally `budget_eighty_percent_iff` states exactly what a route of the first kind would need in
order to reach `80 %`: a distinctness constant `c ≥ 4/5 + b = 0.93136`, far beyond the `5/6`
that is available.  This is the formal content of the sentence "the loss comes from the
multiplicity budget `N_d ≥ (5/6)·N`".

## Scope

Nothing here is a statement about `ζ`.  These are theorems about what can and cannot be deduced
from a given set of inequalities between counting functions; their value is that they make the
boundary of a route checkable instead of asserted.  A route that uses *more* than these
inequalities — a new mollifier, a new distinctness theorem — is not covered by them, which is
exactly the point: to move past `c − b` one has to change the inputs, not the argument.
-/

namespace RiemannHypothesis

/-- The counting data of a dyadic window that a counting route manipulates: the number `N` of
nontrivial zeroes counted **with multiplicity**, the number `N_d` of **distinct** ones, the
splitting of the distinct ones into an off-line and an on-line part, and the splitting of the
count with multiplicity into the same two parts.

All the counts are real numbers: a route only ever uses them through linear inequalities, and
the integrality of the counts is never used. -/
structure WindowCounts where
  /-- `N`: the zeroes of the window counted with multiplicity. -/
  total : ℝ
  /-- `N_d`: the distinct zeroes of the window. -/
  distinct : ℝ
  /-- `N_off`: the distinct zeroes of the window off the critical line. -/
  offLine : ℝ
  /-- `N_on`: the distinct zeroes of the window on the critical line. -/
  onLine : ℝ
  /-- `N_offᵐ`: the zeroes off the critical line counted with multiplicity. -/
  offLineMult : ℝ
  /-- `N_onᵐ`: the zeroes on the critical line counted with multiplicity. -/
  onLineMult : ℝ
  total_pos : 0 < total
  offLine_nonneg : 0 ≤ offLine
  onLine_nonneg : 0 ≤ onLine
  /-- the distinct zeroes split into the on-line and the off-line ones -/
  split_distinct : offLine + onLine = distinct
  /-- so do the zeroes counted with multiplicity -/
  split_total : offLineMult + onLineMult = total
  /-- a distinct zero is counted at least once with multiplicity -/
  onLine_le_onLineMult : onLine ≤ onLineMult
  /-- a distinct zero is counted at least once with multiplicity -/
  offLine_le_offLineMult : offLine ≤ offLineMult
  /-- there are at most as many distinct zeroes as zeroes with multiplicity -/
  distinct_le_total : distinct ≤ total

namespace WindowCounts

/-- The constraint system of the route of `RiemannHypothesis.EightyPercentRoute`: a
**distinctness budget** `N_d ≥ c·N` and an off-line budget `N_off ≤ b·N` for the *distinct*
off-line zeroes.  The repository's instance is `c = 5/6`, `b = 0.13136`. -/
def SatisfiesBudget (c b : ℝ) (W : WindowCounts) : Prop :=
  c * W.total ≤ W.distinct ∧ W.offLine ≤ b * W.total

/-- The constraint system of the route of `RiemannHypothesis.EightyPercentMultiplicity`: the
off-line budget is available for the zeroes counted **with multiplicity**, `N_offᵐ ≤ b·N`.  No
distinctness budget is needed. -/
def SatisfiesBudgetMult (b : ℝ) (W : WindowCounts) : Prop :=
  W.offLineMult ≤ b * W.total

/-! ## The first system: distinctness budget plus a budget for the distinct off-line zeroes -/

/-- **Soundness of the route.**  From `N_d ≥ c·N` and `N_off ≤ b·N` the on-line count with
multiplicity is at least `(c − b)·N`. -/
theorem onLineMult_ge_of_budget {c b : ℝ} {W : WindowCounts} (h : W.SatisfiesBudget c b) :
    (c - b) * W.total ≤ W.onLineMult := by
  obtain ⟨hd, ho⟩ := h
  have hsplit := W.split_distinct
  have hle := W.onLine_le_onLineMult
  nlinarith [hsplit, hle, hd, ho]

/-- **The route is saturated.**  For every pair of constants `0 ≤ b ≤ c ≤ 1` there is a window
satisfying the whole constraint system in which the on-line count with multiplicity is exactly
`(c − b)·N`. -/
theorem exists_windowCounts_budget_sharp {c b : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    ∃ W : WindowCounts, W.SatisfiesBudget c b ∧ W.onLineMult = (c - b) * W.total := by
  refine ⟨{ total := 1
            distinct := c
            offLine := b
            onLine := c - b
            offLineMult := 1 - (c - b)
            onLineMult := c - b
            total_pos := by norm_num
            offLine_nonneg := hb
            onLine_nonneg := by linarith
            split_distinct := by ring
            split_total := by ring
            onLine_le_onLineMult := le_rfl
            offLine_le_offLineMult := by linarith
            distinct_le_total := hc },
          ⟨by change c * (1 : ℝ) ≤ c; simp, by change (b : ℝ) ≤ b * 1; simp⟩, ?_⟩
  simp

/-- **The exact ceiling of the route.**  A proportion `p` of the zeroes on the critical line,
counted with multiplicity, is derivable from the distinctness budget `N_d ≥ c·N` and the
off-line budget `N_off ≤ b·N` **if and only if** `p ≤ c − b`. -/
theorem budget_ceiling {c b p : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    (∀ W : WindowCounts, W.SatisfiesBudget c b → p * W.total ≤ W.onLineMult) ↔ p ≤ c - b := by
  constructor
  · intro h
    obtain ⟨W, hW, hsharp⟩ := exists_windowCounts_budget_sharp hb hbc hc
    have := h W hW
    rw [hsharp] at this
    have hpos := W.total_pos
    nlinarith [this, hpos]
  · intro hp W hW
    have := onLineMult_ge_of_budget hW
    nlinarith [this, W.total_pos, hp]

/-- **The `80 %` target is not derivable from the multiplicity budget.**  With the repository's
constants `c = 5/6` (Theorem C) and `b = 0.13136` (the `ξ′` bad count) the constraint system is
satisfiable by a window in which fewer than `80 %` of the zeroes, counted with multiplicity, lie
on the critical line.  Hence no argument using only those two inequalities proves the `80 %`
target — the `70 %` of `seventy_percent_on_critical_line_of_speiserTransfer` is not a defect of
the write-up. -/
theorem eighty_percent_not_derivable_from_budget :
    ¬ ∀ W : WindowCounts, W.SatisfiesBudget (5 / 6) 0.13136 → (4 / 5) * W.total ≤ W.onLineMult := by
  intro h
  have := (budget_ceiling (c := 5 / 6) (b := 0.13136) (p := 4 / 5)
    (by norm_num) (by norm_num) (by norm_num)).1 h
  norm_num at this

/-- The ceiling of the route is exactly the `70.197…%` that the repository proves: the constant
`5/6 − 0.13136` is `0.70197…`, and it is smaller than `4/5`. -/
theorem budget_ceiling_value :
    (5 / 6 - 0.13136 : ℝ) < 0.702 ∧ (0.7 : ℝ) < 5 / 6 - 0.13136 ∧
      (5 / 6 - 0.13136 : ℝ) < 4 / 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **What a route of this kind would need in order to reach `80 %`.**  With the off-line budget
`b`, the `80 %` target is derivable if and only if the distinctness budget is at least
`4/5 + b`; for `b = 0.13136` that is `c ≥ 0.93136`, well beyond the `5/6 = 0.8333…` of
Theorem C. -/
theorem budget_eighty_percent_iff {c b : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    (∀ W : WindowCounts, W.SatisfiesBudget c b → (4 / 5) * W.total ≤ W.onLineMult)
      ↔ 4 / 5 + b ≤ c := by
  rw [budget_ceiling hb hbc hc]
  constructor <;> intro h <;> linarith

/-! ## The second system: an off-line budget with multiplicity -/

/-- **Soundness of the multiplicity-aware route.**  From `N_offᵐ ≤ b·N` alone the on-line count
with multiplicity is at least `(1 − b)·N`. -/
theorem onLineMult_ge_of_budgetMult {b : ℝ} {W : WindowCounts} (h : W.SatisfiesBudgetMult b) :
    (1 - b) * W.total ≤ W.onLineMult := by
  have hsplit := W.split_total
  have h' : W.offLineMult ≤ b * W.total := h
  nlinarith [h', hsplit]

/-- **The multiplicity-aware route is saturated.**  For `0 ≤ b ≤ 1` there is a window satisfying
the constraint in which the on-line count with multiplicity is exactly `(1 − b)·N`. -/
theorem exists_windowCounts_budgetMult_sharp {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ W : WindowCounts, W.SatisfiesBudgetMult b ∧ W.onLineMult = (1 - b) * W.total := by
  refine ⟨{ total := 1
            distinct := 1
            offLine := b
            onLine := 1 - b
            offLineMult := b
            onLineMult := 1 - b
            total_pos := by norm_num
            offLine_nonneg := hb
            onLine_nonneg := by linarith
            split_distinct := by ring
            split_total := by ring
            onLine_le_onLineMult := le_rfl
            offLine_le_offLineMult := le_rfl
            distinct_le_total := le_rfl }, by change (b : ℝ) ≤ b * 1; simp, ?_⟩
  simp

/-- **The exact ceiling of the multiplicity-aware route.**  A proportion `p` on the critical line
with multiplicity is derivable from `N_offᵐ ≤ b·N` if and only if `p ≤ 1 − b`.  At
`b = 0.13136` this is the `86.864 %` of
`eighty_six_percent_on_critical_line_mult_of_speiserTransferMult`, and it does clear the `80 %`
target — the difference between the two routes is exactly whether the off-line budget is
available with multiplicity. -/
theorem budgetMult_ceiling {b p : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∀ W : WindowCounts, W.SatisfiesBudgetMult b → p * W.total ≤ W.onLineMult) ↔ p ≤ 1 - b := by
  constructor
  · intro h
    obtain ⟨W, hW, hsharp⟩ := exists_windowCounts_budgetMult_sharp hb hb1
    have := h W hW
    rw [hsharp] at this
    nlinarith [this, W.total_pos]
  · intro hp W hW
    have := onLineMult_ge_of_budgetMult hW
    nlinarith [this, W.total_pos, hp]

/-- The two ceilings side by side: the distinct-zero budget caps the route below `80 %`, the
multiplicity budget does not. -/
theorem eighty_percent_derivable_from_budgetMult :
    ∀ W : WindowCounts, W.SatisfiesBudgetMult 0.13136 → (4 / 5) * W.total ≤ W.onLineMult :=
  (budgetMult_ceiling (b := 0.13136) (p := 4 / 5) (by norm_num) (by norm_num)).2 (by norm_num)

end WindowCounts

end RiemannHypothesis
