# M2-METHOD-CEILING — the ceilings of the counting routes, as theorems

Date: 2026-08-26
File: `RiemannHypothesis/MethodCeiling.lean`
Related: `RiemannHypothesis/EightyPercentRoute.lean` (the `70.197 %` route),
`RiemannHypothesis/EightyPercentMultiplicity.lean` (the `86.864 %` route)

## Claim

Until now, *why* a counting route stops where it stops was recorded only in prose — in module
docstrings and in the `open_boundary` fields of this board.  This row turns those reasons into
theorems.

A counting route does not use the zeroes of `ζ`; it uses a handful of inequalities between
counting functions.  `WindowCounts` is those counting functions as abstract reals (`N`, `N_d`,
`N_off`, `N_on`, `N_offᵐ`, `N_onᵐ`) with the split and monotonicity relations that hold for any
window.  Two constraint systems are singled out, one for each route:

    SatisfiesBudget c b   :  c·N ≤ N_d  ∧  N_off ≤ b·N
    SatisfiesBudgetMult b :  N_offᵐ ≤ b·N

and for each the *exact* ceiling is proved:

    budget_ceiling     : (∀ W, SatisfiesBudget c b W → p·N ≤ N_onᵐ) ↔ p ≤ c − b
    budgetMult_ceiling : (∀ W, SatisfiesBudgetMult b W → p·N ≤ N_onᵐ) ↔ p ≤ 1 − b

The `→` direction of each is the soundness of the route (`onLineMult_ge_of_budget`,
`onLineMult_ge_of_budgetMult`); the `←` direction is a saturating witness
(`exists_windowCounts_budget_sharp`, `exists_windowCounts_budgetMult_sharp`), which is what makes
the number a ceiling and not merely a bound.

Substituting the repository's own constants reproduces both of its numbers exactly:

* `c = 5/6` (Theorem C of the vendored library) and `b = 0.13136` (the `ξ′` bad count transported
  by `SpeiserTransfer`) give `5/6 − 0.13136 = 0.70197…`, the constant of
  `seventy_percent_on_critical_line_of_speiserTransfer`, and
  `eighty_percent_not_derivable_from_budget` shows `80 %` is **not** derivable from those two
  inequalities;
* the multiplicity-aware budget with the same `b` gives `1 − 0.13136 = 0.86864`, the constant of
  `eighty_six_percent_on_critical_line_mult_of_speiserTransferMult`, and that one does clear
  `80 %` (`eighty_percent_derivable_from_budgetMult`).

`budget_eighty_percent_iff` states what a route of the first kind would need in order to reach
`80 %`: a distinctness constant `c ≥ 4/5 + b = 0.93136`.

## Scope

Nothing here is a statement about `ζ`.  These are theorems about what can and cannot be deduced
from a given set of inequalities between counting functions.  A route that uses *more* than these
inequalities — a new mollifier, a new distinctness theorem — is not covered, which is the point:
to pass `c − b` one has to change the inputs, not the argument.

## Adversarial revalidation: M2-METHOD-CEILING

* The module is imported by `RiemannHypothesis.lean`, `lake build` succeeds, and the file
  contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `budget_ceiling`, `budgetMult_ceiling`, `eighty_percent_not_derivable_from_budget` and
  `eighty_percent_derivable_from_budgetMult`.
* The theorems are not vacuous: `WindowCounts` is inhabited, and both constraint systems are
  satisfiable — the two saturation lemmas construct explicit witnesses, so the `↔` has content in
  both directions.
* The negative statement `eighty_percent_not_derivable_from_budget` is a genuine impossibility
  result about a constraint system, not a claim that `80 %` is false; the multiplicity-aware
  route in the same file proves `86.864 %`.
* The module imports only Mathlib and depends on no unproved `Prop` of this repository.  Three
  entries do appear in `docs/goal/conditional-theorems.txt` — the soundness lemmas
  `onLineMult_ge_of_budget`, `onLineMult_ge_of_budgetMult` and
  `eighty_percent_derivable_from_budgetMult`, each listed as depending on `SatisfiesBudget` or
  `SatisfiesBudgetMult`.  Those two are *definitions* introduced in this very file, spelling out
  the constraint system whose ceiling is being computed; they are not conjectures awaiting proof,
  and the two `↔` theorems that state the ceilings are unconditional.
