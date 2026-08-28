/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.

Further local modification (2026): the original implementation reused the internals of
Mathlib's `Mathlib.Tactic.LinearCombination'` module (`expandLinearCombo`, `Expanded`,
`eq_of_add`, …).  That module no longer exists in the Mathlib pinned by this repository, so the
tactic is now implemented directly from the three group lemmas below, with the same surface
syntax for the fragment that this repository uses (sums, differences and negations of proofs of
equalities in an additive group, normalized with `abel`).
-/
/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Abel

/-!
# additive_combination Tactic

In this file, the `additive_combination` tactic is created.  This tactic, which
works over `AddGroup`s, attempts to simplify the target by creating an additive combination
of a list of equalities and subtracting it from the target.

## Implementation Notes

This tactic works by creating the sum of the given equations, subtracting the right side of
that sum from its left side, doing the same with the target, and then asking `abel` to prove
that the difference of the two vanishes.
-/

namespace Zeta23.Tactic.AdditiveCombination

variable {α : Type*} [AddGroup α] {a b c d a' b' : α}

theorem add_pf (p₁ : a = b) (p₂ : c = d) : a + c = b + d := by rw [p₁, p₂]

theorem sub_pf (p₁ : a = b) (p₂ : c = d) : a - c = b - d := by rw [p₁, p₂]

theorem neg_pf (p : a = b) : -a = -b := by rw [p]

theorem eq_of_add (p : a = b) (H : a' - b' - (a - b) = 0) : a' = b' := by
  rw [p, sub_self, sub_zero, sub_eq_zero] at H
  exact H

/-- `acomb% e` turns a sum/difference/negation of proofs of equalities into a proof of the
corresponding equality. -/
syntax (name := acombTerm) "acomb% " term : term

macro_rules
  | `(acomb% $e) => `($e)
macro_rules
  | `(acomb% ($e)) => `(acomb% $e)
macro_rules
  | `(acomb% $e₁ + $e₂) => `(add_pf (acomb% $e₁) (acomb% $e₂))
macro_rules
  | `(acomb% $e₁ - $e₂) => `(sub_pf (acomb% $e₁) (acomb% $e₂))
macro_rules
  | `(acomb% -$e) => `(neg_pf (acomb% $e))
/--
`additive_combination e` attempts to close a goal `a' = b'` in an additive group, where `e` is a
sum/difference of proofs of equalities: it forms the corresponding equality `a = b` and asks
`abel` to prove `a' - b' - (a - b) = 0`.

```
example (x y : ℤ) (h1 : x + 2*y = 1) (h2 : x = y) : 2*x + 2*y = 1 + y := by
  additive_combination h1 + h2
```
-/
syntax (name := additiveCombinationTactic) "additive_combination" (ppSpace colGt term) : tactic

macro_rules
  | `(tactic| additive_combination $e) =>
    `(tactic| (refine eq_of_add (acomb% $e) ?_
               try simp only [smul_add, smul_sub]
               abel))

end Zeta23.Tactic.AdditiveCombination
