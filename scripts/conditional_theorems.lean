/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis
import Lean

/-!
# The conditional/unconditional boundary, machine-checked

A theorem of this repository is **conditional** when one of its hypotheses mentions a `Prop`
that this repository *states but does not prove* — `ZetaForm`, `ZetaStripForm`, the entries of
`RiemannHypothesis/Partial.lean`, `SpeiserTransfer`, and so on.  Such a theorem says nothing
unconditional, however strong it looks.

This script computes that boundary from the environment instead of from docstrings:

1. it collects every constant declared in this repository that is a *statement* — a
   definition (not a theorem) whose type is a telescope ending in `Prop`;
2. it discards those for which the environment contains a proof — a constant whose type is
   that `Prop`, applied to any arguments;
3. it prints every theorem of this repository one of whose hypotheses mentions one of the
   remaining, unproved, statements, in the form

   ```
   theoremName <- unprovedProp1, unprovedProp2
   ```

`scripts/audit.sh` diffs the output against `docs/goal/conditional-theorems.txt`, so a new
conditional theorem cannot be added without recording it.  Run

```bash
lake env lean scripts/conditional_theorems.lean > docs/goal/conditional-theorems.txt
```

to regenerate the manifest.
-/

open Lean

namespace ConditionalAudit

/-- Is `m` a module of this repository (as opposed to mathlib or `Zeta23`)? -/
def isProjectModule (m : Name) : Bool :=
  m == `RiemannHypothesis || (`RiemannHypothesis).isPrefixOf m || m == `Solution
    || m == `Challenge

/-- The module a constant was declared in, `none` for the module being elaborated. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Is `n` declared in this repository?  Decided by the module the constant comes from, with
the namespace as a fallback for the (never used here) case of a constant declared in the file
being elaborated. -/
def isProjectConst (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => isProjectModule m
  | none => isProjectModule n.getRoot

/-- Does the type `e` end in `Prop`?  Such a definition is a *statement*: `def P : Prop`, or
`def P (x : α) : Prop`. -/
partial def resultIsProp : Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .mdata _ e => resultIsProp e
  | .sort .zero => true
  | _ => false

/-- The constants occurring in the *hypotheses* (the binder domains) of a `∀`-type. -/
partial def hypothesisConsts (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .forallE _ d b _ => hypothesisConsts b (d.getUsedConstants.foldl (fun a c => a.push c) acc)
  | .mdata _ e => hypothesisConsts e acc
  | _ => acc

end ConditionalAudit

open ConditionalAudit in
run_cmd do
  let env ← Lean.getEnv
  -- 1. the statements of this repository: `Prop`-valued definitions, not proofs
  let mut statements : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    if !n.isInternal && isProjectConst env n then
      match ci with
      | .defnInfo _ | .opaqueInfo _ =>
        if resultIsProp ci.type then statements := statements.insert n
      | _ => pure ()
  -- 2. drop the ones that have a proof somewhere in the environment
  let mut proved : Std.HashSet Name := {}
  for (_, ci) in env.constants.toList do
    if let some c := ci.type.getAppFn.constName? then
      if statements.contains c then proved := proved.insert c
  let unproved : Array Name :=
    statements.toArray.filter (fun n => !proved.contains n) |>.qsort (·.lt ·)
  -- 3. the theorems whose hypotheses mention one of them
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if !n.isInternal && isProjectConst env n then
      match ci with
      | .thmInfo _ =>
        let used := hypothesisConsts ci.type #[]
        let hit := unproved.filter (fun p => used.contains p)
        if hit.size != 0 then
          lines := lines.push
            s!"{n} <- {String.intercalate ", " (hit.toList.map toString)}"
      | _ => pure ()
  for l in lines.qsort (· < ·) do
    IO.println l
