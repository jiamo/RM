/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis
import Solution
import Lean

/-!
# Exhaustive axiom audit

`scripts/audit.sh` pins a hand-maintained list of `#print axioms` commands.  A hand-maintained
list can only ever cover the theorems somebody remembered to add to it: at the time this file
was written it covered 719 of the 2030 theorems the library exports, so about two thirds of
the corpus had no axiom check at all, and a new theorem was a blind spot until a line was added
for it.

This script removes that failure mode.  It walks the whole environment, and for **every**
theorem declared in a module of this repository (`RiemannHypothesis*`, `Solution`, `Challenge`)
it collects the axioms the proof actually depends on, exactly as `#print axioms` does.  It then
reports every theorem whose axiom set is not contained in Lean's three standard axioms
`propext`, `Classical.choice`, `Quot.sound` — in particular every theorem that depends,
however indirectly, on the placeholder axiom Lean introduces for an unfinished proof.

Output: one line per offending theorem, then a summary line

```
AXIOM AUDIT: <n> theorems checked, <k> outside the standard three
```

and, if `k = 0` apart from the deliberate `Challenge.lean` placeholders, the line `OK`.
The three `Challenge.lean` statements are the repository's statement-of-record file and are
left unproved by design (`Solution.lean` proves each of them from `RiemannHypothesis.Main`);
they are listed separately and are not counted as failures.

Run with

    lake env lean scripts/axiom_audit.lean
-/

open Lean

namespace AxiomAudit

/-- Modules whose theorems this audit is responsible for. -/
def isProjectModule (m : Name) : Bool :=
  m == `RiemannHypothesis || (`RiemannHypothesis).isPrefixOf m || m == `Solution
    || m == `Challenge

/-- Lean's three standard axioms. -/
def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Auto-generated or internal names: covered by whatever user-facing result uses them. -/
def isInternalName (n : Name) : Bool :=
  n.isInternal || isPrivateName n
    || n.components.any fun c =>
        let s := c.toString
        s.startsWith "_" || s.startsWith "proof_" || s.startsWith "match_"

end AxiomAudit

open AxiomAudit in
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← getEnv
  let mut checked := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut placeholders : Array Name := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
      if isInternalName n then continue
      match env.getModuleIdxFor? n with
      | none => pure ()
      | some idx =>
        let some mod := env.header.moduleNames[idx.toNat]? | pure ()
        if !isProjectModule mod then continue
        checked := checked + 1
        let axs ← collectAxioms n
        let extra := axs.filter fun a => !standardAxioms.contains a
        if extra.isEmpty then continue
        if mod == `Challenge then
          placeholders := placeholders.push n
        else
          bad := bad.push (n, extra)
    | _ => pure ()
  for n in placeholders do
    IO.println s!"placeholder (Challenge.lean, unproved by design): {n}"
  for (n, extra) in bad do
    IO.println s!"NONSTANDARD {n} : {extra.toList}"
  IO.println s!"AXIOM AUDIT: {checked} theorems checked, {bad.size} outside the standard three"
  if bad.isEmpty then IO.println "OK"
