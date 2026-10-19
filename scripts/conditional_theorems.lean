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

1. it collects every constant declared in this repository **or in the vendored `Zeta23`
   library** that is a *statement* — a definition, structure, class or inductive (not a
   theorem) whose type is a telescope ending in `Prop` — together with Mathlib's own
   `RiemannHypothesis`, for which `ZetaForm` is an `abbrev`;
2. it discards a hypothesis for which the environment contains a proof — a constant whose
   type is *that very proposition*, arguments included, so that a statement proved for one
   argument (`EF_lit` for `ζ`'s zero configuration) does not silently discharge the same
   statement at another argument;
3. it prints every theorem of this repository one of whose hypotheses mentions one of the
   remaining, unproved, statements, in the form

   ```
   theoremName <- unprovedProp1, unprovedProp2
   ```

One limit is worth stating.  When a hypothesis still contains loose bound variables — the
shape `∀ Z, EF_lit Z → ⋯`, where the proposition depends on an argument of the theorem — there
is no closed proposition to look for, and the script falls back to asking whether the head
constant is proved anywhere.  Such a theorem is quantified over its assumption rather than
resting on it, which is the `DEFINITIONAL` case above, so the fallback loses nothing that the
conditional/unconditional boundary is about.

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

/-- Is `m` a module of the vendored `Zeta23` library?  Its statements are scanned too: a
theorem of this repository that assumes one of `Zeta23`'s own hypotheses (`PaperInputs`,
`EF_lit`, `RiemannVonMangoldt`, …) is conditional in exactly the same way as one that assumes
a `Prop` stated here, and restricting the scan to this repository's own modules would miss
it. -/
def isVendorModule (m : Name) : Bool :=
  m == `Zeta23 || (`Zeta23).isPrefixOf m

/-- Is `m` a module of the absorbed openai/math family-003 closure
(`RiemannHypothesis/Family003/`, see `docs/family003/README.md`)?  Like the vendored `Zeta23`
library, its `Prop`-valued definitions are *statements* in the sense of step 1, so a theorem of
this repository that assumes one of them is still reported; but its own theorems are upstream
intermediate lemmas (about 1400 of them take a `Prop`-valued structure of the upstream
development as a hypothesis, exactly as a Mathlib lemma takes `[IsDomain R]`) and are not
listed in step 3.  What the boundary is about is the public endpoints built on that closure
(`QuasiRiemann`, `DirichletSevenEighths`, `HeckeSevenEighths`, `SiegelZeroGap`); they live
outside `Family003/`, are scanned, and assume none of these statements. -/
def isAbsorbedModule (m : Name) : Bool :=
  (`RiemannHypothesis.Family003).isPrefixOf m

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

/-- Every occurrence, anywhere inside `e`, of an application of one of the constants in `S`,
as a whole application (`ZetaStripForm`, `PartialSumBound f`, `EF_lit cfg`, …).  Occurrences
under a negation, inside a nested arrow or under a binder are all found. -/
partial def statementApps (S : Std.HashSet Name) (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let acc := match f.constName? with
      | some c => if S.contains c then acc.push e else acc
      | none => statementApps S f acc
    e.getAppArgs.foldl (fun a x => statementApps S x a) acc
  | .const c _ => if S.contains c then acc.push e else acc
  | .lam _ t b _ | .forallE _ t b _ => statementApps S b (statementApps S t acc)
  | .letE _ t v b _ => statementApps S b (statementApps S v (statementApps S t acc))
  | .mdata _ e => statementApps S e acc
  | .proj _ _ e => statementApps S e acc
  | _ => acc

/-- The *hypotheses* (binder domains) of a `∀`-type. -/
partial def hypotheses (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .forallE _ d b _ => hypotheses b (acc.push d)
  | .mdata _ e => hypotheses e acc
  | _ => acc

/-! ## Classifying the unproved statements

Not every unproved `Prop` of this repository is an open assumption.  Three kinds occur, and
mixing them dilutes the signal the audit exists to give:

* `OPEN` — a statement this repository would like to prove and cannot: the Riemann hypothesis
  itself in its several forms, the Lindelöf hypothesis, and the five arithmetic criteria
  equivalent to the conjecture.  (The approximate functional equation `AFECriticalLine` was in
  this list until 2026-10-19, when `afeCriticalLine : AFECriticalLine 250` proved it; the two
  theorems that take it as a hypothesis are therefore no longer reported.)  A theorem assuming one of
  these says nothing unconditional.
* `DEFINITIONAL` — a property of an *argument* of the theorem, not an assumption about `ζ`:
  `EquidistributedMod1`, `WeylSumsVanish` and `CountsEquidistribute` are the three sides of
  Weyl's criterion ("a sequence is equidistributed iff its Weyl sums vanish iff every
  subinterval receives its share of the fractional parts"), and `PartialSumBound`,
  `SqrtCancellation`, `IsPositiveTestFunction`, `SatisfiesBudget`, `SatisfiesBudgetMult` are
  hypotheses on a sequence, a test function or a window count supplied by the caller, and
  `WeylGeneral.IsPolyPhase d α f` is the property "`f` is a polynomial phase of degree at most
  `d` with leading coefficient `α`" of the phase function supplied by the caller.  These
  are characterizations, not open problems, and a theorem quantified over them is
  unconditional in the sense that matters.  `RHCounts` belongs here too: it is the property
  "this abstract counting configuration has no off-line zeroes" of an argument of the theorem,
  and it occurs only *negated*, in the non-derivability results of
  `RiemannHypothesis/CorpusCeiling.lean`, which are unconditional theorems about a constraint
  system and assume nothing about `ζ`.  `UniformDensity` is likewise a hypothesis on the
  abstract corpus supplied by the caller, used there to measure what a density bound uniform in
  the distance to the critical line would contribute.  `WellSpaced.Separated δ Λ` ("the
  frequencies `Λ` are `δ`-separated") and `Vinogradov.VinogradovEq k s x` ("the tuple `x`
  solves the Vinogradov system of degree `k` in `2s` variables") are of the same kind:
  properties of an argument supplied by the caller.
* `ROUTE_CLOSED` — a hypothesis of a route that has been abandoned: the Speiser transfer
  family, whose direction is the reverse of the free inequality (see the hypothesis-hygiene
  section of `AGENTS.md`).  Kept for the record, not to be built on.

An unproved `Prop` that appears in no list is reported as `UNCLASSIFIED`, so a new one cannot
slip in unnoticed.
-/

/-- Statements this repository cannot prove: open problems. -/
def openStatements : List Name :=
  [`RiemannHypothesis.ZetaForm,
   `RiemannHypothesis.ZetaStripForm,
   `RiemannHypothesis.LindelofHypothesis,
   `RiemannHypothesis.ChebyshevBoundForm,
   `RiemannHypothesis.LiouvilleBoundForm,
   `RiemannHypothesis.MertensBoundForm,
   `RiemannHypothesis.LittleMertensBoundForm,
   `RiemannHypothesis.RedhefferBoundForm,
   `RiemannHypothesis.EightyPercentOnCriticalLine]

/-- Properties of an argument of the theorem: characterizations, not open assumptions. -/
def definitionalStatements : List Name :=
  [`RiemannHypothesis.WeylCriterion.EquidistributedMod1,
   `RiemannHypothesis.WeylCriterion.WeylSumsVanish,
   `RiemannHypothesis.WeylPortmanteau.CountsEquidistribute,
   `RiemannHypothesis.IsPositiveTestFunction,
   `RiemannHypothesis.PartialSumBound,
   `RiemannHypothesis.SqrtCancellation,
   `RiemannHypothesis.WindowCounts.SatisfiesBudget,
   `RiemannHypothesis.WindowCounts.SatisfiesBudgetMult,
   `RiemannHypothesis.RHCounts,
   `RiemannHypothesis.UniformDensity,
   `RiemannHypothesis.WeylGeneral.IsPolyPhase,
   `RiemannHypothesis.WellSpaced.Separated,
   `RiemannHypothesis.Vinogradov.VinogradovEq]

/-- Hypotheses of routes that have been closed; kept for the record. -/
def routeClosedStatements : List Name :=
  [`RiemannHypothesis.SpeiserTransfer,
   `RiemannHypothesis.SpeiserTransferMult,
   `RiemannHypothesis.SpeiserOffLineTransfer]

/-- The tag of an unproved statement. -/
def tagOf (n : Name) : String :=
  if openStatements.contains n then "OPEN"
  else if definitionalStatements.contains n then "DEFINITIONAL"
  else if routeClosedStatements.contains n then "ROUTE_CLOSED"
  else "UNCLASSIFIED"

/-- Severity order, worst first: the tag of a theorem is the worst tag of its hypotheses. -/
def severity (tag : String) : Nat :=
  match tag with
  | "UNCLASSIFIED" => 0
  | "OPEN" => 1
  | "ROUTE_CLOSED" => 2
  | _ => 3

end ConditionalAudit

open ConditionalAudit in
run_cmd do
  let env ← Lean.getEnv
  -- 1. the statements of this repository and of the vendored library: `Prop`-valued
  --    definitions, structures, classes and inductives — anything that can appear as a
  --    hypothesis and stands for an unproved assertion, not just `def P : Prop`.
  --    Mathlib's own `RiemannHypothesis` is added by hand: `ZetaForm` is an `abbrev` for it,
  --    so a theorem may mention it directly, and it is of course unproved.
  let mut statements : Std.HashSet Name := {`RiemannHypothesis}
  for (n, ci) in env.constants.toList do
    if !n.isInternal && (isProjectConst env n || (moduleOf? env n).any isVendorModule) then
      match ci with
      | .defnInfo _ | .opaqueInfo _ | .inductInfo _ =>
        if resultIsProp ci.type then statements := statements.insert n
      | _ => pure ()
  -- 2. record what has a proof.  Two levels, because a parameterized statement can be proved
  --    for one argument and open for another (`EF_lit cfg` is a theorem for ζ's configuration
  --    and an assumption for any other): `provedTypes` holds the exact propositions that some
  --    constant of the environment proves, `proved` only their head constants, and the head
  --    test is used just for a hypothesis that still has loose bound variables, where there is
  --    no closed proposition to look for.
  let mut proved : Std.HashSet Name := {}
  let mut provedTypes : Std.HashSet Expr := {}
  for (_, ci) in env.constants.toList do
    if let some c := ci.type.getAppFn.constName? then
      if statements.contains c then
        proved := proved.insert c
        provedTypes := provedTypes.insert ci.type
  let isOpen (p : Expr) : Bool :=
    if p.hasLooseBVars then
      match p.getAppFn.constName? with
      | some c => !proved.contains c
      | none => false
    else !provedTypes.contains p
  -- 3. the theorems one of whose hypotheses mentions an unproved statement
  let mut lines : Array (String × String) := #[]
  for (n, ci) in env.constants.toList do
    if !n.isInternal && isProjectConst env n && !(moduleOf? env n).any isAbsorbedModule then
      match ci with
      | .thmInfo _ =>
        let apps := (hypotheses ci.type #[]).foldl (fun a d => statementApps statements d a) #[]
        let mut hit : Array Name := #[]
        for p in apps do
          if isOpen p then
            if let some c := p.getAppFn.constName? then
              if !hit.contains c then hit := hit.push c
        let hits := hit.qsort (·.lt ·)
        if hits.size != 0 then
          let tag := hits.foldl
            (fun acc p => if severity (tagOf p) < severity acc then tagOf p else acc)
            "DEFINITIONAL"
          lines := lines.push
            (tag, s!"{n} <- {String.intercalate ", " (hits.toList.map toString)}")
      | _ => pure ()
  -- 4. print the three classes separately: only the first is a conditional/unconditional issue
  let printClass (tag : String) (header : String) : IO Unit := do
    IO.println header
    for (_, l) in (lines.filter (fun p => p.1 == tag)).qsort (fun a b => a.2 < b.2) do
      IO.println s!"  {l}"
  printClass "UNCLASSIFIED"
    "# UNCLASSIFIED: unproved statements missing from the classification in scripts/conditional_theorems.lean"
  printClass "OPEN"
    "# OPEN: theorems conditional on a statement this repository cannot prove"
  printClass "ROUTE_CLOSED"
    "# ROUTE_CLOSED: hypotheses of abandoned routes, kept for the record"
  printClass "DEFINITIONAL"
    "# DEFINITIONAL: hypotheses on an argument of the theorem, not open assumptions"
