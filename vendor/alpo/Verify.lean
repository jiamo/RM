import Main
import Lean

/-!
Independent post-build check of the alpo.ge tree.

Everything is compared as raw kernel `Expr`s and raw `Name`s (single backtick, no name
resolution), so no notation, macro, `open` or shadowing inside the checked tree can change
what is being checked.
-/

open Lean Meta

run_meta do
  let env ← getEnv
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.allImportedModuleNames[i.toNat]!
    | none => `«this file»
  -- 1. the five headline theorems have exactly the advertised types
  let expect (thm : Name) (ty : Expr) : MetaM Unit := do
    let some ci := env.find? thm | throwError "missing {thm}"
    unless ci matches .thmInfo _ do throwError "{thm} is not a theorem"
    unless ci.type == ty do throwError "{thm}: unexpected type {ci.type}"
    let axs ← collectAxioms thm
    let bad := axs.filter (· ∉ [`propext, `Classical.choice, `Quot.sound])
    unless bad.isEmpty do throwError "{thm} depends on non-standard axioms {bad}"
    logInfo m!"OK {thm} : {ty}  [module {modOf thm}]  axioms: {axs}"
  expect `riemannHypothesis (.const `RiemannHypothesis [])
  expect `riemannZeta_eq_zero_re (.const `RiemannZetaZerosOnLine [])
  expect `LFunction_ne_zero_of_half_lt_re (.const `DirichletLNonvanishingRightOfHalf [])
  expect `LFunction_eq_zero_re (.const `DirichletLZerosOnLine [])
  expect `LFunction_eq_zero_re_of_isPrimitive (.const `PrimitiveDirichletLZerosOnLine [])
  -- 2. where the statement constants come from, and what RH unfolds to
  for n in [`RiemannHypothesis, `riemannZeta, `DirichletCharacter.LFunction,
            `RiemannZetaZerosOnLine, `DirichletLNonvanishingRightOfHalf,
            `DirichletLZerosOnLine, `PrimitiveDirichletLZerosOnLine] do
    let some ci := env.find? n | throwError "missing {n}"
    logInfo m!"{n} defined in module {modOf n}; value:\n{ci.value?.getD (mkConst `none)}"
  -- 3. every axiom anywhere in the environment, with its module
  let mut axs : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if ci matches .axiomInfo _ then axs := axs.push (n, modOf n)
  logInfo m!"all axioms in environment ({axs.size}): {axs}"
  -- 4. the statement module imports nothing but Mathlib
  let stIdx := (env.allImportedModuleNames.idxOf? `Statements).getD 0
  logInfo m!"Statements imports: {env.header.moduleData[stIdx]!.imports.map (·.module)}"

#print axioms riemannHypothesis
#print axioms LFunction_eq_zero_re
