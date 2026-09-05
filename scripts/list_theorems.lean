/-
List every theorem of the `RiemannHypothesis` library, one fully qualified name per line.

Run with

    lake env lean scripts/list_theorems.lean

The output is consumed by `scripts/audit_coverage.py`, which compares it with the list of
`#print axioms` commands in `scripts/audit.sh` and reports the theorems that no axiom check
covers.  Auto-generated declarations (equation lemmas, `_proof_*`, internal `match_*`,
instance projections, private declarations) are filtered out: they are not user-facing results
and are covered by the axiom check of whatever result uses them.
-/
import RiemannHypothesis
import Solution

open Lean

/-- Is `n` an internal / auto-generated name that no audit list should be expected to mention? -/
private def isInternalName (n : Name) : Bool :=
  n.isInternal
    || n.components.any fun c =>
        let s := c.toString
        s.startsWith "_"
          || s.startsWith "proof_"
          || s.startsWith "match_"
          || s.startsWith "eq_"
          || s == "sizeOf_spec"
          || s == "injEq"
          || s == "noConfusion"

run_cmd do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
      if isInternalName n then continue
      if isPrivateName n then continue
      match env.getModuleIdxFor? n with
      | none => pure ()
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        if mod == `RiemannHypothesis || (`RiemannHypothesis).isPrefixOf mod
            || mod == `Solution || mod == `Challenge then
          out := out.push n
    | _ => pure ()
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println n
