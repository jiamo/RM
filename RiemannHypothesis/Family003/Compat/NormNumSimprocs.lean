/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, whose
`norm_num` runs the default `simp` simprocs (`Fin.isValue`, `Matrix.cons_val`,
`Int.reduceToNat`, `reduceIte`, ...) during its `simp` traversal, unless `norm_num only` is
used.  At the host pin (Mathlib db584cd6d46c92f209a44c0f1c829460d327499d) `norm_num` passes an
empty simproc array to `simp`, so goals such as `![a, b, c] 2 = c` or `Int.toNat 7 = 7` are left
open by `norm_num` although `simp` closes them.

This file backports the upstream change.  It is the upstream code of
`Mathlib/Tactic/NormNum/Core.lean` at d13f23b7 (functions `methods`, `deriveSimp`,
`getSimpContext`, `elabNormNum` and the `norm_num` tactic / conv elaborators; Mathlib is
Apache 2.0, copyright (c) 2021 Mario Carneiro and the Mathlib contributors), registered as an
additional elaborator for the existing host syntax `Mathlib.Tactic.normNum` (and
`Mathlib.Tactic.normNumConv`), so that a file importing this module elaborates `norm_num` with
the upstream semantics.  `norm_num1` is unchanged (upstream it also uses no simprocs).

Soundness: this changes only which rewrite steps the tactic tries; every step still produces a
proof term that the kernel checks.

Proof status: NEWLY WRITTEN FOR COMPATIBILITY (tactic backport, upstream code).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Tactic.NormNum.Core

namespace RiemannHypothesis.Family003.Compat.NormNumSimprocs

open Lean Meta Elab Tactic Mathlib.Meta.NormNum Mathlib.Tactic

/-- Upstream `Mathlib.Meta.NormNum.methods`: a `Methods` implementation which calls `norm_num`,
running the given simprocs. -/
def methods (simprocs : Simp.SimprocsArray := #[]) (useSimp := true) : Simp.Methods :=
  if useSimp then {
    pre := Simp.preDefault simprocs >> tryNormNum
    post := Simp.postDefault simprocs >> tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  } else {
    pre := tryNormNum
    post := tryNormNum (post := true)
    discharge? := Simp.dischargeGround
  }

/-- Upstream `Mathlib.Meta.NormNum.deriveSimp`. -/
def deriveSimp (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[]) (useSimp := true)
    (e : Expr) : MetaM Simp.Result :=
  (·.1) <$> Simp.main e ctx (methods := methods simprocs useSimp)

/-- Upstream `Mathlib.Meta.NormNum.getSimpContext`: the simp context and the simprocs (the
default simprocs unless `only` is used). -/
def getSimpContext (cfg args : Syntax) (simpOnly := false) :
    TacticM (Simp.Context × Simp.SimprocsArray) := do
  let { config, userConfig } ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let { ctx, simprocs, .. } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := #[simprocs])
      (← Simp.mkContext config (simpTheorems := #[simpTheorems])
        (congrTheorems := ← getSimpCongrTheorems) (userConfig := userConfig))
  return (ctx, simprocs)

/-- Upstream `Mathlib.Meta.NormNum.elabNormNum`. -/
def elabNormNum (cfg args loc : Syntax) (simpOnly := false) (useSimp := true) :
    TacticM Unit := withMainContext do
  let (ctx, simprocs) ← getSimpContext cfg args (!useSimp || simpOnly)
  let loc := expandOptLocation loc
  transformAtNondepPropLocation (fun e ctx ↦ deriveSimp ctx simprocs useSimp e) "norm_num" loc
    (ifUnchanged := .silent) (mayCloseGoalFromHyp := true) ctx

/-- `norm_num` with the upstream (d13f23b7) semantics: the default simprocs are used. -/
@[tactic Mathlib.Tactic.normNum]
def evalNormNum : Tactic := fun stx =>
  elabNormNum stx[1] stx[3] stx[4] (simpOnly := !stx[2].isNone) (useSimp := true)

/-- Conv-mode `norm_num` with the upstream (d13f23b7) semantics. -/
@[tactic Mathlib.Tactic.normNumConv]
def evalNormNumConv : Tactic := fun stx ↦ withMainContext do
  let (ctx, simprocs) ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult
    (← deriveSimp ctx simprocs (useSimp := true) (← instantiateMVars (← Conv.getLhs)))

end RiemannHypothesis.Family003.Compat.NormNumSimprocs
