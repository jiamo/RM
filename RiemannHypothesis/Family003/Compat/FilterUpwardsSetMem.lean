/-
Host-compatibility layer for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

In Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (the upstream pin), an eventual equality or
inclusion of *sets*, `s =ᶠ[l] t` / `s ≤ᶠ[l] t` (in particular `s =ᵐ[μ] t`), is the separate
definition `Filter.EventuallyEqSet l s t := (· ∈ s) =ᶠ[l] (· ∈ t)` (resp.
`Filter.EventuallySubset`), so after `filter_upwards [...] with x` the goal reads
`(x ∈ s) = (x ∈ t)`.  At the host pin (Mathlib db584cd6d46c92f209a44c0f1c829460d327499d) the same
notation is `Filter.EventuallyEq l s t` for `s t : Set α = α → Prop`, and the goal reads
`s x = t x`.  The two are definitionally equal, but `simp`/`rw` lemmas about membership
(`Set.mem_preimage`, ...) do not fire on the host form.

This file adds the elaboration step that restores the upstream goal shape: the tactic
`set_app_to_mem` rewrites (by `change`, i.e. up to definitional equality) every application
`s a` of a term `s : Set α` into `a ∈ s`, and `filter_upwards` is re-registered — same code as
the host's `Mathlib.Tactic.filterUpwards` elaborator in `Mathlib/Order/Filter/Defs.lean`
(Mathlib is Apache 2.0) — with `set_app_to_mem` run on the goal before the `with` binders are
introduced.  Only the *presentation* of goals changes: `change` checks definitional equality,
and the kernel checks the final proof term.

Proof status: NEWLY WRITTEN FOR COMPATIBILITY (tactic).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Order.Filter.Defs

namespace RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem

open Lean Meta Elab Tactic

/-- Rewrite every application `s a`, where `s : Set α`, into `a ∈ s` (definitionally equal). -/
def setAppToMem (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if let .app f a := e then
      let ty ← instantiateMVars (← inferType f)
      if ty.isAppOfArity ``Set 1 then
        if let some mem ← (try some <$> mkAppM ``Membership.mem #[f, a] catch _ => pure none) then
          if ← isDefEq mem e then
            return .done mem
    return .continue)

/-- `set_app_to_mem` rewrites applications `s a` of sets `s : Set α` in the goal into
membership `a ∈ s` (up to definitional equality). -/
elab "set_app_to_mem" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← setAppToMem t
  if t' != t then
    replaceMainGoal [← g.replaceTargetDefEq t']

/-- `filter_upwards`, as in the host's `Mathlib/Order/Filter/Defs.lean`, followed (before the
`with` binders are introduced) by `set_app_to_mem`, which restores the upstream goal shape
`x ∈ s` for eventual equalities and inclusions of sets. -/
elab_rules : tactic
| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do
  focus do
    let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}
    for e in args.getD #[] |>.reverse do
      let goal ← getMainGoal
      replaceMainGoal <| ← goal.withContext <| runTermElab do
        let m ← mkFreshExprMVar none
        let lem ← Term.elabTermEnsuringType
          (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)
        goal.assign lem
        return [m.mvarId!]
    liftMetaTactic fun goal => do
      goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config
    evalTactic <|← `(tactic| try dsimp -zeta only [Set.mem_ofPred_eq])
    evalTactic <|← `(tactic| try set_app_to_mem)
    if let some l := wth then
      evalTactic <|← `(tactic| intro $[$l]*)
    if let some e := usingArg then
      evalTactic <|← `(tactic| exact $e)

end RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem
