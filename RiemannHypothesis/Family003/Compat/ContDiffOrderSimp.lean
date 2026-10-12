/-
Host-compatibility layer for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs discharge smoothness-order side goals such as `(k : WithTop ℕ∞) ≤ ∞`
(for `k : ℕ`) with `by simp`.  In Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (the upstream
pin) `simp` closes this goal; at the host pin (Mathlib db584cd6d46c92f209a44c0f1c829460d327499d)
`simp` makes no progress on it.  This file adds the missing `simp` lemma, proved here from
`le_top`.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace RiemannHypothesis.Family003.Compat

open scoped ContDiff

/-- A natural-number smoothness order is at most `∞`. -/
@[simp] theorem natCast_le_contDiff_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

end RiemannHypothesis.Family003.Compat
