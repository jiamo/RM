/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

`HasCompactSupport.exists_bound_iteratedFDeriv` was added to Mathlib after this repository's
pin db584cd6.  Upstream source: Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
`Mathlib/Analysis/Calculus/ContDiff/Basic.lean` (Apache 2.0, Mathlib contributors).  The
statement is the upstream one; the proof follows the upstream proof, rewritten without
`grw`/`grind` for the host pin.

Proof status: ADAPTED (Mathlib upstream statement; proof re-expressed for the host pin).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The iterated derivatives up to order `m` of a smooth compactly supported function are
uniformly bounded. -/
lemma HasCompactSupport.exists_bound_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  refine (hA i y).trans (le_trans ?_ (le_max_right _ _))
  exact Finset.le_sup' A (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
