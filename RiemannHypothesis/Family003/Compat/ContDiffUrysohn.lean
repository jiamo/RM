/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

`exists_contDiff_support_eq_eq_one_iff` and `exists_contDiff_zero_iff_one_iff_of_isClosed` are
the `ContDiff` counterparts, for a finite-dimensional real normed space, of
`exists_contMDiff_support_eq_eq_one_iff` and `exists_contMDiff_zero_iff_one_iff_of_isClosed`.
They were added in Mathlib after this repository's pin db584cd6; upstream source: Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612, `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
(Apache 2.0, Mathlib contributors).  Statements and proofs are the upstream ones.

Proof status: ADAPTED (Mathlib upstream proofs, verbatim apart from explicit variables).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Function
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞}

/-- The `ContDiff` counterpart of `exists_contMDiff_support_eq_eq_one_iff` for a
finite-dimensional real normed space. -/
theorem exists_contDiff_support_eq_eq_one_iff {s t : Set E} (hs : IsOpen s) (ht : IsClosed t)
    (h : t ⊆ s) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, E)) (n := n) hs ht h

/-- The `ContDiff` counterpart of `exists_contMDiff_zero_iff_one_iff_of_isClosed` for a
finite-dimensional real normed space. -/
theorem exists_contDiff_zero_iff_one_iff_of_isClosed {s t : Set E}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ s ↔ f x = 0)
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using
    exists_contMDiff_zero_iff_one_iff_of_isClosed (I := 𝓘(ℝ, E)) (n := n) hs ht hd
