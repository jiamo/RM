/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (`Mathlib/GroupTheory/Index.lean`, Apache 2.0,
Mathlib contributors) has an instance saying that the preimage of a finite-index subgroup under
a group homomorphism again has finite index; the absorbed proofs use it through `infer_instance`.
It is absent at this repository's Mathlib pin db584cd6.  The instance below states the same
fact and is proved from `Subgroup.index_comap` and `Subgroup.isFiniteRelIndex_of_finiteIndex`.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.GroupTheory.Index

namespace Subgroup

/-- The preimage of a finite-index subgroup under a group homomorphism has finite index. -/
instance family003_finiteIndex_comap {G G' : Type*} [Group G] [Group G'] (H : Subgroup G')
    [H.FiniteIndex] (f : G →* G') : (H.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap]
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := H) (K := f.range)
  exact Subgroup.relIndex_ne_zero

end Subgroup
