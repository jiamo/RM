/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (`Mathlib/GroupTheory/Index.lean`, Apache 2.0,
Mathlib contributors) has `Subgroup.FiniteIndex.map_of_surjective`: the image of a finite-index
subgroup under a surjective homomorphism has finite index.  It is absent at this repository's
Mathlib pin db584cd6; the version below is proved from the host's `Subgroup.index_map_dvd`.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.GroupTheory.Index

namespace Subgroup.FiniteIndex

theorem map_of_surjective {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} [H.FiniteIndex]
    (f : G →* G') (hf : Function.Surjective f) : (H.map f).FiniteIndex :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (Subgroup.index_map_dvd H hf)⟩

end Subgroup.FiniteIndex
