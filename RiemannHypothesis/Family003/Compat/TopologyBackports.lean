/-
Host-compatibility backports (topology) for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.  At
the host pin (Mathlib db584cd6d46c92f209a44c0f1c829460d327499d) the declarations below do not
exist under these names.  Each has exactly the statement of the upstream Mathlib declaration of
the same name (Mathlib is Apache 2.0; copyright of the respective Mathlib authors) and is
proved here from host material:

  * `Pi.tsum_apply`: `Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean` (the host has
    the same statement under the name `tsum_apply`).
  * `Topology.IsOpenQuotientMap.secondCountableTopology`: `Mathlib/Topology/Bases.lean` (the
    host has `Topology.IsQuotientMap.secondCountableTopology`, taking the quotient map and the
    openness separately).

Proof status: NEWLY PROVED FOR COMPATIBILITY (statements copied from upstream).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Bases
import Mathlib.Topology.Maps.OpenQuotient

section Pi

variable {α : Type*} {ι : Type*} {X : α → Type*} [∀ x, AddCommMonoid (X x)]
  [∀ x, TopologicalSpace (X x)] {L : SummationFilter ι}

theorem Pi.tsum_apply [L.NeBot] [∀ x, T2Space (X x)] {f : ι → ∀ x, X x} {x : α}
    (hf : Summable f L) : (∑'[L] i, f i) x = ∑'[L] i, f i x :=
  _root_.tsum_apply hf

end Pi

section Quotient

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {π : X → Y}

/-- A second countable space is mapped by an open quotient map to a second countable space. -/
theorem Topology.IsOpenQuotientMap.secondCountableTopology [SecondCountableTopology X]
    (h : IsOpenQuotientMap π) : SecondCountableTopology Y :=
  h.isQuotientMap.secondCountableTopology h.isOpenMap

end Quotient
