/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

`Finset.sum_le_sum_of_injOn` is the additive form (via `to_additive`) of
`Finset.prod_le_prod_of_injOn` in Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` (Apache 2.0, Mathlib contributors).
It is absent at this repository's Mathlib pin db584cd6.  The statement below is the upstream
statement; the proof is a host-pin reduction to `Finset.sum_le_sum_of_subset_of_nonneg`,
`Finset.sum_image` and `Finset.sum_le_sum`.

Proof status: NEWLY PROVED FOR COMPATIBILITY (statement copied from upstream).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Finset

variable {ι α N : Type*} [AddCommMonoid N] [Preorder N] {f : ι → N}

theorem sum_le_sum_of_injOn [DecidableEq α] [AddLeftMono N]
    {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg ht hg)
  rw [sum_image he]
  exact sum_le_sum h

end Finset
