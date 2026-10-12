/-
Host-compatibility backports for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Lean v4.34.1 and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612.  This repository is pinned to Lean v4.33.0 and
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, where the lemmas below either do not exist
or exist under a different name.  Each declaration here has exactly the statement of the
upstream declaration of the same name, and is proved from host-pin material.

  * `ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right`: Lean core v4.34.1,
    `src/Init/Core.lean` (Copyright Microsoft Corporation / Lean FRO, Apache 2.0); in
    v4.34.1 they replace the deprecated `if_pos`, `if_neg`, `dif_pos`, `dif_neg`.  The
    proofs are the upstream proofs, verbatim.
  * `Finset.prod_le_prod₀`, `Finset.prod_le_one₀`, `Finset.one_le_prod₀`,
    `Finset.prod_le_prod_of_subset_of_one_le₀`: Mathlib d13f23b7,
    `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean` (Copyright (c) 2025
    Michael Stoll, Floris van Doorn, Apache 2.0).  At the host pin the first, second and
    fourth exist without the subscript; the proofs here are one-line reductions to them.

Proof status: NEWLY PROVED FOR COMPATIBILITY (statements copied from upstream).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

universe u

theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} :
    (ite c t e) = t :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} :
    (ite c t e) = e :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α}
    {e : ¬ c → α} : (dite c t e) = t hc :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α}
    {e : ¬ c → α} : (dite c t e) = e hnc :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

namespace Finset

variable {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R] [PosMulMono R]
  {f g : ι → R} {s t : Finset ι}

lemma prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
  prod_le_prod h0 h1

lemma prod_le_one₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 :=
  prod_le_one h0 h1

lemma one_le_prod₀ (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  simpa using prod_le_prod (f := fun _ => (1 : R)) (by simp) hf

lemma prod_le_prod_of_subset_of_one_le₀ (h : s ⊆ t) (hf₀ : ∀ i ∈ s, 0 ≤ f i)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i :=
  prod_le_prod_of_subset_of_one_le h hf₀ hf

end Finset
