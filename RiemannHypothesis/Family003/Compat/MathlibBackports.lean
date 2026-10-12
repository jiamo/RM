/-
Host-compatibility backports (second batch) for the native absorption of openai/math,
family 003 (source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Lean v4.34.1 and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612.  This repository is pinned to Lean v4.33.0 and
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, where the lemmas below do not exist.
Each declaration here has exactly the statement of the upstream Mathlib declaration of the
same name (Mathlib is Apache 2.0; copyright of the respective Mathlib authors), and is
proved from host-pin material:

  * `IsCoprime.dvd_mul_left_iff`, `IsCoprime.dvd_mul_right_iff`:
    `Mathlib/RingTheory/Coprime/Basic.lean` (upstream proofs, verbatim).
  * `multiplicity_eq_zero_of_not_dvd`: `Mathlib/RingTheory/Multiplicity.lean`
    (proved here from the host iff `multiplicity_eq_zero`).
  * `exists_sq_mul_squarefree`: `Mathlib/Algebra/Squarefree/Basic.lean`
    (upstream proof, verbatim).
  * `integral_id_div_sq_add_sq`: `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
    (upstream proof; `convert!` replaced by host `convert (preTransparency := .instances)`
    followed by `push_cast`).

Proof status: NEWLY PROVED FOR COMPATIBILITY (statements copied from upstream).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section Coprime

variable {R : Type*} [CommSemiring R] {x y z : R}

theorem IsCoprime.dvd_mul_right_iff (H : IsCoprime x z) : x ∣ y * z ↔ x ∣ y :=
  ⟨H.dvd_of_dvd_mul_right, fun h ↦ h.mul_right z⟩

theorem IsCoprime.dvd_mul_left_iff (H : IsCoprime x y) : x ∣ y * z ↔ x ∣ z :=
  ⟨H.dvd_of_dvd_mul_left, fun h ↦ h.mul_left y⟩

end Coprime

section Multiplicity

variable {α : Type*} [Monoid α] {a b : α}

theorem multiplicity_eq_zero_of_not_dvd (h : ¬ a ∣ b) : multiplicity a b = 0 :=
  multiplicity_eq_zero.mpr h

end Multiplicity

section Squarefree

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- Every element of a unique factorization monoid is a square times a squarefree element. -/
theorem exists_sq_mul_squarefree (x : R) : ∃ e d : R, e ^ 2 * d = x ∧ Squarefree d := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => exact ⟨0, 1, by simp, squarefree_one⟩
  | unit u hu => exact ⟨1, u, by simp, hu.squarefree⟩
  | mul z p hz hp ih =>
    obtain ⟨e, d, rfl, hd⟩ := ih
    by_cases hpd : p ∣ d
    · obtain ⟨d', rfl⟩ := hpd
      exact ⟨e * p, d', by simp only [pow_two]; ac_rfl, hd.of_mul_right⟩
    · refine ⟨e, d * p, by ac_rfl, ?_⟩
      rw [_root_.squarefree_mul_iff]
      exact ⟨(hp.isRelPrime_iff_not_dvd.mpr hpd).symm, hd, hp.squarefree⟩

end Squarefree

section Integral

open Real intervalIntegral

theorem integral_id_div_sq_add_sq {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, x / (c ^ 2 + x ^ 2) =
      (Real.log (c ^ 2 + b ^ 2) - Real.log (c ^ 2 + a ^ 2)) / 2 := by
  rw [sub_div]
  apply integral_eq_sub_of_hasDerivAt (f := fun x => Real.log (c ^ 2 + x ^ 2) / 2)
  · intro x _
    have h := (((hasDerivAt_pow 2 x).const_add (c ^ 2)).log
      (by dsimp; positivity)).div_const 2
    convert (preTransparency := .instances) h using 1
    push_cast
    ring
  · exact (continuous_id.div (by fun_prop) fun x => by positivity).intervalIntegrable _ _

end Integral
