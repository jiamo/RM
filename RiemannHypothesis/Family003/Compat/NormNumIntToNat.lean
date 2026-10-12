/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Lean v4.34.1 and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612, where `norm_num` evaluates `Int.toNat` of a numeral
(for instance `Int.toNat 7 = 7`).  At the host pin (Lean v4.33.0, Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d) `norm_num` leaves such terms unevaluated.  This file
adds a `norm_num` extension for `Int.toNat` so that the upstream proofs go through unchanged.

Proof status: NEWLY PROVED FOR COMPATIBILITY (a `norm_num` extension; every step it takes is
justified by the lemmas `isNat_intToNat`, `isNat_intToNat_neg` below, checked by the kernel).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Tactic.NormNum.Basic
import RiemannHypothesis.Family003.Compat.NormNumSimprocs

namespace RiemannHypothesis.Family003.Compat.NormNumIntToNat

open Lean Meta Qq Mathlib.Meta.NormNum

theorem isNat_intToNat {a : ℤ} {n : ℕ} (h : IsNat a n) : IsNat a.toNat n :=
  ⟨by rw [h.out]; simp⟩

theorem isNat_intToNat_neg {a : ℤ} {n : ℕ} (h : IsInt a (.negOfNat n)) : IsNat a.toNat 0 :=
  ⟨by rw [h.out, Int.cast_id]; exact Int.toNat_eq_zero.mpr (by cases n <;> simp [Int.negOfNat] <;> omega)⟩

/-- The `norm_num` extension evaluating `Int.toNat` of an integer numeral. -/
@[norm_num Int.toNat _]
def evalIntToNat : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.toNat _) (a : Q(ℤ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.toNat $a := ⟨⟩
  match ← derive (u := .zero) a with
  | .isNat _ n p =>
    assumeInstancesCommute
    return .isNat q(inferInstance) n q(isNat_intToNat $p)
  | .isNegNat _ n p =>
    assumeInstancesCommute
    return .isNat q(inferInstance) q(nat_lit 0) q(isNat_intToNat_neg $p)
  | _ => failure

end RiemannHypothesis.Family003.Compat.NormNumIntToNat
