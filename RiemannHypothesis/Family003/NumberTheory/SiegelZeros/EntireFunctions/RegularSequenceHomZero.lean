/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/RegularSequenceHomZero.lean
  Original module: OAI.NumberTheory.SiegelZeros.EntireFunctions.RegularSequenceHomZero
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Regular.RegularSequence

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.W30
open Module
variable {R : Type*} [CommRing R]

theorem quotient_dual_eq_zero_of_regular (I : Ideal R) (r : R) (hrI : r ∈ I)
    (hr : IsSMulRegular R r) (φ : Dual R (R ⧸ I)) : φ = 0 := by
  apply LinearMap.ext
  intro x
  apply hr
  change r • φ x = r • (0 : R)
  rw [smul_zero, ← φ.map_smul]
  have hx : r • x = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    change r • (Submodule.Quotient.mk a : R ⧸ I) = 0
    rw [← Submodule.Quotient.mk_smul I]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    simpa only [smul_eq_mul, mul_comm] using I.smul_mem a hrI
  rw [hx, map_zero]

theorem regularSequenceQuotient_dual_subsingleton (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Dual R (R ⧸ Ideal.ofList rs)) := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs =>
    apply subsingleton_of_forall_eq 0
    intro φ
    apply quotient_dual_eq_zero_of_regular (Ideal.ofList (r :: rs)) r
    · exact Ideal.subset_span (by simp)
    · exact ((RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg).1

end SiegelZerosAwei.W30

end

end SiegelZeros

end RiemannHypothesis.Family003
