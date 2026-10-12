/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/GenericRegularity.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.GenericRegularity
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Intersection.TorusProjectiveClosure

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

noncomputable section
namespace W58

attribute [local instance 2000] Monoid.toMulAction Semiring.toModule

variable (K : Type*) [Field K]

theorem generic_height_le_cotangent_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) ≤
      Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p) := by
  have h := ringKrullDim_le_spanFinrank_maximalIdeal (GenericLocalRing K p)
  rw [generic_local_dimension,
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
      (GenericLocalRing K p)] at h
  exact h

theorem generic_height_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) ≤
      Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
        (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
          (GenericCotangent K p)) := by
  rw [Subspace.dual_finrank_eq
    (K := IsLocalRing.ResidueField (GenericLocalRing K p))
    (V := GenericCotangent K p)]
  exact generic_height_le_cotangent_dimension K p

theorem height_two_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 2) :
    2 ≤ Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
      (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p)) := by
  have h := generic_height_le_normal_dimension K p
  rw [hp] at h
  exact_mod_cast h

theorem height_three_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 3) :
    3 ≤ Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
      (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p)) := by
  have h := generic_height_le_normal_dimension K p
  rw [hp] at h
  exact_mod_cast h

end W58

end

end

end SiegelZeros

end RiemannHypothesis.Family003
