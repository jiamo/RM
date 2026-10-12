/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/GenericResidueFunctionField.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.GenericResidueFunctionField
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.CanonicalDivisorScalars

namespace RiemannHypothesis.Family003

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.GenericResidueFunctionField
open SiegelZeros.W58
open SiegelZerosAwei.Workers.W15

variable (k : Type*) [Field k] (p : Ideal (TorusRing k)) [p.IsPrime]

def genericResidueFunctionFieldEquiv :
    IsLocalRing.ResidueField (GenericLocalRing k p) ≃ₐ[TorusSubvarietyRing k p]
      (TorusSubvariety k p).functionField := by
  letI : IsFractionRing (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField :=
    affineSpecFunctionField_isFractionRing (TorusSubvarietyRing k p)
  exact IsLocalization.algEquiv (nonZeroDivisors (TorusSubvarietyRing k p))
    (IsLocalRing.ResidueField (GenericLocalRing k p))
    (TorusSubvariety k p).functionField

@[simp] theorem genericResidueFunctionFieldEquiv_quotient (x : TorusSubvarietyRing k p) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusSubvarietyRing k p)
        (IsLocalRing.ResidueField (GenericLocalRing k p)) x) =
      algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField x :=
  (genericResidueFunctionFieldEquiv k p).commutes x

theorem genericResidueFunctionFieldEquiv_base (x : TorusRing k) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusRing k) (IsLocalRing.ResidueField (GenericLocalRing k p)) x) =
      algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField
        (Ideal.Quotient.mk p x) := by
  change genericResidueFunctionFieldEquiv k p
    (algebraMap (TorusSubvarietyRing k p)
      (IsLocalRing.ResidueField (GenericLocalRing k p)) (Ideal.Quotient.mk p x)) = _
  exact genericResidueFunctionFieldEquiv_quotient k p _

theorem genericResidueFunctionFieldEquiv_coordinate (i : Fin 4) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusRing k) (IsLocalRing.ResidueField (GenericLocalRing k p))
        (coordinate k i)) = torusCoordinateFunction k p i :=
  genericResidueFunctionFieldEquiv_base k p (coordinate k i)

variable (P : Ideal (TorusRing ℂ)) [P.IsPrime]

local instance : Algebra ℂ (TorusSubvariety ℂ P).functionField := torusFunctionFieldAlgebra P
local instance : IsScalarTower ℂ (TorusSubvarietyRing ℂ P)
    (TorusSubvariety ℂ P).functionField :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := TorusSubvarietyRing ℂ P)
    (A := (TorusSubvariety ℂ P).functionField) rfl

def genericResidueFunctionFieldAlgEquiv :
    IsLocalRing.ResidueField (GenericLocalRing ℂ P) ≃ₐ[ℂ]
      (TorusSubvariety ℂ P).functionField :=
  (genericResidueFunctionFieldEquiv ℂ P).restrictScalars ℂ

@[simp] theorem genericResidueFunctionFieldAlgEquiv_coordinate (i : Fin 4) :
    genericResidueFunctionFieldAlgEquiv P
      (algebraMap (TorusRing ℂ) (IsLocalRing.ResidueField (GenericLocalRing ℂ P))
        (coordinate ℂ i)) = torusCoordinateFunction ℂ P i :=
  genericResidueFunctionFieldEquiv_coordinate ℂ P i

@[simp] theorem genericResidueFunctionFieldAlgEquiv_scalar (c : ℂ) :
    genericResidueFunctionFieldAlgEquiv P
      (algebraMap ℂ (IsLocalRing.ResidueField (GenericLocalRing ℂ P)) c) =
        algebraMap ℂ (TorusSubvariety ℂ P).functionField c :=
  (genericResidueFunctionFieldAlgEquiv P).commutes c

end WeightedTorusJets.GenericResidueFunctionField

end

end SiegelZeros

end RiemannHypothesis.Family003
