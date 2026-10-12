/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/PrimeResidueAlgebraEquiv.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.PrimeResidueAlgebraEquiv
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.TriangularLocalParametersTransport

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]
variable (e : R ≃ₐ[K] S) (P : Ideal R) [P.IsPrime]

instance primeResidueImage_isPrime : (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

def primeResidueRingEquiv : P.ResidueField ≃+* (P.map e.toRingHom).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (SiegelZeros.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P)

@[simp] theorem primeResidueRingEquiv_algebraMap (r : R) :
    primeResidueRingEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) := by
  change IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (SiegelZeros.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P
        (algebraMap R (Localization.AtPrime P) r)) =
    IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (algebraMap S (Localization.AtPrime (P.map e.toRingHom)) (e r))
  exact congrArg (IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom)))
    (SiegelZeros.W23.atPrimeEquivOfRingEquiv_algebraMap e.toRingEquiv P r)

def primeResidueAlgEquiv : P.ResidueField ≃ₐ[K] (P.map e.toRingHom).ResidueField where
  __ := primeResidueRingEquiv e P
  commutes' a := by
    change primeResidueRingEquiv e P (algebraMap K P.ResidueField a) = _
    rw [IsScalarTower.algebraMap_apply K R P.ResidueField,
      primeResidueRingEquiv_algebraMap, e.commutes]
    exact (IsScalarTower.algebraMap_apply K S (P.map e.toRingHom).ResidueField a).symm

@[simp] theorem primeResidueAlgEquiv_algebraMap (r : R) :
    primeResidueAlgEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) :=
  primeResidueRingEquiv_algebraMap e P r

theorem primeResidueAlgEquiv_transcendenceBasis {ι : Type*} (x : ι → P.ResidueField)
    (hx : IsTranscendenceBasis K x) :
    IsTranscendenceBasis K (fun i => primeResidueAlgEquiv e P (x i)) :=
  (primeResidueAlgEquiv e P).isTranscendenceBasis hx

end WeightedTorusJets.PolynomialLocalResidueResolution

end

end

end SiegelZeros

end RiemannHypothesis.Family003
