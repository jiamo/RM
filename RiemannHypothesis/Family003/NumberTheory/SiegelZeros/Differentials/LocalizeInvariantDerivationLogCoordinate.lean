/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Differentials/LocalizeInvariantDerivationLogCoordinate.lean
  Original module: OAI.NumberTheory.SiegelZeros.Differentials.LocalizeInvariantDerivationLogCoordinate
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib
import RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.FiniteTypeFieldModelEquiv

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

variable {K ι T : Type*} [CommRing K] [CommRing T] [Fintype ι]
  [Algebra K T] [Algebra (MvPolynomial ι K) T] [IsScalarTower K (MvPolynomial ι K) T]

theorem localize_invariantDerivation_log_coordinate (M : Submonoid (MvPolynomial ι K))
    [IsLocalization M T] (c : ι → K) (i : ι) (u : Tˣ)
    (hu : (u : T) = algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) :
    (↑(u⁻¹) : T) * localizeDerivation M (invariantDerivation c)
      (algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) = algebraMap K T (c i) := by
  rw [localize_invariantDerivation_X, ← hu]
  rw [mul_comm (algebraMap K T (c i)) (u : T)]
  exact Units.inv_mul_cancel_left u _

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {k F ι : Type*} [Field k] [Field F] [Algebra k F] [Fintype ι]

theorem lift_logarithmicForm (c : ι → k) (f : ι → F) (D : Derivation k F F) :
    D.liftKaehlerDifferential (logarithmicForm c f) =
      ∑ i, algebraMap k F (c i) * (f i)⁻¹ * D (f i) := by
  simp [logarithmicForm]

end WeightedTorusJets.Geometry

end

end SiegelZeros

end RiemannHypothesis.Family003
