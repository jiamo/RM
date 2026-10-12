/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Characters/BiquadraticGoodPrimeUnramifiedSameWitnessEquiv.lean
  Original module: OAI.NumberTheory.SiegelZeros.Characters.BiquadraticGoodPrimeUnramifiedSameWitnessEquiv
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Characters.BiquadraticGoodPrimeUnramified

namespace RiemannHypothesis.Family003

namespace SiegelZeros

open scoped NumberField
namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField

theorem source_biquadratic_good_prime_unramified_same_witness_equiv
    (q p : ℕ) [NeZero q] (a b : CyclotomicField (8 * q) ℚ)
    {K : Type*} [Field K] [NumberField K]
    (e : IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ)) ≃ₐ[ℚ] K)
    (hp : p.Prime) (hgood : ¬ p ∣ 2 * q) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  let := e.symm.toRingHom.toAlgebra
  exact isUnramifiedIn_of_numberField_extension _
    (source_biquadratic_good_prime_unramified q p a b hp hgood)

end WeightedTorusJets


end SiegelZeros

end RiemannHypothesis.Family003
