/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Characters/BiquadraticGoodPrimeUnramified.lean
  Original module: OAI.NumberTheory.SiegelZeros.Characters.BiquadraticGoodPrimeUnramified
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.QuadraticAdjoinBasis

namespace RiemannHypothesis.Family003

namespace SiegelZeros

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField

theorem source_biquadratic_good_prime_unramified (q p : ℕ) [NeZero q]
    (a b : CyclotomicField (8 * q) ℚ) (hp : p.Prime) (hgood : ¬ p ∣ 2 * q) :
    Algebra.IsUnramifiedIn
      (𝓞 (IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))))
      (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp8 : p ∣ 8 ↔ p ∣ 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0)]
  have hpn : ¬ p ∣ 8 * q := by simpa only [hp.dvd_mul, hp8] using hgood
  exact isUnramifiedIn_of_numberField_extension (L := CyclotomicField (8 * q) ℚ) _
    (cyclotomic_isUnramifiedIn (8 * q) (CyclotomicField (8 * q) ℚ) p hpn)

end WeightedTorusJets


end SiegelZeros

end RiemannHypothesis.Family003
