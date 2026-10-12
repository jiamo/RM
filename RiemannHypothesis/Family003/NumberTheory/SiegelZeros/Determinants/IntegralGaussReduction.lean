/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Determinants/IntegralGaussReduction.lean
  Original module: OAI.NumberTheory.SiegelZeros.Determinants.IntegralGaussReduction
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.GaussMinimalPolynomial

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace SiegelZerosAwei.W09

open scoped NumberField

variable {q : ℕ} [NeZero q]

theorem liftedAddChar_isIntegral (j : ZMod q) :
    IsIntegral ℤ (liftedAddChar j) := by
  apply IsIntegral.of_pow (n := q) (NeZero.pos q)
  have hp : liftedAddChar j ^ q = 1 := by
    apply Subtype.ext
    change ZMod.stdAddChar j ^ q = 1
    rw [← AddChar.map_nsmul_eq_pow]
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  rw [hp]
  exact isIntegral_one

noncomputable def integralAddChar : AddChar (ZMod q) (𝓞 (complexCyclotomicField q)) where
  toFun j := ⟨liftedAddChar j, liftedAddChar_isIntegral j⟩
  map_zero_eq_one' := by
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact ZMod.stdAddChar.map_zero_eq_one
  map_add_eq_mul' j k := by
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact ZMod.stdAddChar.map_add_eq_mul j k

noncomputable def integralGaussSum (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    𝓞 (complexCyclotomicField q) :=
  gaussSum (reducedIntegerCharacter χ hq (𝓞 (complexCyclotomicField q))) integralAddChar

theorem integralGaussSum_coe (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    ((integralGaussSum χ hq : complexCyclotomicField q) : ℂ) = characterGaussSum χ := by
  simp [integralGaussSum, gaussSum, reducedIntegerCharacter, integralAddChar,
    liftedAddChar, characterGaussSum, integerCharacter_cast]
  rfl

theorem integralGaussSum_sq (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    integralGaussSum χ hq ^ 2 = (signedConductor χ : 𝓞 (complexCyclotomicField q)) := by
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  change ((integralGaussSum χ hq : complexCyclotomicField q) : ℂ) ^ 2 =
    (signedConductor χ : ℂ)
  rw [integralGaussSum_coe]
  exact characterGaussSum_sq_signedConductor χ hp hq

noncomputable def residueAddChar {R : Type*} [CommRing R]
    (ρ : 𝓞 (complexCyclotomicField q) →+* R) : AddChar (ZMod q) R :=
  ρ.toMonoidHom.compAddChar integralAddChar

theorem map_integralGaussSum {R : Type*} [CommRing R]
    (ρ : 𝓞 (complexCyclotomicField q) →+* R)
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    ρ (integralGaussSum χ hq) =
      gaussSum (reducedIntegerCharacter χ hq R) (residueAddChar ρ) := by
  simp [integralGaussSum, gaussSum, residueAddChar, reducedIntegerCharacter]

theorem residueGaussSum_sq {R : Type*} [CommRing R]
    (ρ : 𝓞 (complexCyclotomicField q) →+* R)
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    gaussSum (reducedIntegerCharacter χ hq R) (residueAddChar ρ) ^ 2 =
      (signedConductor χ : R) := by
  rw [← map_integralGaussSum ρ χ hq, ← map_pow, integralGaussSum_sq χ hp hq,
    map_intCast]

end SiegelZerosAwei.W09


end SiegelZeros

end RiemannHypothesis.Family003
