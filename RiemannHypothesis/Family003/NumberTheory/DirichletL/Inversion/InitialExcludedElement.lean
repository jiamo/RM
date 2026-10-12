/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialExcludedElement.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialExcludedPeriod
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialRayAttachment

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass HeckeFamily InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O

theorem elementCharacter_eq_elementHom (χ:Character)(hproper:χ.modulus≠⊤):
    elementCharacter (idealCoeff χ).toMonoidHom=HeckeRowClosure.elementHom χ := by
  let:Nontrivial (O⧸χ.modulus):=Ideal.Quotient.nontrivial_iff.mpr hproper
  ext z
  change idealCoeff χ (Ideal.span {z})=elementCoeff χ z
  by_cases hz:z=0
  · subst z
    simp only [Ideal.span_singleton_zero,←Ideal.zero_eq_bot,
      elementCoeff,map_zero,MulChar.map_zero]
  · exact idealCoeff_span χ hz

theorem deleted_modulus_proper (χ:Character)(q:ℕ):
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≠⊤ := by
  have htwo:(Ideal.span {(2:O)}:Ideal O)∈reflectionExcludedPrimes q:=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle:(χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≤
      Ideal.span {(2:O)}:=by
    change χ.modulus*(∏P∈reflectionExcludedPrimes q,P)≤Ideal.span {(2:O)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P=>P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem deleted_physical_element_eq (χ:Character)(q:ℕ):
    elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom=
      HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) :=
  elementCharacter_eq_elementHom _ (deleted_modulus_proper χ q)

theorem deleted_physical_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (elementCharacter (idealCoeff
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom) := by
  rw [deleted_physical_element_eq]
  exact deleted_base_gates χ q hq hperiod

end SevenEighths.InverseInitialExcludedPeriod

end

end RiemannHypothesis.Family003
