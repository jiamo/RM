/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Dictionary/InverseRawConjugateGates.lean
  Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialProfileBounds

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=>star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]

theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=clippedSource (fun x=>star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end RiemannHypothesis.Family003
