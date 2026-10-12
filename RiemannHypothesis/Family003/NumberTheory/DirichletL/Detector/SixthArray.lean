/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/SixthArray.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.SixthArray
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SixthMask
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RawArithmetic
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeCompleted
open HeckeInverseAmplification ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma bareIdealHighCoefficient_sixth (η : HeckeFamily.Character)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (hL : Supported p.2.val)
    (I J K : Ideal O) :
    bareIdealHighCoefficient η (sixthFrequencyEquiv p).val I J K 1=
      bareIdealHighCoefficient η p.1.val I J K p.2.val := by
  rw [sixthFrequencyEquiv_primary p hL]
  unfold bareIdealHighCoefficient
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K
  · simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,hL,supported_one_ideal,and_self,dite_eq_left]
    congr 1
    simp only [primaryGenerator_one,one_pow,mul_one]
  · have h1 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    have h2 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported p.2.val) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [dite_eq_right h1,dite_eq_right h2]

lemma rawHighCoefficient_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Ideal O) (η : HeckeFamily.Character) (x w z : ℂ)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (I J K : Ideal O) :
    fullHighCoefficient S D η
      (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
      (rawHighEmbedding (sixthFrequencyEquiv p,((I,J),K)))=
    star ((calibrationForSet S hS).residueMonoid p.1.val)*
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*
      markedIdealHighSummand S D η p.1.val x w z I J K p.2.val := by
  have hOne : ∀P∈S,¬P∣(1:Ideal O) := fun P hP=> (hprime P hP).not_dvd_one
  change star ((calibrationForSet S hS).residueMonoid (sixthFrequencyEquiv p).val)*
    frequencyWeight z (sixthFrequencyEquiv p)*
      markedIdealHighSummand S D η (sixthFrequencyEquiv p).val x w z I J K 1=_
  rw [sixthFrequencyWeight]
  rw [sixthFrequencyEquiv_apply,calibration_sixth_frequency_mask]
  by_cases hL : ∀P∈S,¬P∣p.2.val
  · have hs := supported_of_source_exclusions S hbad p.2.val p.2.property hL
    have hb := bareIdealHighCoefficient_sixth η p hs I J K
    rw [sixthFrequencyEquiv_apply] at hb
    simp only [ite_eq_left hL,mul_one,markedIdealHighSummand,highIdealMask,ite_eq_left hOne,
      bareIdealHighSummand,hb]
    have hw1 : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
    rw [hw1]
    ring
  · simp only [ite_eq_right hL,mul_zero,zero_mul,markedIdealHighSummand,highIdealMask]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
