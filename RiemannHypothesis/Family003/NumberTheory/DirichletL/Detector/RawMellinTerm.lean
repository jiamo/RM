/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/RawMellinTerm.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.RawMellinTerm
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.InitialSubseries
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.ContourShear

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=>star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator K) := by
    apply calibrationForSet_coprime_of_excluded S hS
    rw [(primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1]
    exact hKS
  unfold rawPhysicalMellinTerm
  rw [physicalMellinCoefficientTerm_eq_guarded η S hS hbad D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) hcs X hX H.val H.property t z,
    guardedHighMellinCoefficient_eq_high η (calibrationForSet S hS) S hpS D I J K hK hKS X H.val
      (t+1-z) w z,sourceMellinWeight_shear]
  simp only [fullHighCoefficient,frequencyWeight,rawHighEmbedding]
  ring

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
