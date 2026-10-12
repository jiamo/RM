/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/LowCompensation.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.LowCompensation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.LowSeparated
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GaussianSubset
import RiemannHypothesis.Family003.Compat.NormNumIntToNat
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowMarkedInverseRow (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
      (fun A=>if D∣A then (1:ℂ) else 0)

lemma lowMarkedInverseRow_eq (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (D : Id) (T t : ℝ) (hT : 0<T)
    (σ : RayRing) (m : O) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        lowMarkedInverseRow η S hS D T t σ m :=
  physicalRayRow_eq_periodic_inverse η S hS hbad σ m D _ (gaussianFixedWindow_twist_compact t) T hT

theorem compensationRowTest_low_separated {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold compensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [lowMarkedInverseRow_eq η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

lemma compensationRowTest_low_integrable {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) :
    Integrable (lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)) := by
  exact lowSeparatedIntegrand_integrable (calibrationForSet S hS) W0 W1 _ a0 b0 ha0 hW0 hWs
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    (lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)) _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J)) _

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
