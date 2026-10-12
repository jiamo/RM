/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/AmplifierFamilyAdmission.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstMixedMainError
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.FirstAnnularAdmission

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstSourceConductorCaps CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplifiedFourCoefficients
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

def referenceCost : ℝ := max 1 rayCost

lemma referenceCost_ge_one : 1≤referenceCost := le_max_left _ _

theorem actual_error_reference_cap (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent n)):
    (υ.modulus.absNorm:ℝ)≤referenceCost*(ρ.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (n+1)):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
  calc
    _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        Z^(errorMoving p Z (n+1)):=by apply hN.trans;gcongr
    _=rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
      unfold rayCost fixedPresentationCost;ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      exact mul_le_mul_of_nonneg_right (le_max_right 1 rayCost) (Nat.cast_nonneg _)

end SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

end

end RiemannHypothesis.Family003
