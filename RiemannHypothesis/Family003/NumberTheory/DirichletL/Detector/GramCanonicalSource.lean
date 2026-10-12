/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramCanonicalSource.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramCanonicalSource
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramCanonicalBlock

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0<commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=>canonicalJoint S hS σ C k (primaryGenerator D*n) (primaryGenerator D*m))).tsum_prod.symm

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
