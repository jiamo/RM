/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/NaturalRowSourceDictionary.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.RetainedEnergy

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.masked_plain {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _

end SevenEighths.CenteredMomentNaturalRowSource

end

end RiemannHypothesis.Family003
