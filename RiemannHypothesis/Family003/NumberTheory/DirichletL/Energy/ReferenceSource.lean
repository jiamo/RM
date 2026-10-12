/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/ReferenceSource.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceSource
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.ReferenceReflection
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CompletedGauss.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

lemma original_row_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(z:O)(hz:z≠0):
    positiveSlotRow s.character s.mask 1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=by
  have hh:=original_positive_deletion s.character z hz s.puncture s.puncture_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool hp β P hP t X₁ X₂ hX₁ hX₂
  dsimp only at hh
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t] at hh
  simpa only [NaturalState.mask,signedCommonSource,naturalCharacter_eq s.character z hz] using hh

theorem original_energy_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale=
    radialEnergy (signedCommonSource s W₁ W₂ pool β P t X₁ X₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  change _=radialEnergy _ (effectiveRadial s.radial).keep _ _
  rw [radialEnergy_effective]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:s.radial.keep z
  · simp only [ite_eq_left hz]
    rw [original_row_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂
      z (s.row_ne_zero z hz),norm_mul,norm_mul,
      positive_height_phase_norm X₁ t hX₁,positive_height_phase_norm X₂ t hX₂,one_mul,one_mul]
  · simp only [ite_eq_right hz]

end SevenEighths.CenteredMomentEnergyReferenceSource

end

end RiemannHypothesis.Family003
