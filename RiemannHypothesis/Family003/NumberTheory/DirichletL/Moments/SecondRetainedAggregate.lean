/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondRetainedAggregate.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondRetainedAggregate
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondSourceFrequency

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained CenteredMomentSecondSourceFrequency
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩

theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK

end SevenEighths.CenteredMomentSecondRetainedAggregate

end

end RiemannHypothesis.Family003
