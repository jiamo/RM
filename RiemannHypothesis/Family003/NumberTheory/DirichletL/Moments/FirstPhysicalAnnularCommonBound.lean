/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalAnnularCommonBound.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalAnnularCommonBound
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCommonBound

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_common_energy (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₁ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₂ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₁ L*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₂ L*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨Cb,hCb,hbound⟩:=fixed_log_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  rw [block_activeRows η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta
    C D hC hD E rows W K n]
  exact hbound η s t C D hC hD hCD E (activeRows rows n)
    (activeRows_nonzero rows n) K (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hK
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _=>CenteredMomentFirstAnnularMajorant.profile_nonneg _)
    (fun h hh=>by
      have hn:=activeRows_norm rows n h hh
      have hm:=CenteredMomentFirstAnnularMajorant.scaled_majorant
        (dyadicScale (n 1)) (normValue h) (dyadicScale_pos _) hn.2.1.le hn.2.2.le
      simpa only [normValue_eq_embedding] using hm.ge)
    E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound

end

end RiemannHypothesis.Family003
