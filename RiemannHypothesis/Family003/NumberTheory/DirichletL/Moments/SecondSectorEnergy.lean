/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondSectorEnergy.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondSectorChildren
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.RestrictedSource

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,hτ I (sectorPool_supported C hC.1 S I) t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem sector_child_row (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) =>
          (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) z := by
  have he := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L t)
  rw [he,sector_rowPolynomial S (fun I => (if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  congr 1
  funext I
  split_ifs <;> simp_all

theorem sector_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) W K=
      sourceRestrictedEnergy keep (residualPool C hC.1 S)
        (fun I => if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) W K := by
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_child_row η τ χ A hτ S β C hC L t z]

end SevenEighths.CenteredMomentSecondSectorEnergy

end

end RiemannHypothesis.Family003
