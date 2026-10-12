/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstIdealFamily.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstIdealFamily
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SourceRow

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstIdealFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstColumns
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_one_primary (η : Character) (m : O) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight η m 1 1 t I=elementCoeff η (CompletedGauss.primaryGenerator I)*
      coprimalityMask m (CompletedGauss.primaryGenerator I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have he : idealCoeff η I=elementCoeff η (CompletedGauss.primaryGenerator I) := by
    have hh := idealCoeff_span η hn
    rw [hs] at hh
    exact hh
  have hm : idealRowHom (m^6) I=coprimalityMask m (CompletedGauss.primaryGenerator I) := by
    have hh := idealRowHom_sixth_eq_mask m _ (hs.symm ▸ hI)
    rw [hs] at hh
    exact hh
  change (idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
  rw [mul_one,mul_one,he,hm]

theorem ideal_height_of_primary (η τ : Character) (m : O) (F : O → ℂ)
    (hτ : ∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
      elementCoeff τ n=elementCoeff η n*coprimalityMask m n*F n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
      rowWeight η m 1 1 t I*F (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  have he := hτ (CompletedGauss.primaryGenerator I) (hs.1.symm ▸ hI) hs.2
  rw [← idealCoeff_span τ hn,hs.1] at he
  rw [he,rowWeight_one_primary η m t I hI]
  ring

theorem exists_first_ideal_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₁ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (leftCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₁ (CompletedGauss.primaryGenerator I))) ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₂ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (rightCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₂ (CompletedGauss.primaryGenerator I))) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_canonical_first_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro I hI t
    apply ideal_height_of_primary η τ₁ m
      (fun n => leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₁ n) _ I hI t
    intro n hn hp
    rw [h₁ n hn hp]
    ring
  · intro I hI t
    apply ideal_height_of_primary η τ₂ m
      (fun n => rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₂ n) _ I hI t
    intro n hn hp
    rw [h₂ n hn hp]
    ring

end SevenEighths.CenteredMomentFirstIdealFamily

end

end RiemannHypothesis.Family003
