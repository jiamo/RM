/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondSourcePoisson.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourcePoisson
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondSourceEnergy
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourcePoisson
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentSecondSourceEnergy CenteredMomentSupportedCorrelation CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O

theorem secondSourceKernel_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        ∑' h : O,actualCorrelation (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) (-h)*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/
            ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2) := by
  unfold secondSourceKernel
  simp only [primaryGaussRow,dite_eq_left hI,dite_eq_left hJ,gaussRow]
  rw [sextic_gauss_pair_poisson _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ) W K hK]
  simp only [primary_span_supported I hI,primary_span_supported J hJ]

theorem sourceGaussEnergy_poisson (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖eisEmbedding h‖^2/
                ‖eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end SevenEighths.CenteredMomentSecondSourcePoisson

end

end RiemannHypothesis.Family003
