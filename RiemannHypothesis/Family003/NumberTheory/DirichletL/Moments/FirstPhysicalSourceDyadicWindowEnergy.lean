/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceDyadicWindowEnergy.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceDyadicWindowEnergy
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowEnergy
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondWindowBudget
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
open IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)

theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end RiemannHypothesis.Family003
