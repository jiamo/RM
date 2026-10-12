/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstAnnularInput.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstAnnularAmplification
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationChildInput

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal HeckeFamily.O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      ((original (child s C R B τ t) (R*C) seed).coefficient τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end SevenEighths.CenteredMomentFirstAnnularInput

end

end RiemannHypothesis.Family003
