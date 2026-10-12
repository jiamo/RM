/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistence.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistence
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CanonicalRankExistenceInduction
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.CanonicalReferenceThreshold

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment

theorem actual_rank_reference_cutoffs : RankReferenceCutoffs :=by
  intro lo hi hlo hhi
  obtain ⟨Vlog,Alog,hA,hAe,hcompact,hsupport,hbox,hone,hzero⟩:=
    exists_canonical_reference_cutoff lo hi
  exact ⟨Vlog,Alog,hbox,hone⟩

theorem actual_rank_reference_thresholds : RankReferenceThresholds :=by
  intro eta heta hi Alog window
  exact eventually_canonical_reference_gates hi Alog window eta heta

theorem canonical_rank_energy_exists
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32)
    (n:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    RankEnergyExists n L cstar cutoff eta K W :=
  rank_energy_exists_all_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    L cstar cutoff eta K hL hcstar hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=
  canonical_energy_exists_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
