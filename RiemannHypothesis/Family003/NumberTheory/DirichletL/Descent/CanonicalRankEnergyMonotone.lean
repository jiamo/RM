/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalRankEnergyMonotone.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankEnergyMonotone
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
