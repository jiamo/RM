/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceNormalization.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0<K)(_hA₀:0<A₀)(_hB₀:0<B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end RiemannHypothesis.Family003
