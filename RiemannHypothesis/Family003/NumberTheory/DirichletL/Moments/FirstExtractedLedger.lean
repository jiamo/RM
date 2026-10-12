/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstExtractedLedger.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstExtractedLedger
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.DescentLedger

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExtractedLedger
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

theorem actual_extracted_first_saving (I J:Ideal O) (hI:Supported I) (hJ:Supported J)
    (Z:ℝ) (hZ:1<Z):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let B:=c+d-2*p-R
    ∀D₀ w q wo g ell σ δ:ℝ,0≤w → 0≤q → 0≤wo → 0≤σ → 0≤δ →
      R≤q → d-δ≤D₀ → g≤max (D₀-c-2*w+wo) 0+2*σ → 0≤ell → w≤7*σ/3 →
      2*(c+w)/3-3*σ-5*δ/6≤firstSaving c D₀ w q wo B g ell:=by
  dsimp only
  intro D₀ w q wo g ell σ δ hw hq hwo hσ hδ hR hD hg hell hwσ
  have ha:=actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at ha
  have hn:(1:ℝ)≤((commonPart I J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (commonPart_supported I J hI).1)
  have hc:0≤Real.logb Z ((commonPart I J).absNorm:ℝ):=Real.logb_nonneg hZ hn
  have hsecond:0≤max (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  have hfirst:0≤max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  exact firstSaving_lower _ _ D₀ w q _ wo _ g ell σ δ hc hw hq hwo
    (by linarith) hσ hδ hR (by linarith) hD hg hell hwσ

end SevenEighths.CenteredMomentFirstExtractedLedger

end

end RiemannHypothesis.Family003
