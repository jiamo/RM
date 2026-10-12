/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/CentralRamified.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralRamified
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsCentralRamifiedQuotient
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.SelectedBounds

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_ramified_normalized (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (alpha eps : ℝ) (x w z : ℂ)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*eps)≤1/2)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50) :
    1/2≤‖ramifiedCorrection η u P hs x w z‖ ∧
    (P.val.absNorm:ℝ)^(-1:ℝ)*
      ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
        ramifiedCorrection η u P hs x w z‖≤
      800*(P.val.absNorm:ℝ)^(-(1/2:ℝ))+
        (if 2≤multiplicity (primaryGenerator P.val) u.val then 12*(P.val.absNorm:ℝ)^(-w.re) else 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal HeckeFamily.O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  constructor
  · have hb := ramifiedClosed_central_lower p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    exact hb
  · rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
    have hb := ramifiedSelected_central_quotient p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    dsimp only at hb
    simpa only [ramifiedCorrection,p,hnorm] using hb
end SevenEighths.ProbeHighRowFamily
end

end RiemannHypothesis.Family003
