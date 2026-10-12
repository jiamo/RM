/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongKeys.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongKeys
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CanonicalLongParent

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks
open InverseMomentFirstOriginalProfile CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Ψ:O→*ℂ)(m mCoef:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=>primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=>normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels)
    (fun x=>x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hcop hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
