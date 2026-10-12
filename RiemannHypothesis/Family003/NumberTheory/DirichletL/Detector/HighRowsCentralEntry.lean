/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighRowsCentralEntry.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralEntry
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsCentralStrict
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_central_strict_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j<6) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (3/2) (1-x.re-w.re)
  · have hb := squarefree_base_strict_norm p hp hg hc j hj
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) by linarith)
  · norm_num ; linarith

include hc in
lemma sourceRowTerm_central_boundary_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (1/2) (-x.re-w.re)
  · have hb := squarefree_base_boundary_norm p hp hg hc j hj
    rw [Real.sqrt_eq_rpow] at hb
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) by linarith)
  · norm_num
end SevenEighths.ProbeEuler
end

end RiemannHypothesis.Family003
