/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialCommonRatios.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonRatios
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialCommonTuples

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace SevenEighths.InverseInitialCommonRatios
open InverseInitialOverlap InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property

omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj

omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]

omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]

end SevenEighths.InverseInitialCommonRatios

end

end RiemannHypothesis.Family003
