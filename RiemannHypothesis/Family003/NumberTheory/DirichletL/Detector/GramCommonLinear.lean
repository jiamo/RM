/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonLinear
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramCommonParam

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
