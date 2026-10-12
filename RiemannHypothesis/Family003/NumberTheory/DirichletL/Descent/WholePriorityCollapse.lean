/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/WholePriorityCollapse.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityCollapse
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.WholePriorityRays
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.WholePriorityPrincipal
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem whole_assigned_source_original
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    (∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y))=
    ∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      H (parent p (fixedPoint cube C E old D)) := by
  rw [activeParents,←wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj,
    sum_activeFixedSource]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector D≠0
  · rw [ite_eq_left hs]
    simp only [fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
  · rw [ite_eq_right hs,priorityOuter_zero p hg cube negative Ψ m selector ray core D (not_ne_iff.mp hs)]
    simp

theorem whole_assigned_source_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    ‖∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y)‖≤
    ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖H (parent p (fixedPoint cube C E old D))‖ := by
  rw [whole_assigned_source_original p hg hinj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
