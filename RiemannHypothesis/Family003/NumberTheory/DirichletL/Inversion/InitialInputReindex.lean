/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialInputReindex.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialInputReindex
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialTotalFourier

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=>L i.val) (fun i:I=>a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=>primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=>L i.val) (fun i:{i:σ//i∉J}=>a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=>primeSlot (L i) (a i) A)).symm

end SevenEighths.InverseInitialInputReindex

end

end RiemannHypothesis.Family003
