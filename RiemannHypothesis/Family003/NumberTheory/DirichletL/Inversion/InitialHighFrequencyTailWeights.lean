/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailWeights.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailWeights
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]

theorem marked_support_norm_bound
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by exact_mod_cast hc)

theorem initialColumn_mark_factor
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h H S‖≤‖H S‖ := by
  rw [initialColumn_mark_factor,norm_mul]
  exact (mul_le_mul_of_nonneg_right
    ((initialColumn_norm_le p hp hcop hg hc Ψ j C d h S).trans (hΨ _))
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.InverseInitialHighFrequencyTail

end

end RiemannHypothesis.Family003
