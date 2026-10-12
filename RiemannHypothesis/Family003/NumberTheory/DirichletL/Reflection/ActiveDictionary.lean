/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/ActiveDictionary.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.ActiveDictionary
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.MarkedActiveSets

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

lemma markedActiveEquiv_frozen (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (b : B) :
    (markedActiveEquiv e B T (Sum.inl b)).val=Sum.inl (e (Sum.inr b.val)) := rfl
lemma markedActiveEquiv_residual (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (a : α) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inl a))).val=Sum.inl (e (Sum.inl a)) := rfl
lemma markedActiveEquiv_slot (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (t : T) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inr t))).val=Sum.inr t.val := rfl
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
