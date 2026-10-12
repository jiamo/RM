/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/PunctureLists.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.PunctureLists
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.PuncturedMarks
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.SlotCoefficients
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.MarkedTuples
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) : σ→Finset (Ideal Eis) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma sum_puncture_lists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rfl
      · exact hz p (by simpa only [not_forall,not_not] using h)
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

theorem original_completed_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P) (S : Finset (Ideal Eis))
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists S i,(∏ i,w i (punctureListLift lists S p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists S
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m*excludedGenerator S∈(p i).val := (p i).val.mul_mem_left m (excludedGenerator_mem S hi)
  have hz := markedCompletedT_zero_punctured Ψ (m*excludedGenerator S) f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
