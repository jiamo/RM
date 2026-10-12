/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/LowPunctureLists.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.LowPunctureLists
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.PunctureLists
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.CanonicalPool
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
