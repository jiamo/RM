/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/PuncturedMarks.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.PunctureAbsorption
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]

lemma markedCompletedT_zero_punctured_slot {σ : Type*} [Fintype σ]
    (S : PrimeFamily σ) (i : σ) (Ψ : Eis→*ℂ) (m f z : Eis) (hm : m∈S.ideal i)
    (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ j,if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  apply markedCompletedT_zero_punctured Ψ m f z (S.ideal i)
    (Ideal.prime_of_isPrime (NeZero.ne (S.ideal i)) inferInstance) hm W X
  intro A hA
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA)
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
