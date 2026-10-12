/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/ActualChildStatePuncture.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStatePuncture
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.ActualChildStateSupport

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseSecondFibers CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma actual_inherited_puncture_dvd (m : O) (γ : OuterTriple) :
    m∣actualSecondInheritedPuncture m γ := by
  refine ⟨ConcretePrimeRowBridge.idealGenerator γ.quotient*primaryGenerator γ.q0*
    primaryGenerator γ.residual,?_⟩
  unfold actualSecondInheritedPuncture actualSecondPuncture
  ring

lemma actual_inherited_radical_puncture_span (m : O) (γ : OuterTriple) :
    Ideal.span {actualSecondInheritedRadicalPuncture m γ}=
      (Ideal.span {actualSecondInheritedPuncture m γ}:Ideal O).radical :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma actual_inherited_radical_preserves_support (m : O) (γ : OuterTriple) :
    (Ideal.span {m}:Ideal O).radical∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.dvd_iff_le]
  apply Ideal.radical_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact actual_inherited_puncture_dvd m γ

lemma actual_inherited_radical_preserves_fixed (m : O) (γ : OuterTriple) (Q : Ideal O)
    (hQ : Q.radical=Q) (hparent : Q∣Ideal.span {m}) :
    Q∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  apply dvd_trans _ (actual_inherited_radical_preserves_support m γ)
  rw [Ideal.dvd_iff_le,←hQ]
  exact Ideal.radical_mono (Ideal.dvd_iff_le.mp hparent)

lemma actual_inherited_radical_is_radical (m : O) (γ : OuterTriple) :
    (Ideal.span {actualSecondInheritedRadicalPuncture m γ}:Ideal O).radical=
      Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.radical_idem]

end SevenEighths.InverseMoment
end

end RiemannHypothesis.Family003
