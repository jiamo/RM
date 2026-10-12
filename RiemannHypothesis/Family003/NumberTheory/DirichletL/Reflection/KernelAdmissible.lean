/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/KernelAdmissible.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.KernelAdmissible
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.PhysicalBranchMeasure

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)

lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)

lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable

lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable

end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
