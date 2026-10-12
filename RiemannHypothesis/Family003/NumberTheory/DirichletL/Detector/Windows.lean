/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/Windows.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.Windows
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.Physical

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])

theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
