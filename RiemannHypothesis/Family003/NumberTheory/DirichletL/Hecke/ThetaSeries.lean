/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.ThetaSeries
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - proof tweak: after convert, close residual instance-equality goals with 'with_reducible_and_instances rfl' (host instances are not reducibly defeq)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.Theta
import RiemannHypothesis.Family003.NumberTheory.DirichletL.LatticeSummability

namespace RiemannHypothesis.Family003

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

@[simp] theorem periodicCoeff_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    periodicCoeff w (0, 0) = w (0, 0) := by
  simp [periodicCoeff, residueEquiv, regroup, Int.divModEquiv, Int.natMod]

theorem norm_periodicCoeff_le {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)

private theorem normForm_coordinates_eq_zero (n : ℤ × ℤ) :
    normForm n.1 n.2 = 0 ↔ n = (0, 0) := by
  rw [normForm_eq_zero_iff]
  simp only [Int.cast_eq_zero, Prod.ext_iff]

theorem theta_sub_zero_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by
  have h := (theta_hasSum w ht).sub (hasSum_ite_eq (0, 0) (w (0, 0)))
  rw [pair_f₀]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [normForm_coordinates_eq_zero]
  by_cases hn : n = (0, 0)
  · subst n
    simp [normForm]
  · simp [hn]

theorem completed_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by
  have hsum : Summable (fun n : ℤ × ℤ => ‖periodicCoeff w n‖ /
      normForm n.1 n.2 ^ s.re) :=
    summable_weighted_normForm (norm_periodicCoeff_le w) hs
  have h := hasSum_mellin_pi_mul₀
    (a := periodicCoeff w) (p := fun n : ℤ × ℤ => normForm n.1 n.2)
    (F := fun t => (pair w).f t - (pair w).f₀)
    (fun _ => normForm_nonneg _ _) (by linarith : 0 < s.re)
    (fun _ ht => theta_sub_zero_hasSum w ht) hsum
  rwa [(pair_hasMellin w hs).2] at h

theorem latticeL_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ s ≠ 0 := fun h => hπ ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := (completed_hasSum w hs).mul_left ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹)
  change HasSum _ ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Complex.cpow_neg]
  field_simp

end SevenEighths.HeckeTheta

end

end RiemannHypothesis.Family003
