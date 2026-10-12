/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Differentials/LogDerivative.lean
  Original module: OAI.NumberTheory.SiegelZeros.Differentials.LogDerivative
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

open Complex

variable {q : ℕ} [NeZero q]

theorem negative_logDerivative_eq_mangoldt_series
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact (DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs).symm

omit [NeZero q] in
theorem gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

theorem LFunction_zero_iff_completed_zero (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.completedLFunction χ s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  simp only [div_eq_zero_iff, gammaFactor_ne_zero_of_re_pos χ hs, or_false]

theorem zero_contribution_nonneg {s : ℝ} {ρ : ℂ}
    (hs : 1 < s) (hρ : ρ.re ≤ 1) :
    0 ≤ (((s : ℂ) - ρ)⁻¹).re := by
  rw [Complex.inv_re]
  apply div_nonneg
  · simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · exact Complex.normSq_nonneg _

theorem real_zero_contribution (s β : ℝ) :
    (((s : ℂ) - (β : ℂ))⁻¹).re = (s - β)⁻¹ := by
  rw [← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re]

end SiegelZerosAwei.W03

end

end SiegelZeros

end RiemannHypothesis.Family003
