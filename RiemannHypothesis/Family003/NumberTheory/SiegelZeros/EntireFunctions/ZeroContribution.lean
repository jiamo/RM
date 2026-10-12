/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/ZeroContribution.lean
  Original module: OAI.NumberTheory.SiegelZeros.EntireFunctions.ZeroContribution
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.LogDerivative

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

variable {q : ℕ} [NeZero q]

theorem LFunction_zero_re_lt_one (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    (le_of_not_gt h) hρ

theorem actual_zero_contribution_nonneg (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    {s : ℝ} (hs : 1 < s) : 0 ≤ (((s : ℂ) - ρ)⁻¹).re :=
  zero_contribution_nonneg hs (LFunction_zero_re_lt_one χ hχ hρ).le

theorem retain_real_zero {ι : Type*} (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ρ : ι → ℂ) (hzeros : ∀ i, DirichletCharacter.LFunction χ (ρ i) = 0)
    {s β : ℝ} (hs : 1 < s) (iβ : ι) (hiβ : ρ iβ = (β : ℂ))
    (hsum : Summable (fun i => (((s : ℂ) - ρ i)⁻¹).re)) :
    (s - β)⁻¹ ≤ ∑' i, (((s : ℂ) - ρ i)⁻¹).re := by
  have hle := hsum.le_tsum iβ (fun i _ =>
    actual_zero_contribution_nonneg χ hχ (hzeros i) hs)
  simpa only [hiβ, real_zero_contribution] using hle

end SiegelZerosAwei.W03

end

end SiegelZeros

end RiemannHypothesis.Family003
