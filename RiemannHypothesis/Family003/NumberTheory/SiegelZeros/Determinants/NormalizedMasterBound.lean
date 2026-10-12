/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Determinants/NormalizedMasterBound.lean
  Original module: OAI.NumberTheory.SiegelZeros.Determinants.NormalizedMasterBound
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib
import RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace RiemannHypothesis.Family003

namespace SiegelZeros

namespace WeightedTorusJets.FinalComparison

theorem normalized_master_bound
    {L S₁ S₂ M U ℓ logN logU logM δ C C_H : ℝ}
    (hS₁ : 0 < S₁) (hlogU : 0 < logU) (hℓ : 0 < ℓ)
    (hN : logN = 3 / 4 * logU)
    (harch : L ≤ M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (logU - C * ℓ - C * δ * logU ^ 2 / ℓ - C_H) - C * M * U ≤ L) :
    1 ≤ 3 / 4 * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
      (C * M * U + 1 / 2 * M * logM) / (S₁ * logU) := by
  apply (mul_le_mul_iff_left₀ (mul_pos hS₁ hlogU)).mp
  have hEq : S₁ * logU *
      (3 / 4 * (1 + S₂ / S₁) +
        (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
        (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
        (C * M * U + 1 / 2 * M * logM) / (S₁ * logU)) =
      M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8) +
        S₁ * (C * ℓ + C * δ * logU ^ 2 / ℓ + C_H) + C * M * U := by
    rw [hN]
    field_simp
    ring
  conv_rhs => rw [mul_comm]
  rw [hEq, one_mul]
  linarith

end WeightedTorusJets.FinalComparison


end SiegelZeros

end RiemannHypothesis.Family003
