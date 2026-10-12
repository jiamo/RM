/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/RealCutoff.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.RealCutoff
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Selection.SelectionBridge

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets.W62

theorem mem_cutoff_floor {H : ℕ} (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T)
    (a : Index H) : a ∈ cutoff H ⌊T⌋₊ ↔
      SiegelZerosAwei.W31.weight (H : ℝ) a.coords ≤ T := by
  rw [mem_cutoff hH, Nat.le_floor_iff hT, real_weight_eq]

theorem rectangle_mem_cutoff {H : ℕ} (hH : 0 < H) {U : ℝ} (hU : 0 ≤ U)
    (a : Index H)
    (h0 : (a.coords 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (h1 : (a.coords 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (h2 : (a.coords 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    a ∈ cutoff H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  apply (mem_cutoff_floor hH (by positivity) a).mpr
  exact SiegelZerosAwei.W31.rectangle_weight_le hH' a.coords h0 h1 h2

theorem rectangle_row_enumerated {H : ℕ} (hH : 0 < H) {U : ℝ} (hU : 0 ≤ U)
    (a : Index H)
    (h0 : (a.coords 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (h1 : (a.coords 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (h2 : (a.coords 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    ∃ n < (cutoff H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊).card,
      enumeration H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ n = a := by
  exact W29.finiteEnumeration_complete _ _ (rectangle_mem_cutoff hH hU a h0 h1 h2)

end WeightedTorusJets.W62


end SiegelZeros

end RiemannHypothesis.Family003
