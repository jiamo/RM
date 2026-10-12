/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Selection/GlobalPivotValuationExponent.lean
  Original module: OAI.NumberTheory.SiegelZeros.Selection.GlobalPivotValuationExponent
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Selection.GreedyPivotsWeightLowSpan

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section
namespace WeightedTorusJets

theorem global_pivot_valuation_exponent_eq {ι : Type*} [Fintype ι]
    (α : ι ↪ (Fin 3 → ℕ)) (P : Finset (Fin 3 → ℕ))
    (hP : Set.range α = (P : Set (Fin 3 → ℕ))) (p : ℕ) :
    (∑ i, α i 0 / p) = ∑ a ∈ P, ⌊(a 0 : ℝ) / p⌋₊ := by
  rw [sum_embedding_eq_sum_finset_of_range α P hP (fun a => a 0 / p)]
  simp only [Nat.floor_div_eq_div]

end WeightedTorusJets

namespace WeightedTorusJets

theorem global_pivot_valuation_exponent_cast_eq {ι : Type*} [Fintype ι]
    (α : ι ↪ (Fin 3 → ℕ)) (P : Finset (Fin 3 → ℕ))
    (hP : Set.range α = (P : Set (Fin 3 → ℕ))) (p : ℕ) :
    ((∑ i, α i 0 / p : ℕ) : ℝ) = ∑ a ∈ P, (⌊(a 0 : ℝ) / p⌋ : ℝ) := by
  rw [global_pivot_valuation_exponent_eq α P hP p, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact natCast_floor_eq_intCast_floor (by positivity)

end WeightedTorusJets

end

end SiegelZeros

end RiemannHypothesis.Family003
