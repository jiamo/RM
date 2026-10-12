/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/FinsuppCandidates.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.FinsuppCandidates
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.ParameterCombinations

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

variable {k σ ι : Type*} [CommRing k]

theorem linearCombination_eq_parameterCombination (f : ι → MvPolynomial σ k) (c : ι →₀ k) :
    Finsupp.linearCombination k f c = parameterCombination c.support c f := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, parameterCombination,
    MvPolynomial.C_mul']

theorem linearCombination_totalDegree_le (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (Finsupp.linearCombination k f c).totalDegree ≤ d := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_totalDegree_le c.support c f (fun i _ => hf i)

theorem linearCombination_mem_ideal (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    (J : Ideal (MvPolynomial σ k)) (hf : ∀ i, f i ∈ J) :
    Finsupp.linearCombination k f c ∈ J := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_mem c.support c f J (fun i _ => hf i)

end WeightedTorusJets.W22

end

end SiegelZeros

end RiemannHypothesis.Family003
