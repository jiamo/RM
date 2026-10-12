/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Selection/JetRowAutCongr.lean
  Original module: OAI.NumberTheory.SiegelZeros.Selection.JetRowAutCongr
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


namespace WeightedTorusJets

theorem source_jet_row_autCongr
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) (σ τ : K ≃ₐ[ℚ] K) (θ : K) (α : Fin 3 → ℕ) :
    e (θ ^ α 0 * σ θ ^ α 1 * (σ * τ) θ ^ α 2) =
      e θ ^ α 0 * (AlgEquiv.autCongr e σ) (e θ) ^ α 1 *
        (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (e θ) ^ α 2 := by
  have he (φ : K ≃ₐ[ℚ] K) (x : K) : (AlgEquiv.autCongr e φ) (e x) = e (φ x) := by
    change e (φ (e.symm (e x))) = e (φ x)
    rw [e.symm_apply_apply]
  simp only [map_mul, map_pow, AlgEquiv.mul_apply, he]

end WeightedTorusJets


end SiegelZeros

end RiemannHypothesis.Family003
