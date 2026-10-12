/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/GreedyPivotsRingEquiv.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.GreedyPivotsRingEquiv
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.AlgebraMapMemSpanImage

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets

theorem greedyPivots_ringEquiv {K L ι : Type*} [Field K] [Field L] [Fintype ι]
    (e : K ≃+* L) (v : ℕ → ι → K) (T : ℕ) :
    greedyPivots L (fun i => e ∘ v i) T = greedyPivots K v T := by
  let : Algebra K L := e.toRingHom.toAlgebra
  exact greedyPivots_algebraMap (L := L) v T

theorem source_greedy_indices_transport {K L ι α : Type*}
    [Field K] [Field L] [Fintype ι]
    (e : K ≃+* L) (R : α → ι → K) (R' : α → ι → L)
    (hR : ∀ a j, e (R a j) = R' a j) (order : ℕ → α) (T : ℕ) :
    greedyPivots L (R' ∘ order) T = greedyPivots K (R ∘ order) T := by
  have h : R' ∘ order = fun i => e ∘ (R ∘ order) i := by
    funext i j
    exact (hR (order i) j).symm
  rw [h]
  exact greedyPivots_ringEquiv e (R ∘ order) T

end WeightedTorusJets


end SiegelZeros

end RiemannHypothesis.Family003
