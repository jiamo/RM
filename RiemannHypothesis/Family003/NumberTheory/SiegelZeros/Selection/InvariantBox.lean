/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Selection/InvariantBox.lean
  Original module: OAI.NumberTheory.SiegelZeros.Selection.InvariantBox
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.InvariantDerivation
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.BoxPolynomials

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace W17

variable {K : Type*} [Field K]

theorem invariantDerivation_mem_boxPolynomials (v : Fin 4 → K) {N : ℕ}
    {F : MvPolynomial (Fin 4) K} (hF : F ∈ boxPolynomials K N) :
    WeightedTorusJets.W18.invariantDerivation v F ∈ boxPolynomials K N :=
  WeightedTorusJets.W18.inBox_invariantDerivation v hF

end W17


end SiegelZeros

end RiemannHypothesis.Family003
