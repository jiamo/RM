/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/EvalOneInvariantJetMonomial.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.EvalOneInvariantJetMonomial
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.InvariantJetMonomial

namespace RiemannHypothesis.Family003

namespace SiegelZeros

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem eval_one_invariantJet_monomial (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : ι →₀ ℕ) (r : R) :
    MvPolynomial.eval (fun _ => 1) (invariantJet c a (MvPolynomial.monomial m r)) =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) * r := by
  rw [invariantJet_monomial, MvPolynomial.smul_eval, MvPolynomial.eval_monomial]
  simp

end WeightedTorusJets.Geometry


end SiegelZeros

end RiemannHypothesis.Family003
