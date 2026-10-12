/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/FinrankDegreePiecePosPrimeVariableNotMem.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.FinrankDegreePiecePosPrimeVariableNotMem
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - `set_option synthInstance.maxHeartbeats 400000` on one theorem: instance search for `Module.IsTorsionFree K (degreePiece I n)` exceeds the default limit at the host pin; the proof is unchanged.
-/
import Mathlib
import RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Hilbert.HilbertSeries
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.ConeMapEval

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_degreePiece_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K)) (hprime : I.IsPrime)
    {i : σ} (hi : X i ∉ I) (n : ℕ) :
    0 < Module.finrank K (degreePiece I n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨Ideal.Quotient.mk I (X i ^ n), X i ^ n, isHomogeneous_X_pow i n, rfl⟩, ?_⟩
  intro hzero
  exact hi (hprime.mem_of_pow_mem n
    (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hzero)))

theorem hilbertPolynomial_ne_zero_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : hilbertPolynomial I hI ≠ 0 := by
  obtain ⟨i, hi⟩ := hvars
  obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
  intro hzero
  have h := hN (N + 1) (by omega)
  rw [hzero, Polynomial.eval_zero] at h
  have hpos := finrank_degreePiece_pos_of_prime_variable_not_mem I hprime hi (N + 1)
  exact (Nat.ne_of_gt hpos) (by exact_mod_cast h)

theorem projectiveDegree_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : 0 < projectiveDegree I hI :=
  (projectiveDegree_pos_iff I hI).mpr
    (hilbertPolynomial_ne_zero_of_prime_variable_not_mem I hI hprime hvars)

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
open MvPolynomial

theorem cone_projectiveDegree_pos
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    0 < projectiveDegree (coneIdeal p) (coneIdeal_isHomogeneous p) :=
  projectiveDegree_pos_of_prime_variable_not_mem
    (coneIdeal p) (coneIdeal_isHomogeneous p) (coneIdeal_isPrime p)
    ⟨none, X_none_not_mem_coneIdeal p⟩

end WeightedTorusJets.Geometry.GradedQuotient



end SiegelZeros

end RiemannHypothesis.Family003
