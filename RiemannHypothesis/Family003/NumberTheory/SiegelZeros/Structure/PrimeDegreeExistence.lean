/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/PrimeDegreeExistence.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.PrimeDegreeExistence
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Hilbert.PrimeHilbertComparison

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace WeightedTorusJets.W27
open WeightedTorusJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem exists_prime_hilbert_polynomial_degree_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ,
      (∀ n : ℕ, N < n →
        (Module.finrank k (quotientSection P n) : ℚ) = p.eval (n : ℚ)) ∧
      1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  obtain ⟨p, N, hp⟩ := exists_homogeneous_hilbert_polynomial σ P hP
  refine ⟨p, N, hp, ?_⟩
  apply prime_eventual_hilbert_degree_ge_one P i hi p (N+1)
  intro n hn
  exact (hp n (by omega)).symm

omit [Fintype σ] in
theorem quotient_eventual_hilbert_coefficient_nonneg
    (I : Ideal (MvPolynomial σ k)) (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ))
    (hd : p.natDegree ≤ d) : 0 ≤ p.coeff d * (d.factorial : ℚ) := by
  have hl : 0 ≤ p.leadingCoeff :=
    polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N (by
      intro n hn
      rw [hp n hn]
      positivity)
  rcases eq_or_lt_of_le hd with heq | hlt
  · rw [← heq, ← Polynomial.leadingCoeff]
    exact mul_nonneg hl (by positivity)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

end WeightedTorusJets.W27

end

end SiegelZeros

end RiemannHypothesis.Family003
