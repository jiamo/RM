/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/ConeMapEval.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.ConeMapEval
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.CoeffPolynomialEvalMul

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem coneMap_eq_eval₂ (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) :
    coneMap p f = f.eval₂ (Polynomial.C.comp (algebraMap K (MvPolynomial σ K ⧸ p)))
      (fun o : Option σ => Polynomial.C (o.elim 1 (fun i => Ideal.Quotient.mk p (X i))) *
        Polynomial.X) := by
  rw [coneMap, aeval_def]
  have halg : algebraMap K (Polynomial (MvPolynomial σ K ⧸ p)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K ⧸ p)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K ⧸ p) r
  rw [halg]
  congr 1
  funext o
  cases o <;> simp

theorem coneMap_homogeneousComponent (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) (n : ℕ) :
    coneMap p (homogeneousComponent n f) =
      Polynomial.C ((coneMap p f).coeff n) * Polynomial.X ^ n := by
  simp only [coneMap_eq_eval₂, polynomial_eval₂_homogeneousComponent]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coneIdeal_isHomogeneous (p : Ideal (MvPolynomial σ K)) :
    (coneIdeal p).IsHomogeneous (homogeneousSubmodule (Option σ) K) := by
  apply (Ideal.isHomogeneous_iff_forall_subset _ _).mpr
  intro n f hf
  change GradedRing.proj (homogeneousSubmodule (Option σ) K) n f ∈ coneIdeal p
  rw [GradedRing.proj_apply]
  change (MvPolynomial.decomposition.decompose' f n : MvPolynomial (Option σ) K) ∈ coneIdeal p
  rw [MvPolynomial.decomposition.decompose'_apply]
  change coneMap p (homogeneousComponent n f) = 0
  rw [coneMap_homogeneousComponent, show coneMap p f = 0 from hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end WeightedTorusJets.Geometry



end SiegelZeros

end RiemannHypothesis.Family003
