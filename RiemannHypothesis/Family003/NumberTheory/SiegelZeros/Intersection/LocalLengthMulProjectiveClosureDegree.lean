/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Intersection/LocalLengthMulProjectiveClosureDegree.lean
  Original module: OAI.NumberTheory.SiegelZeros.Intersection.LocalLengthMulProjectiveClosureDegree
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.FinrankDerivationCardTranscendenceBasis
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.GradedIdealQuotient
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.ConeMapEval
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.LinearVariableBasis

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets.Geometry

open MvPolynomial

attribute [local instance] coneIdeal_isPrime

theorem local_length_mul_projectiveClosure_degree_le
    {K σ : Type*} [Field K] [Infinite K] [Finite σ] {h D : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hp : p.height = h)
    (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))) *
      (GradedQuotient.projectiveDegree (coneIdeal p) (coneIdeal_isHomogeneous p) : ℕ∞) ≤
        (D ^ h : ℕ) := by
  obtain ⟨d, _, g, hg, hint, hfinite, hlin, _, _⟩ :=
    LinearNormalization.exists_finite_linear_normalization_finite_variables
      (coneIdeal p) (coneIdeal_isHomogeneous p) none (X_none_not_mem_coneIdeal p)
  have hcount : d + 1 + h = Nat.card (Option σ) := by
    have hc := polynomial_normalization_count_add_height_finite
      (coneIdeal p) g hg hint
    rw [coneIdeal_height, hp] at hc
    exact_mod_cast hc
  let F : Fin h → MvPolynomial (Option σ) K := fun i => homogenize (f i)
  have hF (i : Fin h) : (F i).totalDegree ≤ D := by
    simpa only [F, homogenize_totalDegree] using hf i
  have hrad' : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
        (F i)))).radical = IsLocalRing.maximalIdeal (Localization.AtPrime (coneIdeal p)) := by
    have ha : ((Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hrad
    simpa only [paddedHomogenizedIdeal, pow_zero, one_mul, Ideal.map_span,
      ← Set.range_comp, Function.comp_def, F] using
      cone_padded_local_radical p f (fun _ => 0) ha
  have hlength :
      Module.length (Localization.AtPrime (coneIdeal p))
        (Localization.AtPrime (coneIdeal p) ⧸ Ideal.span (Set.range (fun i =>
          algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
            (F i)))) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
          algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))) := by
    have hA : (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime p)) =
          Ideal.span (Set.range (fun i =>
            algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have hC : (paddedHomogenizedIdeal f (fun _ => 0)).map
        (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))) =
          Ideal.span (Set.range (fun i =>
            algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p))
              (F i))) := by
      simp only [paddedHomogenizedIdeal, pow_zero, one_mul, Ideal.map_span,
        ← Set.range_comp, Function.comp_def, F]
    exact (DegreeBezout.quotient_length_congr_ideal _ _ hC).symm.trans
      ((cone_padded_quotient_length p f (fun _ => 0)).trans
        (DegreeBezout.quotient_length_congr_ideal _ _ hA))
  have hdegree := GradedQuotient.projectiveDegree_eq_normalization_rank_finiteVariables
    (coneIdeal p) (coneIdeal_isHomogeneous p) g hg hint hlin
  have hbound := DegreeBezout.linear_normalization_weighted_local_length_le
    (coneIdeal p) g hg hfinite hlin hcount F hF hrad'
  rw [hlength, ← hdegree] at hbound
  exact hbound

end WeightedTorusJets.Geometry



end SiegelZeros

end RiemannHypothesis.Family003
