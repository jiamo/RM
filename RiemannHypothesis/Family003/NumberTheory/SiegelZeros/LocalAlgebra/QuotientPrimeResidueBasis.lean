/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/QuotientPrimeResidueBasis.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.QuotientPrimeResidueBasis
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W24

section Surjective

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

def surjective_prime_residueAlgEquiv
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) : P.ResidueField ≃ₐ[k] Q.ResidueField :=
  AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ P Q f hPQ)
    ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective P Q hPQ)

@[simp] theorem surjective_prime_residueAlgEquiv_algebraMap
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) (a : A) :
    surjective_prime_residueAlgEquiv f hf P Q hPQ (algebraMap A P.ResidueField a) =
      algebraMap B Q.ResidueField (f a) :=
  Ideal.ResidueField.map_algebraMap P Q f.toRingHom hPQ a

theorem surjective_prime_residueAlgEquiv_basis
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom)
    {ι : Type*} (b : ι → P.ResidueField) (hb : IsTranscendenceBasis k b) :
    IsTranscendenceBasis k (fun i => surjective_prime_residueAlgEquiv f hf P Q hPQ (b i)) :=
  (surjective_prime_residueAlgEquiv f hf P Q hPQ).isTranscendenceBasis hb

end Surjective

section Quotient

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem quotient_prime_comap (P Q : Ideal A) (hPQ : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change Q ⊔ RingHom.ker (Ideal.Quotient.mk P) = Q
  rw [Ideal.mk_ker, sup_eq_left.mpr hPQ]

def quotientPrimeResidueAlgEquiv
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    Q.ResidueField ≃ₐ[k] (Q.map (Ideal.Quotient.mk P)).ResidueField := by
  letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  exact surjective_prime_residueAlgEquiv (Ideal.Quotient.mkₐ k P)
    Ideal.Quotient.mk_surjective Q (Q.map (Ideal.Quotient.mk P))
    (quotient_prime_comap P Q hPQ).symm

theorem quotientPrimeResidueAlgEquiv_basis
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q)
    {ι : Type*} (b : ι → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    IsTranscendenceBasis k (fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (b i)) := by
  exact (quotientPrimeResidueAlgEquiv (k := k) P Q hPQ).isTranscendenceBasis hb

end Quotient

end WeightedTorusJets.W24

end

end

end SiegelZeros

end RiemannHypothesis.Family003
