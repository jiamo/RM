/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Determinants/NormalSurjectivity.lean
  Original module: OAI.NumberTheory.SiegelZeros.Determinants.NormalSurjectivity
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.SelectedCotangent
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.SmoothConormalExtension

namespace RiemannHypothesis.Family003

noncomputable section

namespace SiegelZeros

namespace WeightedTorusJets.NormalExactness

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R)

def normalRestriction : Derivation K R (R ⧸ I) →ₗ[R ⧸ I]
    (I.Cotangent →ₗ[R ⧸ I] R ⧸ I) where
  toFun := SiegelZeros.W58.residueConormalPairing I
  map_add' D E := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    rfl
  map_smul' a D := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    rfl

@[simp] theorem normalRestriction_toCotangent (D : Derivation K R (R ⧸ I)) (x : I) :
    normalRestriction I D (I.toCotangent x) = D x := rfl

theorem normalRestriction_eq_zero_iff (D : Derivation K R (R ⧸ I)) :
    normalRestriction I D = 0 ↔ ∀ x ∈ I, D x = 0 := by
  constructor
  · intro h x hx
    exact LinearMap.congr_fun h (I.toCotangent ⟨x, hx⟩)
  · intro h
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    exact h x x.property

def quotientDerivation (D : Derivation K R (R ⧸ I))
    (hD : ∀ x ∈ I, D x = 0) : Derivation K (R ⧸ I) (R ⧸ I) where
  toLinearMap := (I.restrictScalars K).liftQ D.toLinearMap (by
    intro x hx
    exact hD x hx)
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change D (a * b) = Ideal.Quotient.mk I a * D b + Ideal.Quotient.mk I b * D a
    exact D.leibniz a b

@[simp] theorem quotientDerivation_mk (D : Derivation K R (R ⧸ I))
    (hD : ∀ x ∈ I, D x = 0) (x : R) :
    quotientDerivation I D hD (Ideal.Quotient.mk I x) = D x := rfl

def tangentInclusion : Derivation K (R ⧸ I) (R ⧸ I) →ₗ[R ⧸ I]
    Derivation K R (R ⧸ I) :=
  Derivation.compAlgebraMapL K R (R ⧸ I) (R ⧸ I)

@[simp] theorem tangentInclusion_apply (D : Derivation K (R ⧸ I) (R ⧸ I)) (x : R) :
    tangentInclusion I D x = D (Ideal.Quotient.mk I x) := rfl

theorem tangentInclusion_injective : Function.Injective (tangentInclusion (K := K) I) := by
  intro D E h
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun F : Derivation K R (R ⧸ I) => F x) h

theorem normalRestriction_kernel_eq_tangent_range :
    LinearMap.ker (normalRestriction (K := K) I) =
      LinearMap.range (tangentInclusion (K := K) I) := by
  ext D
  rw [LinearMap.mem_ker, normalRestriction_eq_zero_iff, LinearMap.mem_range]
  constructor
  · intro hD
    refine ⟨quotientDerivation I D hD, ?_⟩
    ext x
    rfl
  · rintro ⟨E, rfl⟩ x hx
    change E (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem normalRestriction_surjective
    [Algebra.FormallySmooth K R] [Algebra.FormallySmooth K (R ⧸ I)] :
    Function.Surjective (normalRestriction (K := K) I) := by
  intro φ
  obtain ⟨D, hD⟩ :=
    SmoothConormalExtension.exists_derivation_extending_ideal (K := K)
      (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)
      I (show RingHom.ker (algebraMap R (R ⧸ I)) = I from Ideal.mk_ker)
      (φ.restrictScalars R)
  refine ⟨D, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  exact hD x

@[reducible] local instance genericLocalCommSemiring (k : Type*) [Field k]
    (p : Ideal (SiegelZeros.W58.TorusRing k)) [p.IsPrime] :
    CommSemiring (SiegelZeros.W58.GenericLocalRing k p) :=
  (inferInstance : CommRing (SiegelZeros.W58.GenericLocalRing k p)).toCommSemiring

theorem torus_generic_normalRestriction_surjective
    (k : Type*) [Field k] [PerfectField k]
    (p : Ideal (SiegelZeros.W58.TorusRing k)) [p.IsPrime] :
    Function.Surjective (normalRestriction (K := k) (R := SiegelZeros.W58.GenericLocalRing k p)
      (IsLocalRing.maximalIdeal (SiegelZeros.W58.GenericLocalRing k p))) := by
  let := SiegelZeros.W58.generic_local_formallySmooth k p
  let : Algebra.FormallySmooth k
      (SiegelZeros.W58.GenericLocalRing k p ⧸
        IsLocalRing.maximalIdeal (SiegelZeros.W58.GenericLocalRing k p)) := by
    change Algebra.FormallySmooth k
      (IsLocalRing.ResidueField (SiegelZeros.W58.GenericLocalRing k p))
    exact SiegelZeros.W58.generic_residue_formallySmooth k p
  exact normalRestriction_surjective _

end WeightedTorusJets.NormalExactness

end SiegelZeros

end

end RiemannHypothesis.Family003
