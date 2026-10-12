/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Intersection/TorusIntoProj.lean
  Original module: OAI.NumberTheory.SiegelZeros.Intersection.TorusIntoProj
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Intersection.ConeProjectivePoint

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe uTorusClosure

noncomputable def torusIntoProj {K σ : Type uTorusClosure} [CommRing K] [Fintype σ] :
    Spec (CommRingCat.of (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) ⟶
      Proj (homogeneousSubmodule (Option σ) K) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial σ K) (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K))))) ≫
      affineIntoProj (k := K) (fun i : σ => (X i : MvPolynomial σ K))

@[simp]
theorem torusIntoProj_apply {K σ : Type uTorusClosure} [CommRing K] [Fintype σ]
    (q : PrimeSpectrum (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) :
    torusIntoProj (K := K) (σ := σ) q =
      affineIntoProj (k := K) (fun i : σ => (X i : MvPolynomial σ K))
        (PrimeSpectrum.comap
          (algebraMap (MvPolynomial σ K)
            (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) q) := rfl

theorem closure_torusIntoProj_zeroLocus_eq_affine
    {K σ : Type uTorusClosure} [CommRing K] [Fintype σ]
    (J : Ideal (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) :
    closure (torusIntoProj (K := K) (σ := σ) '' PrimeSpectrum.zeroLocus J) =
      closure (affineIntoProj (k := K) (fun i : σ => (X i : MvPolynomial σ K)) ''
        PrimeSpectrum.zeroLocus (J.comap
          (algebraMap (MvPolynomial σ K)
            (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) : Set (MvPolynomial σ K))) := by
  let f := algebraMap (MvPolynomial σ K)
    (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))
  let g : PrimeSpectrum (MvPolynomial σ K) →
      ProjectiveSpectrum (homogeneousSubmodule (Option σ) K) :=
    fun x => affineIntoProj (k := K) (fun i : σ => (X i : MvPolynomial σ K)) x
  have hc : Continuous g :=
    (affineIntoProj (k := K) (fun i : σ => (X i : MvPolynomial σ K))).continuous
  change closure ((fun q => g (PrimeSpectrum.comap f q)) '' PrimeSpectrum.zeroLocus J) =
    closure (g '' PrimeSpectrum.zeroLocus (J.comap f))
  rw [← Set.image_image, ← closure_image_closure hc, PrimeSpectrum.closure_image_comap_zeroLocus]

theorem closure_torusIntoProj_zeroLocus
    {K σ : Type uTorusClosure} [CommRing K] [Fintype σ]
    (q : PrimeSpectrum (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))) :
    closure (torusIntoProj (K := K) (σ := σ) '' PrimeSpectrum.zeroLocus q.asIdeal) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) K)
        (coneIdeal (q.asIdeal.comap
          (algebraMap (MvPolynomial σ K)
            (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K)))))) := by
  let p := q.asIdeal.comap (algebraMap (MvPolynomial σ K)
    (Localization.Away (∏ i : σ, (X i : MvPolynomial σ K))))
  let : p.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  exact (closure_torusIntoProj_zeroLocus_eq_affine q.asIdeal).trans
    (closure_affineIntoProj_zeroLocus p)

end WeightedTorusJets.Geometry

end

end SiegelZeros

end RiemannHypothesis.Family003
