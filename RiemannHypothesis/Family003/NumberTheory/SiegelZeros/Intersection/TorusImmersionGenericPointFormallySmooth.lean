/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Intersection/TorusImmersionGenericPointFormallySmooth.lean
  Original module: OAI.NumberTheory.SiegelZeros.Intersection.TorusImmersionGenericPointFormallySmooth
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
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicForm

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section
open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets.Geometry

theorem torus_immersion_genericPoint_formallySmooth
    {X : Scheme} [IsIntegral X]
    (j : X ⟶ Spec (.of (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ)))) [IsImmersion j] :
    ((j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))))).stalkMap
        (genericPoint X)).hom.FormallySmooth := by
  have : Algebra.FiniteType ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ)) :=
    WeightedTorusJets.laurent_finiteType
  let b := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))))
  have : LocallyOfFiniteType b :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact (j ≫ b).genericPoint_mem_smoothLocus_of_perfectField

end WeightedTorusJets.Geometry

end

end SiegelZeros

end RiemannHypothesis.Family003
