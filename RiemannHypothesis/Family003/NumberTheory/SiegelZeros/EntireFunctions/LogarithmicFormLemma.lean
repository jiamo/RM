/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/LogarithmicFormLemma.lean
  Original module: OAI.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicFormLemma
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
open WeightedTorusJets.Geometry

theorem WeightedTorusJets.Geometry.logarithmic_form_lemma_source
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c) :
    (∀ (P : Ideal (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))) (hP : P.IsPrime),
      letI := hP
      0 < ringKrullDim (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ) ⧸ P) →
      let A := AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ) ⧸ P
      let F := FractionRing A
      let x := fun i ↦ algebraMap _ F
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
      let T := LinearMap.range (logarithmicTangentMap (k := ℂ) x)
      logarithmicForm c x ≠ 0 ∧
      Module.finrank F (LinearMap.range
        (T.mkQ.domRestrict (LinearMap.ker (logarithmicLinearForm c)))) =
          4 - ((ringKrullDim A).unbotD 0).toNat) ∧
    ∀ y : Fin 4 → ℂˣ,
      Module.finrank ℂ (LinearMap.range
        ((LinearMap.range (logarithmicTangentMap (k := ℂ) (fun i ↦ (y i : ℂ)))).mkQ.domRestrict
          (LinearMap.ker (logarithmicLinearForm (F := ℂ) c)))) = 3 := by
  exact WeightedTorusJets.Geometry.logarithmic_form_lemma_exact (K := ℂ) c hc

end

end SiegelZeros

end RiemannHypothesis.Family003
