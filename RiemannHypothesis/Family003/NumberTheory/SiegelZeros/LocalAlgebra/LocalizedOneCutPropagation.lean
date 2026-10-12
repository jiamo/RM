/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/LocalizedOneCutPropagation.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedOneCutPropagation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Intersection.LocalIntersectionFormula

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

noncomputable def globalParentCutSum (I Q : Ideal A) [Q.IsPrime] (x : A) : ℕ∞ :=
  ∑ P : MinimalParentsBelow I Q,
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ I.map (algebraMap A (Localization.AtPrime P.val))) *
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (P.val ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)))

omit [IsNoetherianRing A] in
theorem localization_map_cut (I Q : Ideal A) [Q.IsPrime] (x : A) :
    (I ⊔ Ideal.span {x}).map (algebraMap A (Localization.AtPrime Q)) =
      I.map (algebraMap A (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem minimalPrimeCutSum_localization (I Q : Ideal A) [Q.IsPrime] (x : A) :
    minimalPrimeCutSum (I.map (algebraMap A (Localization.AtPrime Q)))
      (algebraMap A (Localization.AtPrime Q) x) = globalParentCutSum I Q x := by
  classical
  let : Fintype (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes :=
    ((I.map (algebraMap A (Localization.AtPrime Q))).finite_minimalPrimes_of_isNoetherianRing
      (Localization.AtPrime Q)).fintype
  unfold minimalPrimeCutSum globalParentCutSum
  apply Fintype.sum_equiv (localizedMinimalPrimesEquiv I Q)
  intro p
  let : p.val.IsPrime := p.property.1.1
  have htower := localPrimeTower_quotient_length Q p.val I
  have hcut :
      ((p.val.comap (algebraMap A (Localization.AtPrime Q))) ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)) =
      p.val ⊔ Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
        IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p.val]
  have hcutlen := congrArg
    (fun K : Ideal (Localization.AtPrime Q) =>
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸ K)) hcut
  exact congrArg₂ HMul.hMul htower.symm hcutlen.symm

theorem localized_onecut_parent_recurrence
    (I Q : Ideal A) [Q.IsPrime] (x : A)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap A (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) x))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x := by
  rw [localization_map_cut]
  exact (local_onecut_length _ _ hdim hregular).trans
    (minimalPrimeCutSum_localization I Q x)

end WeightedTorusJets.W22

end

end SiegelZeros

end RiemannHypothesis.Family003
