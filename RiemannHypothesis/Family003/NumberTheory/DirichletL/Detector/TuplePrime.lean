/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/TuplePrime.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.TuplePrime
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.TupleRows
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.CompensationActual

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma span_tupleProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    Ideal.span {∏i∈J,p i}=∏i∈J,Ideal.span {p i} := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Ideal.span_singleton_one,Ideal.one_eq_top]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,←Ideal.span_singleton_mul_span_singleton,ih,Finset.prod_insert hi]

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

theorem indexedCompensatedHigh_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hs : ∀i,Supported (P i).val)
    (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      spectralCompensatedHigh S (Finset.univ.image P) η x w z
        (fun Q=>star (HeckeFamily.idealCoeff η Q.val)*(Ideal.absNorm Q.val:ℂ)^x)
        (fun Q=>(Ideal.absNorm Q.val:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedHigh
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : HeckeFamily.elementCoeff η (primaryGenerator (P i).val)=
      HeckeFamily.idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
