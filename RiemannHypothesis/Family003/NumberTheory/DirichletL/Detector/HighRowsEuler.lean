/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighRowsEuler.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsEuler
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsMultiplicative
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

@[simp] theorem bareIdealHighCoefficient_row_one (η : HeckeFamily.Character) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : HeckeFamily.Character) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
