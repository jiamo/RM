/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighEuler.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighEuler
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighValuations
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.EulerFinsupp
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.IdealLocalEuler
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right hn,zero_mul]

theorem highValuationTerm_tsum_eq (η : HeckeFamily.Character) (x w z : ℂ) :
    (∑'v : PrimeIdeal→₀HighValuation,highValuationTerm η x w z v)=
      bareIdealHighSeries η 1 x w z := by
  unfold highValuationTerm bareIdealHighSeries
  apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
    bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  intro a ha
  have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
  let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
    ((⟨a.1.1,hs.2.1.1⟩,⟨a.1.2,hs.2.2.1.1⟩),
      (⟨a.2.1,hs.2.2.2.1.1⟩,⟨a.2.2,hs.2.2.2.2.1⟩))
  refine ⟨highValuationEquiv b,?_⟩
  rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]

theorem bareIdealHighSeries_hasProd (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,highPrimeTerm η x w z P b)
      (bareIdealHighSeries η 1 x w z) := by
  have hs := highValuationTerm_summable_norm η x w z hx hw hz
  simp only [highValuationTerm_eq_prod] at hs
  have he := ProbeEulerFinsupp.hasProd_of_summable (highPrimeTerm η x w z)
    (highPrimeTerm_zero η x w z) hs
  simpa only [←highValuationTerm_eq_prod,highValuationTerm_tsum_eq] using he

theorem bareIdealHighSeries_eq_tprod (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    bareIdealHighSeries η 1 x w z =
      ∏' P : PrimeIdeal,∑' b : HighValuation,highPrimeTerm η x w z P b :=
  (bareIdealHighSeries_hasProd η x w z hx hw hz).tprod_eq.symm

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
