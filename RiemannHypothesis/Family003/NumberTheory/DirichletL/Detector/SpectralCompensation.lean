/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/SpectralCompensation.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.SpectralCompensation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.MarkedProduct
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.MarkedRational
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

theorem spectralCompensatedHigh_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedIdealHighSeries_eq_product S hS (T\J)
    (fun P hP=>hT P (Finset.mem_sdiff.mp hP).1) η x w z hx hw hz]
  simp only [mul_div_assoc,Finset.prod_mul_distrib]
  ring

theorem spectralCompensatedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh_eq_product S hS T hT η x w z B q hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
