/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/CubeCalibration.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily

end

end RiemannHypothesis.Family003
