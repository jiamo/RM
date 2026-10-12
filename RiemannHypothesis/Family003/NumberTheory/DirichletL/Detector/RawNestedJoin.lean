/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/RawNestedJoin.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.RawNestedJoin
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RawRadialJoin
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.OuterIndex
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=>verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))

theorem nestedMellinPhysicalProbe_eq_raw (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) :
    nestedMellinPhysicalProbe η C D W0 W1 X Y Z ξ υ=
      rawNestedPhysicalProbe η C D W0 W1 X Y Z ξ υ := by
  unfold nestedMellinPhysicalProbe rawNestedPhysicalProbe
  rw [sourceOuter_tsum]
  apply tsum_congr
  intro K
  dsimp only
  simp_rw [rawPhysicalMellinTerm_radial_join,tsum_mul_left]
  apply congrArg (verticalIntegral υ)
  funext w
  unfold rawRadialOuterFactor
  simp only [fullIdealWeight,ite_eq_right K.property.1.1]
  unfold verticalIntegral
  simp_rw [mul_assoc,integral_const_mul]
  simp only [Complex.ofReal_natCast]
  ring_nf
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  ring_nf

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
