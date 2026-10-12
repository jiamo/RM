/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/InitialFubini.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.InitialFubini
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.InitialIntegral
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.InitialScales

namespace RiemannHypothesis.Family003

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem source_initial_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p : HeightSpace,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p : HeightSpace,initialHighOnLines S D η mask σ υ ξ i p*
        sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  exact initialHigh_integral_tsum_test S D η mask hm σ υ ξ hσ hυ hξ _
    (sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ σ ξ υ (by linarith))

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
