/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/KernelBaseline.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.KernelBaseline
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.KernelActual

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem mixedReflectedValue_eq_actualKernelSource (F : PrimeFamily φ)
    (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s (F.reflected K hK S).generator_ne_zero hc
      (F.reflected K hK S).generator_good (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ) W X =
    fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i)*
      ∑' t : ThetaFullIndex,
        actualKernelSourceTerm F K hK S jF D s hc t.1 t.2.1 t.2.2.1.val t.2.2.2.val
          (fun _ _ => 1) 1 1 1 1 W 0 X := by
  unfold mixedReflectedValue
  congr 1
  apply tsum_congr
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t) =
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  have hW : CompletedHeight.normTwistedSource W 0 = W := by
    funext x
    simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]
  unfold actualKernelSourceTerm actualMixedCoefficient
  rw [hx,hW]
  simp only [Finset.prod_const_one,one_div]
  ring

end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
