/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/PhysicalCoefficientScaling.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficientScaling
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SpectralCoefficient
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.PhysicalNorms
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RadialIdentity

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0<X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := supportedElement_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (supportedElement_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have hh := congrArg (fun v : ℂ=>v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        star (FiniteGaussPhase.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert (preTransparency := .instances) hh using 1 <;> ring

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
