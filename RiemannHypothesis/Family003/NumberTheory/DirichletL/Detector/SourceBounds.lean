/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/SourceBounds.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.SourceBounds
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SourceCoefficient
import RiemannHypothesis.Family003.NumberTheory.DirichletL.CubicSieve.GaussNorm

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
