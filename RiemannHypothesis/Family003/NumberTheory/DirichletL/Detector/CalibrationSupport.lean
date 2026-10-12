/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/CalibrationSupport.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.Calibration
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.PhysicalAnalytic

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

theorem source_rowCoefficient_apply (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    rowCoefficient η (calibrationForSet S hS).Xi s hs m a =
      HeckeFamily.elementCoeff η a * ((calibrationForSet S hS).Xi a)⁻¹ *
        sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  calibrated_rowCoefficient_apply η (calibrationForSet S hS) s hs m a ha
    (calibrationForSet_coprime_of_excluded S hS a hmask)

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
