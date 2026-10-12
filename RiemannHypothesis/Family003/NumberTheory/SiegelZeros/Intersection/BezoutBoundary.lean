/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Intersection/BezoutBoundary.lean
  Original module: OAI.NumberTheory.SiegelZeros.Intersection.BezoutBoundary
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Estimates.GeometricBoundary

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.W50

open WeightedTorusJets

theorem uniform_exclusion_of_local_isolated_bezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ) :
    UniformSiegelZeroExclusion := by
  apply uniform_exclusion_of_actual_cutoff
  intro H N hH hHN _hN d a hd hd1 hd2 ha
  exact W28.actualCutoffSpanning_of_localBezout hBezout H N (by omega) hHN
    d hd hd1 hd2 a ha

end SiegelZerosAwei.W50

end

end SiegelZeros

end RiemannHypothesis.Family003
