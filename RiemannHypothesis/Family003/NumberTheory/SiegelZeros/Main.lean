/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Main.lean
  Original module: OAI.NumberTheory.SiegelZeros.Main
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Characters.BiquadraticBasisGroupTransport
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Characters.DirichletRealZeroBoundProof
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Characters.NormLogDerivLFunctionNegLogDerivZeta
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Characters.SumCharacterPeriodZero
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Conclusions.Theorem
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Determinants.Divisibility
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Differentials.FractionEulerDerivation
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.EntireFunctions.ClosureSpecMapZeroLocus
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.EntireFunctions.CompletedLAnalyticOrderNeTop
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicFormLemma
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.EntireFunctions.TorusJetZeroSchemeInclusion
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Hilbert.NormalizedHomogeneousChartEquation
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Intersection.TorusImmersionGenericPointFormallySmooth
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Intersection.TorusIntoProj
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.DegreeSliceQuotientEquiv
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.LocalAlgebra.FractionEquivAlgebra
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Selection.GlobalPivotValuationExponent
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Selection.PivotBounds
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.MapIInfPrimesOver
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.RectangularGradedPieceGeneratedByDegreeOne
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.SumCardFilterSumMin

