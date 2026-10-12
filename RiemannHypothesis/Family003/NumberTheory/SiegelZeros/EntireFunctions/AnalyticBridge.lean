/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/AnalyticBridge.lean
  Original module: OAI.NumberTheory.SiegelZeros.EntireFunctions.AnalyticBridge
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace WeightedTorusJets.W05

theorem twisted_mangoldt_eq_logDerivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv χ.LFunction s / χ.LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

theorem combined_mangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  change LSeriesSummable
    ((fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) +
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))) s
  apply LSeriesSummable.add
  · exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  · exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

theorem combined_mangoldt_eq_logDerivatives {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s +
      -deriv χ.LFunction s / χ.LFunction s := by
  calc
    _ = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s +
        LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
      exact LSeries_add
        (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (g := fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
        (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
    _ = _ := congrArg₂ (fun x y : ℂ => x + y)
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)
      (twisted_mangoldt_eq_logDerivative χ hs)

end WeightedTorusJets.W05

end

end SiegelZeros

end RiemannHypothesis.Family003
