/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean
  Original module: OAI.NumberTheory.DirichletL.Nonvanishing
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Foundation
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

namespace RiemannHypothesis.Family003

/-!
# Nonvanishing of Dirichlet L-functions to the right of seven eighths

The main result excludes zeros of Dirichlet L-functions in the half-plane
`7 / 8 < re s`, apart from the principal character's pole at `s = 1`.
The corresponding nonvanishing statement for the Riemann zeta function follows.
-/

namespace DirichletCharacter
open scoped _root_.DirichletCharacter

/-- Dirichlet L-functions do not vanish to the right of `7 / 8`, away from the
principal character's pole at `1`. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
    q (NeZero.ne q) χ s hs hpole

end DirichletCharacter

/-- The Riemann zeta function does not vanish to the right of `7 / 8`. -/
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero s hs

end RiemannHypothesis.Family003
