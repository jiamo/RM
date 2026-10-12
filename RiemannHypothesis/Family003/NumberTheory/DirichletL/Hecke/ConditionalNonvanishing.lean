/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/ConditionalNonvanishing.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.ConditionalNonvanishing
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands

namespace RiemannHypothesis.Family003

/-! The seven-eighths Hecke nonvanishing theorem from certified moment estimates. -/

namespace SevenEighths.HeckeFamily

theorem LFunction_ne_zero_of_certified_bands
    (h : ProbeFinalAssemblyCertifiedBands.DetectorCertifiedBands)
    (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 := by
  apply ProbeFinalAssembly.hecke_of_chosen_moments
    (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified h) χ s hs
  by_cases hs1 : s = 1
  · exact Or.inr (fun hχ => hpole ⟨hχ, hs1⟩)
  · exact Or.inl hs1

end SevenEighths.HeckeFamily

end RiemannHypothesis.Family003
