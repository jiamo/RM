/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/Compensation.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.Compensation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompensation

def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))

theorem tupleOperation_zero {α : Type*} [CommMonoid α]
    (p : Fin 0 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z = F 1 X Y Z := by
  simp [tupleOperation, hq, hη]

theorem tupleOperation_one {α : Type*} [CommMonoid α]
    (p : Fin 1 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z =
      star (η (p 0)) * F (p 0) X Y (Z * q (p 0)) -
      ((q (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * F 1 (X / q (p 0)) (Y / q (p 0)) Z := by
  have hp : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  simp only [tupleOperation, hp]
  simp [hq, hη]
  ring

end SevenEighths.ProbeCompensation
end

end RiemannHypothesis.Family003
