/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailAggregate.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAggregate
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailSource

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialPhysicalMeasure

theorem original_source_norm_fibers
    {ι ρ : Type*} [DecidableEq ι]
    (S : Finset (Point ι)) (R : Finset ρ) (f : Point ι→ρ→ℂ) (b : ρ→ℝ)
    (hb : ∀k∈sourceKeys S,∀r∈R,
      ‖∑h∈sourceFrequencies S k,f (sourcePoint k h) r‖≤b r) :
    ‖∑x∈S,∑r∈R,f x r‖≤((sourceKeys S).card:ℝ)*(∑r∈R,b r) := by
  rw [source_sum_fibers]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k∈sourceKeys S,∑r∈R,b r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr=>hb k hk r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SevenEighths.InverseInitialHighFrequencyTail

end

end RiemannHypothesis.Family003
