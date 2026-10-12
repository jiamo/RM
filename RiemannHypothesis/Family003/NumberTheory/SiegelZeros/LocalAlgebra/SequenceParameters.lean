/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/SequenceParameters.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.SequenceParameters
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Estimates.AsymptoticAssembly
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Estimates.GenuineSequence

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

open Filter
open scoped Topology

namespace WeightedTorusJets.W02

theorem genuine_sequence_eventually_ne {ι : Type*} {l : Filter ι}
    (z : ι → GenuineZero)
    (hq : Tendsto (fun i ↦ ((z i).q : ℕ)) l atTop) (B : ℕ) :
    ∀ᶠ i in l, ((z i).q : ℕ) ≠ B :=
  (hq.eventually_gt_atTop B).mono fun _ h ↦ ne_of_gt h

theorem genuine_contrary_sequence_with_parameters
    (failure : ¬ UniformSiegelZeroExclusion) (γ : ℝ) (hγ : 0 < γ) (H : ℕ) :
    ∃ z : ℕ → GenuineZero,
      (∀ n, n < ((z n).q : ℕ)) ∧
      (∀ n, 0 < (z n).gap ∧ (z n).gap < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ ((z n).q : ℕ)) atTop atTop ∧
      Tendsto (fun n ↦ (z n).gap) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ((z n).q : ℕ) ≠ 8) ∧
      (∀ᶠ n in atTop, H ≤ W48.auxiliaryN γ ((z n).q : ℝ)) ∧
      Tendsto (fun n ↦ ((z n).q : ℝ)) atTop atTop ∧
      Tendsto (fun n ↦ W48.auxiliaryN γ ((z n).q : ℝ)) atTop atTop ∧
      Tendsto (fun n ↦ W48.auxiliaryU γ ((z n).q : ℝ)) atTop atTop ∧
      Tendsto (fun n ↦ Real.log (W48.auxiliaryU γ ((z n).q : ℝ)) /
        Real.log ((z n).q : ℝ)) atTop (𝓝 (4 * γ / 3)) := by
  obtain ⟨z, hindex, hsmall, hq, hgap⟩ := genuine_contrary_sequence failure
  have hqR : Tendsto (fun n ↦ ((z n).q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  obtain ⟨hN, hU, hratio⟩ := W48.natural_conductor_limits hγ hq
  exact ⟨z, hindex, hsmall, hq, hgap,
    genuine_sequence_eventually_ne z hq 8,
    hN.eventually_ge_atTop H, hqR, hN, hU, hratio⟩

end WeightedTorusJets.W02

end

end SiegelZeros

end RiemannHypothesis.Family003
