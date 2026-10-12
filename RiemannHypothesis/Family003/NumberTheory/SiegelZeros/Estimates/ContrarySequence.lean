/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Estimates/ContrarySequence.lean
  Original module: OAI.NumberTheory.SiegelZeros.Estimates.ContrarySequence
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace WeightedTorusJets.W02

theorem exists_contrary_sequence {A : Type*} (admissible : A → Prop)
    (conductor : A → ℕ) (gap : A → ℝ)
    (positiveGap : ∀ x, admissible x → 0 < gap x)
    (boundedGap : ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x, admissible x → conductor x ≤ Q → c ≤ gap x)
    (failure : ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, admissible x → c ≤ gap x) :
    ∃ x : ℕ → A, (∀ n, admissible (x n)) ∧
      (∀ n, n < conductor (x n)) ∧
      (∀ n, 0 < gap (x n) ∧ gap (x n) < 1 / ((n : ℝ) + 1)) ∧
      Filter.Tendsto (fun n ↦ conductor (x n)) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n ↦ gap (x n)) Filter.atTop (nhds 0) := by
  classical
  have small : ∀ c : ℝ, 0 < c → ∃ x, admissible x ∧ gap x < c := by
    intro c hc
    by_contra h
    push Not at h
    exact failure ⟨c, hc, fun x hx ↦ h x hx⟩
  have chooseOne : ∀ n : ℕ, ∃ x, admissible x ∧ n < conductor x ∧
      0 < gap x ∧ gap x < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨c, hc, hbound⟩ := boundedGap n
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨x, hx, hsmall⟩ := small (min c (1 / ((n : ℝ) + 1))) (lt_min_iff.mpr ⟨hc, hn⟩)
    refine ⟨x, hx, ?_, positiveGap x hx, lt_of_lt_of_le hsmall (min_le_right _ _)⟩
    by_contra h
    have hb := hbound x hx (Nat.le_of_not_gt h)
    have hlt := lt_of_lt_of_le hsmall (min_le_left c (1 / ((n : ℝ) + 1)))
    exact (not_lt_of_ge hb) hlt
  choose x hx hcond hpos hsmall using chooseOne
  refine ⟨x, hx, hcond, fun n ↦ ⟨hpos n, hsmall n⟩, ?_, ?_⟩
  · exact Filter.tendsto_atTop_mono (fun n ↦ (hcond n).le) Filter.tendsto_id
  · exact squeeze_zero (fun n ↦ (hpos n).le) (fun n ↦ (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

end WeightedTorusJets.W02


end SiegelZeros

end RiemannHypothesis.Family003
