/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/LocalGap.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalGap
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Tactic

namespace RiemannHypothesis.Family003

namespace SiegelZeros


open Filter Topology

namespace WeightedTorusJets.W02

theorem fixed_level_nonvanishing_near_one (q : ℕ) [NeZero q] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ s : ℂ, dist s 1 < ε → χ.LFunction s ≠ 0 := by
  have he : ∀ χ : {χ : DirichletCharacter ℂ q // χ ≠ 1},
      ∀ᶠ s in nhds (1 : ℂ), χ.val.LFunction s ≠ 0 := by
    intro χ
    exact (χ.val.differentiableAt_LFunction 1 (Or.inr χ.property)).continuousAt.eventually_ne
      (DirichletCharacter.LFunction_apply_one_ne_zero χ.property)
  have hall : ∀ᶠ s in nhds (1 : ℂ),
      ∀ χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}, χ.val.LFunction s ≠ 0 :=
    Filter.eventually_all.mpr he
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨ε, hε, fun χ hχ s hs ↦ hball hs ⟨χ, hχ⟩⟩

theorem fixed_level_real_zero_gap (q : ℕ) [NeZero q] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, β < 1 → χ.LFunction (β : ℂ) = 0 → ε ≤ 1 - β := by
  obtain ⟨ε, hε, hne⟩ := fixed_level_nonvanishing_near_one q
  refine ⟨ε, hε, fun χ hχ β hβ hz ↦ ?_⟩
  by_contra h
  have hd : dist (β : ℂ) 1 < ε := by
    rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hβ)]
    linarith
  exact hne χ hχ β hd hz

end WeightedTorusJets.W02


end SiegelZeros

end RiemannHypothesis.Family003
