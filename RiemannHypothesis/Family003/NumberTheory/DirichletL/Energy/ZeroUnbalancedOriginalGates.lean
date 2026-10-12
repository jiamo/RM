/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/ZeroUnbalancedOriginalGates.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalGates
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBranchGeometry

lemma original_long_positive (Z M X₁ X₂:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hpos:0<length Z X₂:=by linarith
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma raw_short_bound (Z M X:ℝ)(hZ:1<Z)(hX:0<X)
    (hshort:length Z X≤M/4):Real.logb Z X≤M/4:=by
  rw [length_eq_max_log Z X hZ hX] at hshort
  exact (le_max_right _ _).trans hshort

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates

end

end RiemannHypothesis.Family003
