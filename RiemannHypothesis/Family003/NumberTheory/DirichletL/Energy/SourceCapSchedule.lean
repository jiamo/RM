/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/SourceCapSchedule.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.SourceCapSchedule
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.WidthRanges
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.FirstLiveAdmission

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.CenteredMomentEnergySourceCapSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyFirstLiveAdmission

lemma count_pos (M ε:ℝ):0<count M ε:=by
  unfold count CenteredMomentFirstSecondLossParameters.depth
  omega
lemma final_range_large (M B L ε:ℝ)(hM:0≤M)(hB:0≤B):
    20≤range M B L (count M ε):=by
  have hh:=range_mono M B L hM hB (show 1≤count M ε from count_pos M ε)
  have hm:1≤max 1 L:=le_max_left _ _
  simp only [range,step] at hh
  linarith
lemma readyBudget_le_schedule (M B L ε A P:ℝ)(hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L (count M ε)+M+1)(hP:P≤B):
    readyBudget A P≤finalSourceCap M B L ε:=by
  have hr:=final_range_large M B L ε hM hB
  unfold readyBudget finalSourceCap sourceCap
  linarith
lemma declared_capacity_le_schedule (M B L ε A:ℝ)(hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L (count M ε)):
    max M A≤finalSourceCap M B L ε:=by
  have hr:=final_range_large M B L ε hM hB
  apply max_le
  all_goals unfold finalSourceCap sourceCap;linarith

end SevenEighths.CenteredMomentEnergySourceCapSchedule

end

end RiemannHypothesis.Family003
