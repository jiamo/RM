/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalRankPuncture.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankPuncture
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CanonicalCompleteRankNormalized

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseTerminalWidths
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1<Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) :=by
  have hi:(Ideal.span {m}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm
  have hn:0<(Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ):=actual_ideal_norm_pos _ hi
  have hle:Ideal.absNorm (Ideal.span {m}:Ideal O).radical≤Ideal.absNorm (Ideal.span {m}:Ideal O):=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0<Z) (ne_of_gt hZ) hn]
  exact_mod_cast hle

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
