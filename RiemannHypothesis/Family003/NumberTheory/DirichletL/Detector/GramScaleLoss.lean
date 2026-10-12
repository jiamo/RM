/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramScaleLoss.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramScaleLoss
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramInfiniteEstimate

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_scale_identity (M P Y δ : ℝ) (hM : 0<M) (hP : 0<P) (hY : 0<Y) :
    P*(Y/(M*P))^(-1+δ)=M^(1-δ)*P^(2-δ)*Y^(-1+δ) := by
  rw [Real.div_rpow hY.le (mul_pos hM hP).le,Real.mul_rpow hM.le hP.le,div_eq_mul_inv,mul_inv_rev,
    ←Real.rpow_neg hM.le,←Real.rpow_neg hP.le]
  have he : P*P^(-(-1+δ))=P^(2-δ) := by
    conv_lhs => lhs;rw [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
    congr 1
    ring
  calc
    _=M^(1-δ)*(P*P^(-(-1+δ)))*Y^(-1+δ) := by rw [show -(-1+δ)=1-δ by ring];ring
    _=_ := by rw [he]

lemma nonexceptional_scale_loss (M P Y δ : ℝ) (hM : 1≤M) (hP : 1≤P) (hY : 0<Y)
    (hδ : 0≤δ) :
    P*(Y/(M*P))^(-1+δ)≤M*(P^2/Y)*Y^δ := by
  have hm : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hp : 0<P := lt_of_lt_of_le zero_lt_one hP
  rw [nonexceptional_scale_identity M P Y δ hm hp hY]
  have hmp : M^(1-δ)≤M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM (show 1-δ≤1 by linarith)
  have hpp : P^(2-δ)≤P^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hP (show 2-δ≤2 by linarith)
  calc
    _≤M*P^2*Y^(-1+δ) := mul_le_mul_of_nonneg_right
      (mul_le_mul hmp hpp (by positivity) hm.le) (by positivity)
    _=_ := by rw [Real.rpow_add hY,Real.rpow_neg_one];ring

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
