/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SourceInputFirstTailScale.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstScale
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end RiemannHypothesis.Family003
