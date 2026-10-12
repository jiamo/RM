/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/LowSlotWeights.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.LowSlotPolynomial
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

lemma lowSingleSlotWeight_height_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖=‖lowSingleSlotWeight η W P 0 a‖ := by
  simp only [lowSingleSlotWeight,norm_mul,logPhase_norm,mul_one]

lemma lowSelectedWeight_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤∏i : SelectedSlot J,‖W i.val (elementNorm (b i).val/P i.val)‖ := by
  rw [lowSelectedWeight_eq_product,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>lowSingleSlotWeight_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_height_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖=‖lowSelectedWeight η slots J W P 0 b‖ := by
  rw [lowSelectedWeight_eq_product,lowSelectedWeight_eq_product,norm_prod,norm_prod]
  exact Finset.prod_congr rfl (fun i _=>lowSingleSlotWeight_height_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (hW : ∀i x,‖W i x‖≤1) (t : ℝ) (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤1 :=
  (lowSelectedWeight_norm η slots J W P t b).trans
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
