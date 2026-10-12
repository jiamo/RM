/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/LowCentralGeometry.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.LowNominalGeometry
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod₀
      (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1<Z) (hT : 0<T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1<Z) (hT : 0<T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤T) (hhi : T≤Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0<Z)
    (hlo : Z^(-ε/2)≤T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤Z^(ε/2)) :
    Z^(1+ell-ε/2)≤T ∧ T≤Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert (preTransparency := .instances) hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert (preTransparency := .instances) hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
