/-
# The heat flow behind the de Bruijn–Newman constant

`RiemannHypothesis/DeBruijnNewman.lean` builds the family

  `H t (z) = ∫_0^∞ e^{t u²} Φ(u) cos(u z) du`

and shows that each `H t` is entire, even and conjugate-symmetric;
`RiemannHypothesis/FourierXi.lean` identifies the initial datum, `H 0 (z) = ξ(z/2)/8`, and
so turns the Riemann hypothesis into the statement that every zero of `H 0` is real.

This file supplies the two things that were missing on that side of the ledger.

* **The flow.**  `H` solves the *backward* heat equation `∂_t H = −∂_z² H`
  (`dbnH_backward_heat_equation`).  This is what makes `t` a time parameter at all: the family
  is obtained from `H 0` by running the heat equation *backwards*, which is exactly why
  `t < 0` may create complex zeros and `t > 0` may not.  Both derivatives are obtained by
  differentiating under the integral sign against the dominating function already used for
  the analyticity of `H t`.

* **The order structure of `Λ`.**  `dbnRealSet` is the set of times at which every zero of
  `H t` is real, and `dbnLambda = sInf dbnRealSet`.  We record the elementary `sInf` API
  (`dbnLambda_le_of_mem`, `le_dbnLambda_of_lowerBound`), the translation of the Riemann
  hypothesis into membership of `0` (`zetaForm_iff_zero_mem_dbnRealSet`), and the derivation
  of `DeBruijnNewmanEquivRH` from de Bruijn's structural theorem that `dbnRealSet` is the ray
  `[Λ, ∞)` (`deBruijnNewmanEquivRH_of_realSet_eq_Ici`).  De Bruijn's theorem itself is *not*
  proved here; it is isolated as the single hypothesis the equivalence needs.

Nothing here proves the Riemann hypothesis, and nothing here proves `Λ ≥ 0`
(Rodgers–Tao); those remain the `DeBruijnNewmanEquivRH` and `DeBruijnNewmanNonnegative`
statements of `DeBruijnNewman.lean`.
-/
import RiemannHypothesis.FourierXi

noncomputable section

open Set MeasureTheory Filter Complex
open scoped Topology Real

namespace RiemannHypothesis

/-! ## A dominating function carrying two extra powers of `u`

Differentiating `dbnKernel` once in `z` costs a factor `u`, and differentiating in `t` or
twice in `z` costs `u²`.  Since `u² ≤ e^{2u}` for `u ≥ 0`, the cost is absorbed by moving the
linear coefficient of the existing majorant from `9 + ‖z‖` to `11 + ‖z‖`, which keeps the
majorant in the integrable family `exp (a u² + b u − 2 u³)`.
-/

lemma sq_le_exp_two_mul {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ Real.exp (2 * u) := by
  have h : 1 + (2 * u) + (2 * u) ^ 2 / 2 ≤ Real.exp (2 * u) :=
    Real.quadratic_le_exp_of_nonneg (by linarith)
  nlinarith [hu]

/-- The second-order integrand `u² e^{t u²} Φ(u) cos(u z)`, which is both `∂_t` of
`dbnKernel` and `−∂_z²` of it. -/
def dbnKernelSq (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((u : ℂ) ^ 2) * dbnKernel t z u

lemma norm_dbnKernelSq_le (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖dbnKernelSq t z u‖ ≤ dbnConst * Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3) := by
  have hnorm : ‖dbnKernelSq t z u‖ = u ^ 2 * ‖dbnKernel t z u‖ := by
    rw [dbnKernelSq, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  rw [hnorm]
  have hk := norm_dbnKernel_le t z hu
  have hsq := sq_le_exp_two_mul hu
  have hstep : u ^ 2 * ‖dbnKernel t z u‖ ≤
      Real.exp (2 * u) * (dbnConst * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3)) := by
    refine mul_le_mul hsq hk (norm_nonneg _) (Real.exp_pos _).le
  refine hstep.trans_eq ?_
  rw [show Real.exp (2 * u) * (dbnConst * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3)) =
      dbnConst * (Real.exp (2 * u) * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3)) by ring]
  rw [← Real.exp_add]
  ring_nf

lemma continuousOn_dbnKernelSq (t : ℝ) (z : ℂ) : ContinuousOn (dbnKernelSq t z) (Ioi 0) :=
  (Continuous.continuousOn (by fun_prop)).mul (continuousOn_dbnKernel t z)

lemma integrableOn_dbnKernelSq (t : ℝ) (z : ℂ) : IntegrableOn (dbnKernelSq t z) (Ioi 0) := by
  refine Integrable.mono'
    ((integrableOn_exp_quadratic_sub_cube t (11 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul
      dbnConst)
    ((continuousOn_dbnKernelSq t z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_dbnKernelSq_le t z (le_of_lt hu)

/-! ## The time derivative -/

lemma hasDerivAt_dbnKernel_time (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun s : ℝ => dbnKernel s z u) (dbnKernelSq t z u) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * u ^ 2) (u ^ 2) t := by
    simpa using (hasDerivAt_id t).mul_const (u ^ 2)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2) * dbnPhi u)
      (u ^ 2 * Real.exp (t * u ^ 2) * dbnPhi u) t := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (h1.exp.mul_const (dbnPhi u))
  have h3 := (h2.ofReal_comp).mul_const (Complex.cos ((u : ℂ) * z))
  refine h3.congr_deriv ?_
  simp only [dbnKernelSq, dbnKernel]
  push_cast
  ring

/-- **Differentiation under the integral sign in the time variable.** -/
theorem hasDerivAt_dbnH_time (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => dbnH s z) (∫ u in Ioi (0 : ℝ), dbnKernelSq t z u) t := by
  have hball : Metric.ball t 1 ∈ 𝓝 t := Metric.ball_mem_nhds t one_pos
  have hbound_int : Integrable
      (fun u : ℝ => dbnConst * Real.exp ((t + 1) * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_quadratic_sub_cube (t + 1) (11 + ‖z‖)
      (by norm_num : (0:ℝ) < 2)).const_mul dbnConst
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun s u => dbnKernel s z u)
    (F' := fun s u => dbnKernelSq s z u)
    (bound := fun u => dbnConst * Real.exp ((t + 1) * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
    (s := Metric.ball t 1) (x₀ := t) hball
    (Eventually.of_forall fun s =>
      (continuousOn_dbnKernel s z).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_dbnKernel t z)
    ((continuousOn_dbnKernelSq t z).aestronglyMeasurable measurableSet_Ioi)
    ?_ hbound_int ?_
  · exact hmain.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro s hs
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have hs' : s ≤ t + 1 := by
      have := Metric.mem_ball.mp hs
      rw [Real.dist_eq] at this
      have := abs_lt.mp this
      linarith [this.2]
    refine (norm_dbnKernelSq_le s z hu0).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) dbnConst_nonneg
    nlinarith [sq_nonneg u, hs']
  · filter_upwards with u
    intro s _
    exact hasDerivAt_dbnKernel_time s z u

/-! ## The first and second derivatives in `z` -/

/-- **Differentiation under the integral sign in the space variable.** -/
theorem hasDerivAt_dbnH_space (t : ℝ) (z : ℂ) :
    HasDerivAt (dbnH t) (∫ u in Ioi (0 : ℝ), dbnKernelDeriv t z u) z := by
  have hball : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hbound_int : Integrable
      (fun u : ℝ => dbnConst * Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_quadratic_sub_cube t (11 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul
      dbnConst
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun w u => dbnKernel t w u)
    (F' := fun w u => dbnKernelDeriv t w u)
    (bound := fun u => dbnConst * Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
    (s := Metric.ball z 1) (x₀ := z) hball
    (Eventually.of_forall fun w =>
      (continuousOn_dbnKernel t w).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_dbnKernel t z)
    ((continuousOn_dbnKernelDeriv t z).aestronglyMeasurable measurableSet_Ioi)
    ?_ hbound_int ?_
  · exact hmain.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := Metric.mem_ball.mp hw
      rw [Complex.dist_eq] at this
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    refine (norm_dbnKernelDeriv_le t w hu0).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) dbnConst_nonneg
    nlinarith [hu0, hw']
  · filter_upwards with u
    intro w _
    exact hasDerivAt_dbnKernel t w u

lemma deriv_dbnH (t : ℝ) (z : ℂ) :
    deriv (dbnH t) z = ∫ u in Ioi (0 : ℝ), dbnKernelDeriv t z u :=
  (hasDerivAt_dbnH_space t z).deriv

lemma deriv_dbnH_eq (t : ℝ) :
    deriv (dbnH t) = fun z => ∫ u in Ioi (0 : ℝ), dbnKernelDeriv t z u :=
  funext (deriv_dbnH t)

lemma integrableOn_dbnKernelDeriv (t : ℝ) (z : ℂ) :
    IntegrableOn (dbnKernelDeriv t z) (Ioi 0) := by
  refine Integrable.mono'
    ((integrableOn_exp_quadratic_sub_cube t (10 + ‖z‖)
      (by norm_num : (0:ℝ) < 2)).const_mul dbnConst)
    ((continuousOn_dbnKernelDeriv t z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_dbnKernelDeriv_le t z (le_of_lt hu)

lemma hasDerivAt_dbnKernelDeriv (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => dbnKernelDeriv t w u) (-dbnKernelSq t z u) z := by
  have h : HasDerivAt (fun w : ℂ => (u : ℂ) * w) (u : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (u : ℂ)
  have h2 := (((h.csin).neg.mul_const (u : ℂ)).const_mul
    (((Real.exp (t * u ^ 2) * dbnPhi u : ℝ) : ℂ)))
  refine h2.congr_deriv ?_
  simp only [dbnKernelSq, dbnKernel]
  ring

/-- **The second derivative of `H t`.**  Differentiating twice in `z` brings down `−u²`. -/
theorem hasDerivAt_deriv_dbnH (t : ℝ) (z : ℂ) :
    HasDerivAt (deriv (dbnH t)) (-∫ u in Ioi (0 : ℝ), dbnKernelSq t z u) z := by
  have hball : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hbound_int : Integrable
      (fun u : ℝ => dbnConst * Real.exp (t * u ^ 2 + (12 + ‖z‖) * u - 2 * u ^ 3))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_quadratic_sub_cube t (12 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul
      dbnConst
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun w u => dbnKernelDeriv t w u)
    (F' := fun w u => -dbnKernelSq t w u)
    (bound := fun u => dbnConst * Real.exp (t * u ^ 2 + (12 + ‖z‖) * u - 2 * u ^ 3))
    (s := Metric.ball z 1) (x₀ := z) hball
    (Eventually.of_forall fun w =>
      (continuousOn_dbnKernelDeriv t w).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_dbnKernelDeriv t z)
    (((continuousOn_dbnKernelSq t z).neg).aestronglyMeasurable measurableSet_Ioi)
    ?_ hbound_int ?_
  · rw [deriv_dbnH_eq t]
    refine hmain.2.congr_deriv ?_
    rw [MeasureTheory.integral_neg]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := Metric.mem_ball.mp hw
      rw [Complex.dist_eq] at this
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    rw [norm_neg]
    refine (norm_dbnKernelSq_le t w hu0).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) dbnConst_nonneg
    nlinarith [hu0, hw']
  · filter_upwards with u
    intro w _
    exact hasDerivAt_dbnKernelDeriv t w u

lemma deriv_deriv_dbnH (t : ℝ) (z : ℂ) :
    deriv (deriv (dbnH t)) z = -∫ u in Ioi (0 : ℝ), dbnKernelSq t z u :=
  (hasDerivAt_deriv_dbnH t z).deriv

/-- **The de Bruijn–Newman family solves the backward heat equation** `∂_t H = −∂_z² H`.

This is the whole content of the parameter `t`: `H t` is the *backward* heat evolution of
`H 0 = ξ(·/2)/8`.  Running time forwards (`t > 0`) is the smoothing direction, in which zeros
may only become more real; running it backwards (`t < 0`) is the direction in which pairs of
real zeros may collide and leave the real axis.  `Λ` is the time at which the last such
collision happens. -/
theorem dbnH_backward_heat_equation (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => dbnH s z) (-deriv (deriv (dbnH t)) z) t := by
  rw [deriv_deriv_dbnH t z, neg_neg]
  exact hasDerivAt_dbnH_time t z

/-! ## Reality on the real axis, and the symmetry of the zero set -/

/-- `H t` is real-valued on the real axis. -/
theorem dbnH_ofReal_im (t x : ℝ) : (dbnH t (x : ℂ)).im = 0 := by
  have h := dbnH_conj t (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have h2 : (dbnH t (x : ℂ)).im = -(dbnH t (x : ℂ)).im := by
    simpa using congrArg Complex.im h
  linarith

/-- The zeros of `H t` are invariant under `z ↦ -z`. -/
theorem dbnH_neg_eq_zero {t : ℝ} {z : ℂ} (hz : dbnH t z = 0) : dbnH t (-z) = 0 := by
  rw [dbnH_neg]; exact hz

/-- The zeros of `H t` come in quadruples `{z, -z, conj z, -conj z}`: they are symmetric in
both axes.  Hence a zero is forced to be real exactly when it is not one of a genuine
quadruple, which is why "all zeros of `H t` are real" is the natural analogue of the Riemann
hypothesis for the whole family. -/
theorem dbnH_zero_quadruple {t : ℝ} {z : ℂ} (hz : dbnH t z = 0) :
    dbnH t (-z) = 0 ∧ dbnH t ((starRingEnd ℂ) z) = 0 ∧
      dbnH t (-(starRingEnd ℂ) z) = 0 := by
  refine ⟨dbnH_neg_eq_zero hz, dbnH_conj_eq_zero t hz, ?_⟩
  exact dbnH_neg_eq_zero (dbnH_conj_eq_zero t hz)

/-! ## The order structure of `Λ` -/

/-- The set of times at which every zero of `H t` is real.  By definition
`dbnLambda = sInf dbnRealSet`. -/
def dbnRealSet : Set ℝ := {t : ℝ | ∀ z : ℂ, dbnH t z = 0 → z.im = 0}

lemma dbnLambda_eq_sInf : dbnLambda = sInf dbnRealSet := rfl

lemma mem_dbnRealSet_iff {t : ℝ} :
    t ∈ dbnRealSet ↔ ∀ z : ℂ, dbnH t z = 0 → z.im = 0 := Iff.rfl

/-- **The Riemann hypothesis is the statement that `0` is one of the reality times.**
This is `FourierXi.zeta_iff_dbnH_zero` restated in the language of `dbnRealSet`. -/
theorem zetaForm_iff_zero_mem_dbnRealSet : ZetaForm ↔ (0 : ℝ) ∈ dbnRealSet :=
  zeta_iff_dbnH_zero

/-- If the reality set is bounded below, any of its elements bounds `Λ` from above. -/
theorem dbnLambda_le_of_mem (hbdd : BddBelow dbnRealSet) {t : ℝ} (ht : t ∈ dbnRealSet) :
    dbnLambda ≤ t :=
  csInf_le hbdd ht

/-- Any lower bound of the reality set is at most `Λ`, provided the set is nonempty. -/
theorem le_dbnLambda_of_lowerBound (hne : dbnRealSet.Nonempty) {c : ℝ}
    (hc : ∀ t ∈ dbnRealSet, c ≤ t) : c ≤ dbnLambda :=
  le_csInf hne hc

/-- **The de Bruijn–Newman equivalence, reduced to de Bruijn's structural theorem.**

De Bruijn (1950) and Newman (1976) show that the reality set is a closed ray: there is a
time `Λ` before which some zero is complex and after which all zeros are real, and the ray
contains its endpoint.  Granting exactly that — `dbnRealSet = Ici dbnLambda` — the Riemann
hypothesis becomes the inequality `Λ ≤ 0`.

The proof is the one-line consequence of `zetaForm_iff_zero_mem_dbnRealSet`; the mathematical
content sits entirely in the hypothesis, which is not proved in this repository. -/
theorem deBruijnNewmanEquivRH_of_realSet_eq_Ici (h : dbnRealSet = Ici dbnLambda) :
    DeBruijnNewmanEquivRH := by
  rw [DeBruijnNewmanEquivRH, zetaForm_iff_zero_mem_dbnRealSet, h]
  exact mem_Ici

/-- The half of the de Bruijn–Newman equivalence that needs only upward-closedness together
with boundedness below: if all zeros of `H 0` are real, then `Λ ≤ 0`. -/
theorem dbnLambda_le_zero_of_zetaForm (hbdd : BddBelow dbnRealSet) (h : ZetaForm) :
    dbnLambda ≤ 0 :=
  dbnLambda_le_of_mem hbdd (zetaForm_iff_zero_mem_dbnRealSet.mp h)

/-- **Rodgers–Tao plus de Bruijn turn the Riemann hypothesis into an equality.**
Granting de Bruijn's ray structure and the Rodgers–Tao bound `0 ≤ Λ`, the conjecture is
`Λ = 0` rather than an inequality. -/
theorem zetaForm_iff_dbnLambda_eq_zero (h : dbnRealSet = Ici dbnLambda)
    (hRT : DeBruijnNewmanNonnegative) : ZetaForm ↔ dbnLambda = 0 := by
  have hiff : ZetaForm ↔ dbnLambda ≤ 0 := deBruijnNewmanEquivRH_of_realSet_eq_Ici h
  rw [hiff]
  exact ⟨fun hle => le_antisymm hle hRT, fun heq => heq.le⟩

end RiemannHypothesis

end
