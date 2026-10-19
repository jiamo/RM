/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZetaStationaryPhase

/-!
# The integrals of the approximate functional equation: auxiliary bounds

Bounds on `I(a, b) = ∫_a^b u^(-1/2) e^{iΦ(u)} du`, `Φ(u) = ωu − t log u`, used by
`RiemannHypothesis.AFEProof` besides the stationary-phase evaluation of
`RiemannHypothesis.ZetaStationaryPhase`:

* `norm_mI_neg_add_boundary_le` — the reflected frequency `−ω` (no stationary point), to second
  order, remainder `≤ 2/(ω² a^{3/2})`;
* `norm_mI_le_of_near` — near the stationary point (second-derivative test on `[a, 2a]` with the
  weight `u^(-1/2)`, first-derivative test on `[2a, b]`): `‖I(a, b)‖ ≤ 24 √a/√t + 2 h(2a)`.

Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RiemannHypothesis

namespace ZetaMellinPhase

open VanDerCorput Oscillatory

theorem rpow_neg_five_halves {u : ℝ} (hu : 0 < u) : u ^ (-(5 / 2 : ℝ)) = 1 / (u ^ 2 * Real.sqrt u) := by
  rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow, one_div]
  congr 1
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_natCast]

theorem abs_ampK_neg_le {t ω u : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) (hu : 0 < u) :
    |ampK t (-ω) u| ≤ 1 / (2 * ω ^ 2 * (u * Real.sqrt u)) := by
  unfold ampK
  have hs := Real.sqrt_pos.mpr hu
  have hs2 := Real.mul_self_sqrt hu.le
  have hp : 0 < ω * u + t := by positivity
  have e1 : -ω * u - t = -(ω * u + t) := by ring
  rw [e1, abs_div, abs_neg, abs_mul, abs_of_pos hs, neg_pow, abs_mul,
    show ((-1 : ℝ) ^ 3) = -1 by norm_num, abs_mul, abs_neg, abs_one, one_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (pow_pos hp 3),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |-ω * u + t| ≤ ω * u + t := by
    rw [abs_le]; constructor <;> nlinarith
  have hωu : ω * u ≤ ω * u + t := by linarith
  -- √u |t-ωu| · 2ω²u√u ≤ √u(ωu+t) · 2ω²u√u = 2 u (ωu)² (ωu+t)... ≤ 2 (ωu+t)³ · ...
  have key : Real.sqrt u * |-ω * u + t| * (2 * ω ^ 2 * (u * Real.sqrt u))
      ≤ 2 * (ω * u + t) ^ 3 := by
    have e : Real.sqrt u * |-ω * u + t| * (2 * ω ^ 2 * (u * Real.sqrt u))
        = 2 * (Real.sqrt u * Real.sqrt u) * u * ω ^ 2 * |-ω * u + t| := by ring
    rw [e, hs2]
    have : 2 * u * u * ω ^ 2 * |-ω * u + t| ≤ 2 * (ω * u) ^ 2 * (ω * u + t) := by
      have : 2 * u * u * ω ^ 2 = 2 * (ω * u) ^ 2 := by ring
      rw [this]; gcongr
    have h3 : (ω * u) ^ 2 ≤ (ω * u + t) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [sq_nonneg (ω * u + t)]
  linarith

theorem abs_ampK'_neg_le {t ω u : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) (hu : 0 < u) :
    |ampK' t (-ω) u| ≤ u ^ (-(5 / 2 : ℝ)) / ω ^ 2 := by
  rw [rpow_neg_five_halves hu]
  unfold ampK'
  have hs := Real.sqrt_pos.mpr hu
  have hp : 0 < ω * u + t := by positivity
  have e1 : (-ω * u - t) ^ 4 = (ω * u + t) ^ 4 := by ring
  rw [e1, abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.sqrt u * (ω * u + t) ^ 4)]
  have hnum : |3 * (-ω) ^ 2 * u ^ 2 + 8 * -ω * u * t + t ^ 2| ≤ 4 * (ω * u + t) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (mul_nonneg hω.le hu.le) ht]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc |3 * (-ω) ^ 2 * u ^ 2 + 8 * -ω * u * t + t ^ 2| * ω ^ 2
      ≤ 4 * (ω * u + t) ^ 2 * ω ^ 2 := by gcongr
    _ ≤ 1 / (u ^ 2 * Real.sqrt u) * (4 * Real.sqrt u * (ω * u + t) ^ 4) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        have h3 : (ω * u) ^ 2 ≤ (ω * u + t) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        have : 4 * (ω * u + t) ^ 2 * ω ^ 2 * (u ^ 2 * Real.sqrt u)
            = 4 * Real.sqrt u * (ω * u + t) ^ 2 * (ω * u) ^ 2 := by ring
        rw [this]
        have h4 := mul_le_mul_of_nonneg_left h3
          (by positivity : (0:ℝ) ≤ 4 * Real.sqrt u * (ω * u + t) ^ 2)
        nlinarith [h4]

theorem integral_rpow_neg_five_halves_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, u ^ (-(5 / 2 : ℝ)) ≤ 2 / 3 * (1 / (a * Real.sqrt a)) := by
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith⟩)]
  have hb : 0 < b := by linarith
  have e : -(5 / 2 : ℝ) + 1 = -(3 / 2) := by norm_num
  rw [e]
  have hbpos : 0 ≤ b ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hb.le _
  have ha' : a ^ (-(3 / 2 : ℝ)) = 1 / (a * Real.sqrt a) := by
    rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one]
  rw [ha']
  have : (b ^ (-(3 / 2 : ℝ)) - 1 / (a * Real.sqrt a)) / -(3 / 2) 
      = 2 / 3 * (1 / (a * Real.sqrt a)) - 2 / 3 * b ^ (-(3 / 2 : ℝ)) := by ring
  rw [this]
  linarith

/-- The reflected integral `∫_a^b u^(-s) e^{-iωu} du` (no stationary point), to second order:
the remainder is at most `2/(ω² a^{3/2})`. -/
theorem norm_mI_neg_add_boundary_le {t ω a b : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) (ha : 0 < a)
    (hab : a ≤ b) :
    ‖mI t (-ω) a b + I * (bdry t (-ω) b - bdry t (-ω) a)‖ ≤ 2 / (ω ^ 2 * (a * Real.sqrt a)) := by
  have hne : ∀ u ∈ Icc a b, -ω * u - t ≠ 0 := by
    intro u hu
    have : 0 < ω * u := mul_pos hω (lt_of_lt_of_le ha hu.1)
    linarith
  refine (norm_integral_add_boundary_le_of_ne ha hab hne).trans ?_
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 := abs_ampK_neg_le ht hω ha
  have h2 : |ampK t (-ω) b| ≤ 1 / (2 * ω ^ 2 * (a * Real.sqrt a)) := by
    refine (abs_ampK_neg_le ht hω hb).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have := Real.sqrt_le_sqrt hab
    gcongr
  have h3 : ∫ u in a..b, |ampK' t (-ω) u| ≤ ∫ u in a..b, u ^ (-(5 / 2 : ℝ)) / ω ^ 2 := by
    apply intervalIntegral.integral_mono_on hab
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.abs
      apply continuousOn_ampK'
      intro u hu
      rw [Set.uIcc_of_le hab] at hu
      exact ⟨lt_of_lt_of_le ha hu.1, hne u hu⟩
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro u hu
      rw [Set.uIcc_of_le hab] at hu
      left; exact (lt_of_lt_of_le ha hu.1).ne'
    · intro u hu
      exact abs_ampK'_neg_le ht hω (lt_of_lt_of_le ha hu.1)
  rw [intervalIntegral.integral_div] at h3
  have h4 := integral_rpow_neg_five_halves_le ha hab
  have h5 : (∫ u in a..b, u ^ (-(5 / 2 : ℝ))) / ω ^ 2 ≤ 2 / 3 * (1 / (a * Real.sqrt a)) / ω ^ 2 :=
    div_le_div_of_nonneg_right h4 (by positivity)
  have hfinal : 1 / (2 * ω ^ 2 * (a * Real.sqrt a)) + 1 / (2 * ω ^ 2 * (a * Real.sqrt a))
      + 2 / 3 * (1 / (a * Real.sqrt a)) / ω ^ 2 ≤ 2 / (ω ^ 2 * (a * Real.sqrt a)) := by
    have hs := Real.sqrt_pos.mpr ha
    have hq : 0 < ω ^ 2 * (a * Real.sqrt a) := by positivity
    calc 1 / (2 * ω ^ 2 * (a * Real.sqrt a)) + 1 / (2 * ω ^ 2 * (a * Real.sqrt a))
          + 2 / 3 * (1 / (a * Real.sqrt a)) / ω ^ 2 = (5 / 3) / (ω ^ 2 * (a * Real.sqrt a)) := by
          field_simp; ring
      _ ≤ 2 / (ω ^ 2 * (a * Real.sqrt a)) := div_le_div_of_nonneg_right (by norm_num) hq.le
  linarith


theorem hasDerivAt_one_div_sqrt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x => 1 / Real.sqrt x) (-(1 / (2 * (u * Real.sqrt u)))) u := by
  have hs := Real.sqrt_pos.mpr hu
  have h := (Real.hasDerivAt_sqrt hu.ne').inv hs.ne'
  simp only [one_div] at h ⊢
  refine h.congr_deriv ?_
  rw [Real.sq_sqrt hu.le] at *
  field_simp

/-- **Near the stationary point** (second-derivative test with the weight `u^(-1/2)` on `[a, 2a]`,
first-derivative test on `[2a, b]`): if `t < 2ωa` and `2a ≤ b`, then
`‖I(a, b)‖ ≤ 24 √a/√t + 2 h(2a)`. -/
theorem norm_mI_le_of_near {t ω a b : ℝ} (ht : 0 < t) (ha : 0 < a)
    (h2ab : 2 * a ≤ b) (h2a : t < ω * (2 * a)) :
    ‖mI t ω a b‖ ≤ 24 * Real.sqrt a / Real.sqrt t + 2 * ampH t ω (2 * a) := by
  have h2a0 : 0 < 2 * a := by positivity
  have haa : a ≤ 2 * a := by linarith
  -- a phase that is continuous everywhere and equals `Φ` near `[a, ∞)`
  set Ψ : ℝ → ℝ := fun u => ω * u - t * Real.log (max u (a / 2)) with hΨ
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    refine continuous_const.mul continuous_id |>.sub (continuous_const.mul ?_)
    exact Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const)
      fun u => by simp only [mem_compl_iff, mem_singleton_iff]; have := le_max_right u (a / 2); intro h; linarith
  have hΨeq : ∀ u, a / 2 < u → Ψ =ᶠ[𝓝 u] phase t ω := by
    intro u hu
    filter_upwards [lt_mem_nhds hu] with v hv
    simp only [hΨ, phase, max_eq_left hv.le]
  have hΨd : ∀ u ∈ Icc a (2 * a), HasDerivAt Ψ (phase' t ω u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    exact (hasDerivAt_phase t ω hu0).congr_of_eventuallyEq (hΨeq u (by linarith [hu.1]))
  have hΦ'd : ∀ u ∈ Icc a (2 * a), HasDerivAt (phase' t ω) (t / u ^ 2) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    have h := (hasDerivAt_id u).inv hu0.ne'
    have h2 := (h.const_mul t).const_sub ω
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [id]; ring
    · filter_upwards with v
      simp [phase', div_eq_mul_inv]
  set r : ℝ := t / (4 * a ^ 2) with hr
  have hr0 : 0 < r := by positivity
  have hM : ∀ y ∈ Icc a (2 * a), ‖∫ x in a..y, expI Ψ x‖ ≤ 12 / Real.sqrt r := by
    intro y hy
    refine norm_integral_expI_le_of_deriv_two_ge hy.1 hr0 (fun x hx => hΨd x ⟨hx.1, hx.2.trans hy.2⟩)
      (fun x hx => hΦ'd x ⟨hx.1, hx.2.trans hy.2⟩) ?_ ?_
    · apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro x hx; exact (pow_pos (lt_of_lt_of_le ha hx.1) 2).ne'
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      rw [hr]
      apply div_le_div_of_nonneg_left ht.le (pow_pos hx0 2)
      nlinarith [hx.1, hx.2.trans hy.2]
  have hw := norm_integral_weight_le haa (g := fun x => 1 / Real.sqrt x)
    (g' := fun u => -(1 / (2 * (u * Real.sqrt u)))) (Φ := Ψ)
    (fun x hx => hasDerivAt_one_div_sqrt (lt_of_lt_of_le ha hx.1))
    (by
      apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; have : 0 < x := lt_of_lt_of_le ha hx.1
      have := Real.sqrt_pos.mpr this; positivity)
    (fun x hx => by
      have : 0 < x := lt_of_lt_of_le ha hx.1
      have := Real.sqrt_pos.mpr this
      simp only [neg_nonpos]; positivity)
    (by positivity) hΨc hM
  have hfirst : mI t ω a (2 * a) = ∫ x in a..(2 * a), ((1 / Real.sqrt x : ℝ) : ℂ) * expI Ψ x := by
    unfold mI
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le haa] at hx
    have : Ψ x = phase t ω x := by
      simp only [hΨ, phase, max_eq_left (show a / 2 ≤ x by linarith [hx.1])]
    simp only [expI, this]
  have hval : 1 / Real.sqrt a * (12 / Real.sqrt r) = 24 * Real.sqrt a / Real.sqrt t := by
    have hsa := Real.sqrt_pos.mpr ha
    have hst := Real.sqrt_pos.mpr ht
    have : Real.sqrt r = Real.sqrt t / (2 * a) := by
      rw [hr, Real.sqrt_div ht.le, show 4 * a ^ 2 = (2 * a) ^ 2 by ring, Real.sqrt_sq h2a0.le]
    rw [this]
    have hsa2 := Real.mul_self_sqrt ha.le
    field_simp
    nlinarith [hsa2]
  have h1 : ‖mI t ω a (2 * a)‖ ≤ 24 * Real.sqrt a / Real.sqrt t := by
    rw [hfirst, ← hval]; exact hw
  have h2 : ‖mI t ω (2 * a) b‖ ≤ 2 * ampH t ω (2 * a) := by
    have := norm_integral_tail_le (ε := 0) ht.le le_rfl h2a0 h2ab h2a
    simp only [zero_mul, neg_zero, Real.exp_zero] at this
    exact this
  rw [← mI_add t ω ha.le h2a0.le (by linarith)]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end ZetaMellinPhase

end RiemannHypothesis
