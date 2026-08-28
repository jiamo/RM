/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Convexity

/-!
# The convexity bound with a logarithm instead of an `ε`

`RiemannHypothesis.norm_riemannZeta_le_convexity` gives, for every `ε > 0`, a bound
`‖ζ(σ + i t)‖ ≤ C_ε |t| ^ ((1 - σ)/2 + ε)` inside the closed critical strip.  This file
removes the `ε` at the cost of a single logarithm:

`‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t| ^ ((1 - σ)/2)`   for `0 ≤ σ ≤ 1`, `|t| ≥ 3`,

which is the classical form of the convexity bound; at `σ = 1/2` it reads
`‖ζ(1/2 + i t)‖ ≤ C |t|^(1/4) (1 + log|t|)`.

The proof reuses the Phragmén–Lindelöf apparatus of `RiemannHypothesis.Convexity` with the
interpolation exponent `ε = 0`, dividing in addition by the analytic function
`log u(s)`, `u(s) = s(1 - s) + 4`.  On the closed strip `re u ≥ 4`, so `log u` is analytic
and `‖log u‖ ≥ log 4 > 1`, while at height `|t| ≥ 3` one has `‖log u‖ ≤ 3(1 + log|t|)`: the
factor `1/log u` is therefore harmless for the growth hypothesis and just large enough to
absorb the logarithm in the two boundary bounds.

## Main results

* `norm_riemannZeta_le_convexity_log` : `‖ζ(s)‖ ≤ C (1 + log|t|) |t| ^ ((1 - re s)/2)`.
* `norm_riemannZeta_le_critical_line_log` : `‖ζ(1/2 + i t)‖ ≤ C (1 + log|t|) |t| ^ (1/4)`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-- The principal logarithm of `u(s) = s(1 - s) + 4`; analytic on the closed strip. -/
def logAux (s : ℂ) : ℂ := Complex.log (uAux s)

/-- The function to which Phragmén–Lindelöf is applied here: the `ε = 0` interpolation
divided by `log u`. -/
def hAux (s : ℂ) : ℂ := gAux 0 s / logAux s

lemma norm_uAux_ge_four {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : (4 : ℝ) ≤ ‖uAux s‖ := by
  have := norm_uAux_ge h0 h1
  nlinarith [sq_nonneg s.im]

lemma one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact he

lemma logAux_re (s : ℂ) :
    (logAux s).re = Real.log ‖uAux s‖ := by
  simp [logAux, Complex.log_re]

lemma norm_logAux_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : Real.log 4 ≤ ‖logAux s‖ := by
  have hre : Real.log 4 ≤ (logAux s).re := by
    rw [logAux_re s]
    exact Real.log_le_log (by norm_num) (norm_uAux_ge_four h0 h1)
  exact hre.trans (Complex.re_le_norm _)

lemma one_le_norm_logAux {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : (1 : ℝ) ≤ ‖logAux s‖ :=
  le_trans one_lt_log_four.le (norm_logAux_ge h0 h1)

lemma logAux_ne_zero {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : logAux s ≠ 0 := by
  intro hcon
  have := one_le_norm_logAux h0 h1
  rw [hcon] at this
  simp at this
  linarith

/-- At height at least `3` the logarithm of `u` is at most `3 (1 + log|t|)` in modulus. -/
lemma norm_logAux_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    ‖logAux s‖ ≤ 3 * (1 + Real.log |s.im|) := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hL : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
  have hu4 := norm_uAux_ge_four h0 h1
  have hu2 : ‖uAux s‖ ≤ 2 * s.im ^ 2 := norm_uAux_le h0 h1 ht
  have hre : (logAux s).re = Real.log ‖uAux s‖ := logAux_re s
  have hlogle : Real.log ‖uAux s‖ ≤ Real.log 2 + 2 * Real.log |s.im| := by
    have h1' : Real.log ‖uAux s‖ ≤ Real.log (2 * |s.im| ^ 2) := by
      refine Real.log_le_log (by linarith) ?_
      rw [hsq]
      exact hu2
    have h2' : Real.log (2 * |s.im| ^ 2) = Real.log 2 + 2 * Real.log |s.im| := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith [h1'.trans_eq h2']
  have hlognn : 0 ≤ Real.log ‖uAux s‖ := by
    have : Real.log 4 ≤ Real.log ‖uAux s‖ := Real.log_le_log (by norm_num) hu4
    linarith [one_lt_log_four]
  have harg : |(logAux s).im| ≤ Real.pi / 2 := by
    have hnn : (0 : ℝ) ≤ (uAux s).re := by
      have := uAux_re_ge h0 h1
      nlinarith [sq_nonneg s.im]
    have : (logAux s).im = Complex.arg (uAux s) := by simp [logAux, Complex.log_im]
    rw [this]
    exact Complex.abs_arg_le_pi_div_two_iff.2 hnn
  have hb := Complex.norm_le_abs_re_add_abs_im (logAux s)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  rw [hre] at hb
  rw [abs_of_nonneg hlognn] at hb
  linarith

lemma differentiableAt_logAux {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    DifferentiableAt ℂ logAux s := by
  have hu : DifferentiableAt ℂ uAux s := by
    unfold uAux
    fun_prop
  exact (Complex.differentiableAt_log (uAux_mem_slitPlane h0 h1)).comp s hu

lemma continuousAt_hAux {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : ContinuousAt hAux s :=
  (continuousAt_gAux 0 h0 h1).div (differentiableAt_logAux h0 h1).continuousAt
    (logAux_ne_zero h0 h1)

lemma diffContOnCl_hAux : DiffContOnCl ℂ hAux (Complex.re ⁻¹' Set.Ioo 0 1) := by
  constructor
  · intro s hs
    have hs1 : s ≠ 1 := by
      intro hcon
      have : s.re = 1 := by rw [hcon]; simp
      exact absurd this (ne_of_lt hs.2)
    exact (((differentiableAt_gAux 0 hs.1.le hs.2.le hs1).div
      (differentiableAt_logAux hs.1.le hs.2.le)
      (logAux_ne_zero hs.1.le hs.2.le))).differentiableWithinAt
  · intro s hs
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hs
    exact (continuousAt_hAux hs.1 hs.2).continuousWithinAt

lemma isBigO_hAux :
    ∃ c < Real.pi / (1 - 0), ∃ B : ℝ, hAux =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)] fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨c, hc, B, hO⟩ := isBigO_gAux (le_refl (0 : ℝ))
  refine ⟨c, hc, B, Asymptotics.IsBigO.trans ?_ hO⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  have hmem : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 1), z.re ∈ Set.Ioo (0 : ℝ) 1 :=
    Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun _ hz => hz)
  filter_upwards [hmem] with z hz
  have hlog := one_le_norm_logAux hz.1.le hz.2.le
  rw [hAux, norm_div, one_mul]
  exact div_le_self (norm_nonneg _) hlog

/-- At large height the two edges of the strip give a *constant* bound for `‖h‖`. -/
lemma norm_hAux_le_boundary_large {s : ℂ} (hs : s.re = 0 ∨ s.re = 1) (ht : 3 ≤ |s.im|) :
    ‖hAux s‖ ≤ Real.exp (Real.pi / 8) * 4 := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have h0 : 0 ≤ s.re := by rcases hs with h | h <;> simp [h]
  have h1 : s.re ≤ 1 := by rcases hs with h | h <;> simp [h]
  have hL : 1 < Real.log |s.im| := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact he
    have : Real.log 3 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) ht
    linarith
  -- the numerator: the `ε = 0` interpolation is bounded by `e^(π/8) (6 + log(1+|t|))`
  have hzeta := norm_riemannZeta_le_boundary hs ht
  have hexp := norm_expAux_le (le_refl (0 : ℝ)) h0 h1 ht
  have hratio := norm_ratio_sq_le_one h0
  have hlogpos : 0 ≤ 6 + Real.log (1 + |s.im|) := by
    have : (0 : ℝ) ≤ Real.log (1 + |s.im|) := Real.log_nonneg (by linarith)
    linarith
  have hpowmul : |s.im| ^ ((1 - s.re) / 2) * |s.im| ^ (-((1 - s.re) / 2 + 0)) = 1 := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hb1 : ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖
      ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|))) :=
    mul_le_mul hratio hzeta (norm_nonneg _) zero_le_one
  have hrhs1 : (0 : ℝ) ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|))) := by
    have hnn := Real.rpow_nonneg hT0.le ((1 - s.re) / 2)
    nlinarith
  have hb2 := mul_le_mul hb1 hexp (norm_nonneg _) hrhs1
  have hnum : ‖gAux 0 s‖ ≤ Real.exp (Real.pi / 8) * (6 + Real.log (1 + |s.im|)) := by
    rw [gAux, norm_mul, norm_mul]
    calc ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖ * ‖expAux 0 s‖
        ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|)))
          * (Real.exp (Real.pi / 8) * |s.im| ^ (-((1 - s.re) / 2 + 0))) := hb2
      _ = Real.exp (Real.pi / 8) * ((6 + Real.log (1 + |s.im|))
          * (|s.im| ^ ((1 - s.re) / 2) * |s.im| ^ (-((1 - s.re) / 2 + 0)))) := by ring
      _ = Real.exp (Real.pi / 8) * (6 + Real.log (1 + |s.im|)) := by
          rw [hpowmul, mul_one]
  -- the denominator: `‖log u‖ ≥ 2 log|t|`
  have hden : 2 * Real.log |s.im| ≤ ‖logAux s‖ := by
    have hre : (logAux s).re = Real.log ‖uAux s‖ := logAux_re s
    have hu : |s.im| ^ 2 ≤ ‖uAux s‖ := by
      have := norm_uAux_ge h0 h1
      nlinarith [sq_abs s.im]
    have hlog : 2 * Real.log |s.im| ≤ Real.log ‖uAux s‖ := by
      have h := Real.log_le_log (by positivity) hu
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    calc 2 * Real.log |s.im| ≤ (logAux s).re := by rw [hre]; exact hlog
      _ ≤ ‖logAux s‖ := Complex.re_le_norm _
  have hdenpos : (0 : ℝ) < ‖logAux s‖ := by linarith
  -- combine
  have hnumle : 6 + Real.log (1 + |s.im|) ≤ 7 + Real.log |s.im| := by
    have h2 : Real.log (1 + |s.im|) ≤ Real.log (2 * |s.im|) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (2 * |s.im|) = Real.log 2 + Real.log |s.im| :=
      Real.log_mul (by norm_num) (by positivity)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    linarith
  have hfrac : (6 + Real.log (1 + |s.im|)) / ‖logAux s‖ ≤ 4 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  rw [hAux, norm_div]
  calc ‖gAux 0 s‖ / ‖logAux s‖
      ≤ (Real.exp (Real.pi / 8) * (6 + Real.log (1 + |s.im|))) / ‖logAux s‖ := by
        exact div_le_div_of_nonneg_right hnum hdenpos.le
    _ = Real.exp (Real.pi / 8) * ((6 + Real.log (1 + |s.im|)) / ‖logAux s‖) := by
        rw [mul_div_assoc]
    _ ≤ Real.exp (Real.pi / 8) * 4 := by
        exact mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le

/-- The two edges of the strip: `‖h‖` is bounded there by an absolute constant. -/
lemma exists_bound_boundary_log :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 0 ∨ s.re = 1 → ‖hAux s‖ ≤ C := by
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 3} with hK
  have hKclosed : IsClosed K := by
    have hEq : K = (Complex.re ⁻¹' Set.Icc 0 1) ∩ ((fun z : ℂ => |z.im|) ⁻¹' Set.Iic 3) := by
      ext z
      simp [hK, Set.mem_Icc, and_assoc]
    rw [hEq]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Iic.preimage Complex.continuous_im.abs)
  have hKbdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨4, fun z hz => ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hb := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 1 := by
      rw [abs_of_nonneg hz.1]
      exact hz.2.1
    linarith [hz.2.2]
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hcont : ContinuousOn hAux K := fun z hz =>
    (continuousAt_hAux hz.1 hz.2.1).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hcont
  have hpos2 : (0 : ℝ) < Real.exp (Real.pi / 8) * 4 := by positivity
  refine ⟨max C₁ (Real.exp (Real.pi / 8) * 4), lt_of_lt_of_le hpos2 (le_max_right _ _), ?_⟩
  intro s hs
  have h0 : 0 ≤ s.re := by rcases hs with h | h <;> simp [h]
  have h1 : s.re ≤ 1 := by rcases hs with h | h <;> simp [h]
  rcases le_or_gt |s.im| 3 with hsm | hlg
  · exact (hC₁ s ⟨h0, h1, hsm⟩).trans (le_max_left _ _)
  · exact (norm_hAux_le_boundary_large hs hlg.le).trans (le_max_right _ _)

/-- **The convexity bound with a logarithm.**  There is a constant `C` with
`‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t| ^ ((1 - σ)/2)` for `0 ≤ σ ≤ 1` and `|t| ≥ 3`. -/
theorem norm_riemannZeta_le_convexity_log :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2) := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_boundary_log
  set a : ℝ := 9 / 25 * (Real.exp (-(Real.pi / 8)) / 2) with ha
  have hapos : 0 < a := by
    rw [ha]
    positivity
  refine ⟨3 * C / a, by positivity, ?_⟩
  intro s h0 h1 ht
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hPL : ‖hAux s‖ ≤ C :=
    PhragmenLindelof.vertical_strip diffContOnCl_hAux isBigO_hAux
      (fun z hz => hC z (Or.inl hz)) (fun z hz => hC z (Or.inr hz)) h0 h1
  have hfac : gAux 0 s = hAux s * logAux s := by
    rw [hAux]
    field_simp [logAux_ne_zero h0 h1]
  have hgle : ‖gAux 0 s‖ ≤ C * (3 * (1 + Real.log |s.im|)) := by
    rw [hfac, norm_mul]
    exact mul_le_mul hPL (norm_logAux_le h0 h1 ht) (norm_nonneg _) hCpos.le
  have hPpos : (0 : ℝ) < |s.im| ^ (-((1 - s.re) / 2 + 0)) := Real.rpow_pos_of_pos hT0 _
  have hQpos : (0 : ℝ) < |s.im| ^ ((1 - s.re) / 2) := Real.rpow_pos_of_pos hT0 _
  have hPQ : |s.im| ^ (-((1 - s.re) / 2 + 0)) * |s.im| ^ ((1 - s.re) / 2) = 1 := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hratio_ge := norm_ratio_sq_ge h0 h1 ht
  have hexp_ge := norm_expAux_ge (le_refl (0 : ℝ)) zero_le_one h0 h1 ht
  have hnorm : ‖gAux 0 s‖
      = ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖ * ‖expAux 0 s‖ := by
    rw [gAux, norm_mul, norm_mul]
  have hstep : a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + 0))
      ≤ C * (3 * (1 + Real.log |s.im|)) := by
    calc a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + 0))
        = (9 / 25 * ‖riemannZeta s‖)
          * (Real.exp (-(Real.pi / 8)) / 2 * |s.im| ^ (-((1 - s.re) / 2 + 0))) := by
          rw [ha]; ring
      _ ≤ (‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖) * ‖expAux 0 s‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hratio_ge (norm_nonneg _)) hexp_ge
            (mul_nonneg (by positivity) hPpos.le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖gAux 0 s‖ := hnorm.symm
      _ ≤ C * (3 * (1 + Real.log |s.im|)) := hgle
  have hfinal : a * ‖riemannZeta s‖
      ≤ C * (3 * (1 + Real.log |s.im|)) * |s.im| ^ ((1 - s.re) / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hstep hQpos.le
    calc a * ‖riemannZeta s‖
        = a * ‖riemannZeta s‖ * (|s.im| ^ (-((1 - s.re) / 2 + 0))
            * |s.im| ^ ((1 - s.re) / 2)) := by rw [hPQ]; ring
      _ = a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + 0))
            * |s.im| ^ ((1 - s.re) / 2) := by ring
      _ ≤ C * (3 * (1 + Real.log |s.im|)) * |s.im| ^ ((1 - s.re) / 2) := hmul
  have hgoal : ‖riemannZeta s‖ * a
      ≤ 3 * C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2) := by
    nlinarith [hfinal]
  rw [show 3 * C / a * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2)
      = (3 * C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2)) / a by ring,
    le_div_iff₀ hapos]
  exact hgoal

/-- The convexity bound with a logarithm on the critical line:
`‖ζ(1/2 + i t)‖ ≤ C (1 + log|t|) |t| ^ (1/4)`. -/
theorem norm_riemannZeta_le_critical_line_log :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + Real.log |t|) * |t| ^ ((1 : ℝ) / 4) := by
  obtain ⟨C, hCpos, hC⟩ := norm_riemannZeta_le_convexity_log
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  have hre : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have him : ((1 : ℂ) / 2 + (t : ℂ) * I).im = t := by simp
  have h := hC ((1 : ℂ) / 2 + (t : ℂ) * I) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
    (by rw [him]; exact ht)
  rw [hre, him] at h
  refine h.trans_eq ?_
  norm_num

end RiemannHypothesis

end
