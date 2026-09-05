/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ConvexityLog
import RiemannHypothesis.SubconvexityUnconditional
import RiemannHypothesis.Symmetry

/-!
# Subconvexity in the left half of the critical strip

`RiemannHypothesis.norm_riemannZeta_strip_le` proves the subconvex bound
`‖ζ(σ + i t)‖ ≤ 400 t^((1-σ)/3) (log t + 1)` for `1/2 ≤ σ ≤ 1`; nothing better than the
convexity bound was available for `σ ≤ 1/2`.  This file fills that gap by interpolating,
through Phragmén–Lindelöf, between

* the left edge `re s = 0`, where `‖ζ(i t)‖ ≤ √(|t|/2π) (6 + log(1 + |t|))`
  (`RiemannHypothesis.norm_riemannZeta_mul_I_le`, from the functional equation), and
* the critical line `re s = 1/2`, where the unconditional Weyl exponent `1/6` is available
  (`RiemannHypothesis.norm_riemannZeta_criticalLine_le`).

Linear interpolation of the exponents `1/2` and `1/6` across `0 ≤ σ ≤ 1/2` gives the exponent
`1/2 - 2σ/3`, which is smaller than the convexity exponent `(1 - σ)/2` by the fixed power
`σ/6` of the height.

The interpolation is applied to `g(s) = ζ(s) u(s)^(-w(s)) / log u(s)`, with
`u(s) = s(1 - s) + 4` and `w(s) = 1/4 - s/3`, exactly as in
`RiemannHypothesis.Convexity` and `RiemannHypothesis.ConvexityLog`: the modulus of
`u(s)^(-w(s))` is `≍ |t|^(-(1/2 - 2σ/3))`, and the division by `log u` absorbs the single
logarithm carried by both boundary bounds.  Note that `ζ` has no pole in the closed strip
`0 ≤ σ ≤ 1/2`, so no rational factor is needed here.

## Main results

* `exists_bound_criticalLine_sixth` : `‖ζ(1/2 + i t)‖ ≤ A |t|^(1/6) (1 + log|t|)` for all
  `|t| ≥ 3`, positive or negative — the `t ≥ 10⁹` bound of `SubconvexityUnconditional`
  extended to every height by the conjugation symmetry and the convexity bound.
* `norm_riemannZeta_le_subconvexity_left` : `‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^(1/2 - 2σ/3)`
  for `0 ≤ σ ≤ 1/2` and `|t| ≥ 3`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## The Weyl exponent on the critical line, at every height -/

/-- `‖ζ‖` on the critical line depends only on `|t|`, by the conjugation symmetry. -/
lemma norm_riemannZeta_criticalLine_abs (t : ℝ) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ = ‖riemannZeta (1 / 2 + ((|t| : ℝ) : ℂ) * I)‖ := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h]
    have hre : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
    have hs : (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) := by
      simp [Complex.ext_iff]
    rw [hs, riemannZeta_conj_of_mem_strip (by rw [hre]; norm_num) (by rw [hre]; norm_num),
      norm_conj]

/-- The unconditional Weyl exponent `1/6` on the critical line, at *every* height `|t| ≥ 3`:
the bound of `norm_riemannZeta_criticalLine_le` (valid for `t ≥ 10⁹`) extended downwards by the
convexity bound and sideways by the conjugation symmetry. -/
lemma exists_bound_criticalLine_sixth :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ A * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) := by
  obtain ⟨C, hCpos, hC⟩ := norm_riemannZeta_le_critical_line_log
  refine ⟨max 200 (6 * C), by positivity, ?_⟩
  intro t ht
  have hT0 : (0 : ℝ) < |t| := by linarith
  have hT1 : (1 : ℝ) ≤ |t| := by linarith
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg hT1
  have hpow : 0 < |t| ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hT0 _
  rw [norm_riemannZeta_criticalLine_abs t]
  rcases le_or_gt ((10 : ℝ) ^ 9) |t| with hbig | hsmall
  · have h := SubconvexityUnconditional.norm_riemannZeta_criticalLine_le (t := |t|) hbig
    refine h.trans ?_
    have hmul : 200 * |t| ^ ((1 : ℝ) / 6) ≤ max 200 (6 * C) * |t| ^ ((1 : ℝ) / 6) := by
      gcongr
      exact le_max_left _ _
    calc 200 * |t| ^ ((1 : ℝ) / 6) * (Real.log |t| + 1)
        = 200 * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) := by ring
      _ ≤ max 200 (6 * C) * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) := by
          gcongr
  · have h := hC |t| (by rwa [abs_of_pos hT0])
    rw [abs_of_pos hT0] at h
    have hsplit : |t| ^ ((1 : ℝ) / 4) ≤ 6 * |t| ^ ((1 : ℝ) / 6) := by
      have hfac : |t| ^ ((1 : ℝ) / 4) = |t| ^ ((1 : ℝ) / 6) * |t| ^ ((1 : ℝ) / 12) := by
        rw [← Real.rpow_add hT0]
        norm_num
      have h12 : |t| ^ ((1 : ℝ) / 12) ≤ 6 := by
        have hbase : |t| ≤ (6 : ℝ) ^ (12 : ℕ) := le_trans hsmall.le (by norm_num)
        have hle : |t| ^ ((1 : ℝ) / 12) ≤ ((6 : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow hT0.le hbase (by norm_num)
        refine hle.trans_eq ?_
        rw [← Real.rpow_natCast (6 : ℝ) 12, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [hfac]
      nlinarith
    have hCle : C * (1 + Real.log |t|) * |t| ^ ((1 : ℝ) / 4)
        ≤ (6 * C) * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) := by
      have hfac : (0 : ℝ) ≤ C * (1 + Real.log |t|) := by positivity
      calc C * (1 + Real.log |t|) * |t| ^ ((1 : ℝ) / 4)
          ≤ C * (1 + Real.log |t|) * (6 * |t| ^ ((1 : ℝ) / 6)) :=
            mul_le_mul_of_nonneg_left hsplit hfac
        _ = (6 * C) * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) := by ring
    refine h.trans (hCle.trans ?_)
    have hmax : (6 * C : ℝ) ≤ max 200 (6 * C) := le_max_right _ _
    gcongr

/-! ## The interpolating function -/

/-- The interpolation exponent for the left half of the strip: `w(s) = 1/4 - s/3`, so that
`|u(s)^(-w(s))| ≍ |t|^(-(1/2 - 2σ/3))`. -/
def wLeft (s : ℂ) : ℂ := 1 / 4 - s / 3

/-- The interpolating factor `u(s)^(-w(s))`, through the principal logarithm. -/
def expLeft (s : ℂ) : ℂ := Complex.exp (-(wLeft s) * Complex.log (uAux s))

/-- The function to which Phragmén–Lindelöf is applied on `0 ≤ re s ≤ 1/2`. -/
def gLeft (s : ℂ) : ℂ := riemannZeta s * expLeft s / logAux s

lemma norm_expLeft (s : ℂ) :
    ‖expLeft s‖ = Real.exp (-(1 / 4 - s.re / 3) * Real.log ‖uAux s‖
      - s.im / 3 * Complex.arg (uAux s)) := by
  rw [expLeft, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.log_re, Complex.log_im, wLeft]

/-- The interpolating factor is at most `e^(π/6) |t|^(-(1/2 - 2σ/3))`. -/
lemma norm_expLeft_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 3 ≤ |s.im|) :
    ‖expLeft s‖ ≤ Real.exp (Real.pi / 6) * |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) := by
  have h1' : s.re ≤ 1 := by linarith
  have hT : (0 : ℝ) < |s.im| := by linarith
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hu1 : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1'
  have hupos : (0 : ℝ) < ‖uAux s‖ := by nlinarith [sq_nonneg s.im]
  have hA : 0 ≤ 1 / 4 - s.re / 3 := by linarith
  have harg : |s.im / 3 * Complex.arg (uAux s)| ≤ Real.pi / 6 := by
    have hb := abs_arg_uAux_le h0 h1'
    rw [abs_mul]
    have h1'' : |s.im / 3| = |s.im| / 3 := by
      rw [abs_div]
      simp
    rw [h1'']
    have hstep : |s.im| / 3 * |Complex.arg (uAux s)|
        ≤ |s.im| / 3 * (Real.pi / 2 * (|s.im| / ‖uAux s‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine hstep.trans ?_
    have hle : |s.im| * |s.im| ≤ ‖uAux s‖ := by nlinarith
    have hrw : |s.im| / 3 * (Real.pi / 2 * (|s.im| / ‖uAux s‖))
        = Real.pi / 6 * ((|s.im| * |s.im|) / ‖uAux s‖) := by ring
    rw [hrw, mul_le_iff_le_one_right (by positivity), div_le_one hupos]
    exact hle
  have hlog : Real.log (|s.im| ^ 2) ≤ Real.log ‖uAux s‖ := by
    refine Real.log_le_log (by positivity) ?_
    nlinarith
  rw [norm_expLeft]
  have hrpow : |s.im| ^ (-(1 / 2 - 2 * s.re / 3))
      = Real.exp (-(1 / 4 - s.re / 3) * Real.log (|s.im| ^ 2)) := by
    rw [Real.rpow_def_of_pos hT, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hargge : -(Real.pi / 6) ≤ s.im / 3 * Complex.arg (uAux s) := (abs_le.mp harg).1
  have hmul : (1 / 4 - s.re / 3) * Real.log (|s.im| ^ 2)
      ≤ (1 / 4 - s.re / 3) * Real.log ‖uAux s‖ := mul_le_mul_of_nonneg_left hlog hA
  linarith

/-- The interpolating factor is at least `e^(-π/6)/2 · |t|^(-(1/2 - 2σ/3))`. -/
lemma norm_expLeft_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 3 ≤ |s.im|) :
    Real.exp (-(Real.pi / 6)) / 2 * |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) ≤ ‖expLeft s‖ := by
  have h1' : s.re ≤ 1 := by linarith
  have hT : (0 : ℝ) < |s.im| := by linarith
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hu1 : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1'
  have hu2 : ‖uAux s‖ ≤ 2 * s.im ^ 2 := norm_uAux_le h0 h1' ht
  have hupos : (0 : ℝ) < ‖uAux s‖ := by nlinarith [sq_nonneg s.im]
  have hA : 0 ≤ 1 / 4 - s.re / 3 := by linarith
  have hA4 : 1 / 4 - s.re / 3 ≤ 1 / 4 := by linarith
  have harg : |s.im / 3 * Complex.arg (uAux s)| ≤ Real.pi / 6 := by
    have hb := abs_arg_uAux_le h0 h1'
    rw [abs_mul]
    have h1'' : |s.im / 3| = |s.im| / 3 := by
      rw [abs_div]
      simp
    rw [h1'']
    have hstep : |s.im| / 3 * |Complex.arg (uAux s)|
        ≤ |s.im| / 3 * (Real.pi / 2 * (|s.im| / ‖uAux s‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine hstep.trans ?_
    have hle : |s.im| * |s.im| ≤ ‖uAux s‖ := by nlinarith
    have hrw : |s.im| / 3 * (Real.pi / 2 * (|s.im| / ‖uAux s‖))
        = Real.pi / 6 * ((|s.im| * |s.im|) / ‖uAux s‖) := by ring
    rw [hrw, mul_le_iff_le_one_right (by positivity), div_le_one hupos]
    exact hle
  have hlog : Real.log ‖uAux s‖ ≤ Real.log 2 + Real.log (|s.im| ^ 2) := by
    have h2 : Real.log ‖uAux s‖ ≤ Real.log (2 * |s.im| ^ 2) := by
      refine Real.log_le_log hupos ?_
      nlinarith
    refine h2.trans_eq ?_
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [norm_expLeft]
  have hrpow : |s.im| ^ (-(1 / 2 - 2 * s.re / 3))
      = Real.exp (-(1 / 4 - s.re / 3) * Real.log (|s.im| ^ 2)) := by
    rw [Real.rpow_def_of_pos hT, Real.log_pow]
    congr 1
    push_cast
    ring
  have hhalf : Real.exp (-(Real.pi / 6)) / 2
      = Real.exp (-(Real.pi / 6) - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [hrpow, hhalf, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hargle : s.im / 3 * Complex.arg (uAux s) ≤ Real.pi / 6 :=
    le_trans (le_abs_self _) harg
  have hmul : (1 / 4 - s.re / 3) * Real.log ‖uAux s‖
      ≤ (1 / 4 - s.re / 3) * (Real.log 2 + Real.log (|s.im| ^ 2)) :=
    mul_le_mul_of_nonneg_left hlog hA
  have hexpand : (1 / 4 - s.re / 3) * (Real.log 2 + Real.log (|s.im| ^ 2))
      = (1 / 4 - s.re / 3) * Real.log 2 + (1 / 4 - s.re / 3) * Real.log (|s.im| ^ 2) := by
    ring
  have hmul2 : (1 / 4 - s.re / 3) * Real.log 2 ≤ Real.log 2 := by nlinarith
  linarith

/-! ## Analyticity -/

lemma differentiableAt_expLeft {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    DifferentiableAt ℂ expLeft s := by
  have hu : DifferentiableAt ℂ uAux s := by
    unfold uAux
    fun_prop
  have hlog : DifferentiableAt ℂ Complex.log (uAux s) :=
    Complex.differentiableAt_log (uAux_mem_slitPlane h0 h1)
  have hw : DifferentiableAt ℂ wLeft s := by
    unfold wLeft
    fun_prop
  exact (hw.neg.mul (hlog.comp s hu)).cexp

lemma differentiableAt_gLeft {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) :
    DifferentiableAt ℂ gLeft s := by
  have h1' : s.re ≤ 1 := by linarith
  have hs1 : s ≠ 1 := by
    intro hcon
    rw [hcon] at h1
    norm_num at h1
  exact ((differentiableAt_riemannZeta hs1).mul (differentiableAt_expLeft h0 h1')).div
    (differentiableAt_logAux h0 h1') (logAux_ne_zero h0 h1')

lemma diffContOnCl_gLeft : DiffContOnCl ℂ gLeft (Complex.re ⁻¹' Set.Ioo 0 (1 / 2)) := by
  constructor
  · intro s hs
    exact (differentiableAt_gLeft hs.1.le hs.2.le).differentiableWithinAt
  · intro s hs
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)] at hs
    exact (differentiableAt_gLeft hs.1 hs.2).continuousAt.continuousWithinAt

/-! ## The growth hypothesis -/

lemma norm_gLeft_le_exp {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 3 ≤ |s.im|) :
    ‖gLeft s‖ ≤ 200 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2 := by
  have h1' : s.re ≤ 1 := by linarith
  have hT : (0 : ℝ) < |s.im| := by linarith
  have hzeta := norm_riemannZeta_le_exp_strip h0 h1' ht
  have hzeta0 : (0 : ℝ) ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hexp : ‖expLeft s‖ ≤ 2 := by
    refine (norm_expLeft_le h0 h1 ht).trans ?_
    have hle1 : |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith) ?_
      linarith
    have hpi : Real.exp (Real.pi / 6) ≤ 2 := by
      have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
      have : Real.exp (Real.pi / 6) ≤ Real.exp (0.6) := by
        refine Real.exp_le_exp.2 (by linarith)
      refine this.trans ?_
      have hlog2 := Real.log_two_gt_d9
      calc Real.exp (0.6 : ℝ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith [Real.rpow_nonneg hT.le (-(1 / 2 - 2 * s.re / 3)), Real.exp_pos (Real.pi / 6)]
  have hlog : (1 : ℝ) ≤ ‖logAux s‖ := one_le_norm_logAux h0 h1'
  have hpos : (0 : ℝ) < ‖logAux s‖ := by linarith
  rw [gLeft, norm_div, norm_mul]
  rw [div_le_iff₀ hpos]
  calc ‖riemannZeta s‖ * ‖expLeft s‖
      ≤ (100 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2) * 2 := by
        exact mul_le_mul hzeta hexp (norm_nonneg _) (by positivity)
    _ = 200 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2 * 1 := by ring
    _ ≤ 200 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2 * ‖logAux s‖ :=
        mul_le_mul_of_nonneg_left hlog (by positivity)


lemma isBigO_gLeft :
    ∃ c < Real.pi / (1 / 2 - 0), ∃ B : ℝ, gLeft =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 (1 / 2))] fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  refine ⟨1, ?_, 5, ?_⟩
  · rw [sub_zero]
    have := Real.pi_gt_three
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨200, ?_⟩
  have hmem : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 (1 / 2)), 3 ≤ |z.im| ∧ z.re ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    refine Filter.eventually_inf.2 ⟨{z : ℂ | 3 ≤ |z.im|}, ?_, Complex.re ⁻¹' Set.Ioo 0 (1 / 2),
      Filter.mem_principal_self _, ?_⟩
    · exact Filter.mem_comap.2 ⟨Set.Ici 3, Filter.Ici_mem_atTop 3, fun z hz => hz⟩
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hz2⟩
  filter_upwards [hmem] with z hz
  obtain ⟨ht, hre⟩ := hz
  have hT0 : (0 : ℝ) < |z.im| := by linarith
  have hg := norm_gLeft_le_exp hre.1.le hre.2.le ht
  have hsq : |z.im| ^ 2 ≤ Real.exp (2 * |z.im|) := by
    have hone : |z.im| ≤ Real.exp |z.im| := by
      have := Real.add_one_le_exp |z.im|
      linarith
    calc |z.im| ^ 2 ≤ Real.exp |z.im| ^ 2 := by
          exact pow_le_pow_left₀ hT0.le hone 2
      _ = Real.exp (2 * |z.im|) := by
          rw [← Real.exp_nsmul]
          norm_num
  have hcomb : Real.exp (Real.pi * |z.im| / 2) * |z.im| ^ 2
      ≤ Real.exp (5 * Real.exp (1 * |z.im|)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hle : |z.im| ≤ Real.exp (1 * |z.im|) := by
      have := Real.add_one_le_exp |z.im|
      rw [one_mul]
      linarith
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hstep : Real.pi * |z.im| / 2 + 2 * |z.im| ≤ 5 * |z.im| := by nlinarith
    linarith
  calc ‖gLeft z‖ ≤ 200 * Real.exp (Real.pi * |z.im| / 2) * |z.im| ^ 2 := hg
    _ = 200 * (Real.exp (Real.pi * |z.im| / 2) * |z.im| ^ 2) := by ring
    _ ≤ 200 * Real.exp (5 * Real.exp (1 * |z.im|)) := by linarith
    _ = 200 * ‖Real.exp (5 * Real.exp (1 * |z.im|))‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-! ## The boundary bounds -/

/-- `‖log u‖` is at least `2 log|t|`, which is what absorbs the boundary logarithms. -/
lemma norm_logAux_ge_two_log {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ht : 1 ≤ |s.im|) :
    2 * Real.log |s.im| ≤ ‖logAux s‖ := by
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hu : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1
  have hre : 2 * Real.log |s.im| ≤ (logAux s).re := by
    rw [logAux_re s]
    have h2 : Real.log (|s.im| ^ 2) ≤ Real.log ‖uAux s‖ := by
      refine Real.log_le_log (by positivity) ?_
      nlinarith
    rwa [Real.log_pow] at h2
    
  exact hre.trans (Complex.re_le_norm _)

/-- Both edges of the strip obey the interpolated bound, with a single logarithm. -/
lemma norm_riemannZeta_le_boundary_left {A : ℝ} (hApos : 0 < A)
    (hA : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ A * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|))
    {s : ℂ} (hs : s.re = 0 ∨ s.re = 1 / 2) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (A + 7) * |s.im| ^ (1 / 2 - 2 * s.re / 3) * (1 + Real.log |s.im|) := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg hT1
  rcases hs with h0 | h2
  · have hs' : s = ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [h0]
    have h := norm_riemannZeta_mul_I_le (t := s.im) (by linarith)
    rw [← hs'] at h
    refine h.trans ?_
    have hexp : |s.im| ^ (1 / 2 - 2 * s.re / 3) = Real.sqrt |s.im| := by
      rw [h0, Real.sqrt_eq_rpow]
      norm_num
    rw [hexp]
    have hsqrtle : Real.sqrt (|s.im| / (2 * Real.pi)) ≤ Real.sqrt |s.im| := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hloglt : Real.log (1 + |s.im|) ≤ 1 + Real.log |s.im| := by
      have h2' : Real.log (1 + |s.im|) ≤ Real.log (2 * |s.im|) := by
        refine Real.log_le_log (by linarith) (by linarith)
      have h3 : Real.log (2 * |s.im|) = Real.log 2 + Real.log |s.im| := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
        linarith
      linarith
    have hsqrt0 : 0 ≤ Real.sqrt |s.im| := Real.sqrt_nonneg _
    have hbound : (6 : ℝ) + Real.log (1 + |s.im|) ≤ (A + 7) * (1 + Real.log |s.im|) := by
      nlinarith
    have hnn : (0 : ℝ) ≤ 6 + Real.log (1 + |s.im|) := by
      have : (0 : ℝ) ≤ Real.log (1 + |s.im|) := Real.log_nonneg (by linarith)
      linarith
    calc Real.sqrt (|s.im| / (2 * Real.pi)) * (6 + Real.log (1 + |s.im|))
        ≤ Real.sqrt |s.im| * ((A + 7) * (1 + Real.log |s.im|)) :=
          mul_le_mul hsqrtle hbound hnn hsqrt0
      _ = (A + 7) * Real.sqrt |s.im| * (1 + Real.log |s.im|) := by ring
  · have hs' : s = 1 / 2 + ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [h2]
    have h := hA s.im ht
    rw [← hs'] at h
    refine h.trans ?_
    have hexp : |s.im| ^ (1 / 2 - 2 * s.re / 3) = |s.im| ^ ((1 : ℝ) / 6) := by
      rw [h2]
      norm_num
    rw [hexp]
    have hpow : 0 < |s.im| ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hT0 _
    nlinarith

/-- At large height, `‖g‖` is bounded on both edges by a constant. -/
lemma norm_gLeft_le_boundary_large {A : ℝ} (hApos : 0 < A)
    (hA : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ A * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|))
    {s : ℂ} (hs : s.re = 0 ∨ s.re = 1 / 2) (ht : 3 ≤ |s.im|) :
    ‖gLeft s‖ ≤ Real.exp (Real.pi / 6) * (A + 7) * (3 / 2) := by
  have h0 : 0 ≤ s.re := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; norm_num
  have h1 : s.re ≤ 1 / 2 := by
    rcases hs with h | h
    · rw [h]; norm_num
    · rw [h]
  have h1' : s.re ≤ 1 := by linarith
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg hT1
  have hzeta := norm_riemannZeta_le_boundary_left hApos hA hs ht
  have hexp := norm_expLeft_le h0 h1 ht
  have hL1 : (1 : ℝ) ≤ ‖logAux s‖ := one_le_norm_logAux h0 h1'
  have hL2 : 2 * Real.log |s.im| ≤ ‖logAux s‖ := norm_logAux_ge_two_log h0 h1' hT1
  have hLpos : (0 : ℝ) < ‖logAux s‖ := by linarith
  have hratio : 1 + Real.log |s.im| ≤ (3 / 2) * ‖logAux s‖ := by linarith
  have hpowpos : (0 : ℝ) < |s.im| ^ (1 / 2 - 2 * s.re / 3) := Real.rpow_pos_of_pos hT0 _
  have hcancel : |s.im| ^ (1 / 2 - 2 * s.re / 3) * |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) = 1 := by
    rw [← Real.rpow_add hT0]
    simp
  rw [gLeft, norm_div, norm_mul, div_le_iff₀ hLpos]
  have hstep : ‖riemannZeta s‖ * ‖expLeft s‖
      ≤ ((A + 7) * |s.im| ^ (1 / 2 - 2 * s.re / 3) * (1 + Real.log |s.im|))
        * (Real.exp (Real.pi / 6) * |s.im| ^ (-(1 / 2 - 2 * s.re / 3))) := by
    refine mul_le_mul hzeta hexp (norm_nonneg _) ?_
    have : (0 : ℝ) ≤ (A + 7) * |s.im| ^ (1 / 2 - 2 * s.re / 3) := by positivity
    nlinarith
  refine hstep.trans ?_
  have hrw : ((A + 7) * |s.im| ^ (1 / 2 - 2 * s.re / 3) * (1 + Real.log |s.im|))
        * (Real.exp (Real.pi / 6) * |s.im| ^ (-(1 / 2 - 2 * s.re / 3)))
      = Real.exp (Real.pi / 6) * (A + 7) * (1 + Real.log |s.im|)
        * (|s.im| ^ (1 / 2 - 2 * s.re / 3) * |s.im| ^ (-(1 / 2 - 2 * s.re / 3))) := by
    ring
  rw [hrw, hcancel, mul_one]
  have hc : (0 : ℝ) < Real.exp (Real.pi / 6) * (A + 7) := by positivity
  calc Real.exp (Real.pi / 6) * (A + 7) * (1 + Real.log |s.im|)
      ≤ Real.exp (Real.pi / 6) * (A + 7) * ((3 / 2) * ‖logAux s‖) := by
        exact mul_le_mul_of_nonneg_left hratio hc.le
    _ = Real.exp (Real.pi / 6) * (A + 7) * (3 / 2) * ‖logAux s‖ := by ring

/-- The two edges of the strip: `‖g‖` is bounded there by an absolute constant. -/
lemma exists_bound_boundary_left :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 0 ∨ s.re = 1 / 2 → ‖gLeft s‖ ≤ C := by
  classical
  obtain ⟨A, hApos, hA⟩ := exists_bound_criticalLine_sixth
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ |z.im| ≤ 3} with hK
  have hKclosed : IsClosed K := by
    have hEq : K = (Complex.re ⁻¹' Set.Icc 0 (1 / 2)) ∩ ((fun z : ℂ => |z.im|) ⁻¹' Set.Iic 3) := by
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
      linarith [hz.2.1]
    linarith [hz.2.2]
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hcont : ContinuousOn gLeft K := fun z hz =>
    (differentiableAt_gLeft hz.1 hz.2.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hcont
  have hpos2 : (0 : ℝ) < Real.exp (Real.pi / 6) * (A + 7) * (3 / 2) := by positivity
  refine ⟨max C₁ (Real.exp (Real.pi / 6) * (A + 7) * (3 / 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le hpos2 (le_max_right _ _)
  · intro s hs
    have h0 : 0 ≤ s.re := by
      rcases hs with h | h
      · rw [h]
      · rw [h]; norm_num
    have h1 : s.re ≤ 1 / 2 := by
      rcases hs with h | h
      · rw [h]; norm_num
      · rw [h]
    rcases le_or_gt |s.im| 3 with hsm | hlg
    · exact (hC₁ s ⟨h0, h1, hsm⟩).trans (le_max_left _ _)
    · exact (norm_gLeft_le_boundary_large hApos hA hs hlg.le).trans (le_max_right _ _)

/-! ## The subconvexity bound on the left half of the strip -/

/-- **Subconvexity for `ζ` on `0 ≤ σ ≤ 1/2`.**  There is a constant `C` with
`‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^(1/2 - 2σ/3)` for `0 ≤ σ ≤ 1/2` and `|t| ≥ 3`.

The exponent `1/2 - 2σ/3` is smaller than the convexity exponent `(1 - σ)/2` by `σ/6`. -/
theorem norm_riemannZeta_le_subconvexity_left :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 / 2 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ (1 / 2 - 2 * s.re / 3) := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_boundary_left
  refine ⟨C * 6 * Real.exp (Real.pi / 6), by positivity, ?_⟩
  intro s h0 h1 ht
  have h1' : s.re ≤ 1 := by linarith
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg hT1
  have hPL : ‖gLeft s‖ ≤ C :=
    PhragmenLindelof.vertical_strip diffContOnCl_gLeft isBigO_gLeft
      (fun z hz => hC z (Or.inl hz)) (fun z hz => hC z (Or.inr hz)) h0 h1
  have hLpos : (0 : ℝ) < ‖logAux s‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_logAux h0 h1')
  have hL : ‖logAux s‖ ≤ 3 * (1 + Real.log |s.im|) := norm_logAux_le h0 h1' ht
  have hnorm : ‖gLeft s‖ = ‖riemannZeta s‖ * ‖expLeft s‖ / ‖logAux s‖ := by
    rw [gLeft, norm_div, norm_mul]
  have hexpge := norm_expLeft_ge h0 h1 ht
  have hpowpos : (0 : ℝ) < |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) := Real.rpow_pos_of_pos hT0 _
  have hcancel : |s.im| ^ (-(1 / 2 - 2 * s.re / 3)) * |s.im| ^ (1 / 2 - 2 * s.re / 3) = 1 := by
    rw [← Real.rpow_add hT0]
    simp
  -- from the Phragmén–Lindelöf bound, `‖ζ‖ ‖exp‖ ≤ C ‖log u‖`
  have hkey : ‖riemannZeta s‖ * ‖expLeft s‖ ≤ C * ‖logAux s‖ := by
    rw [hnorm, div_le_iff₀ hLpos] at hPL
    exact hPL
  have hstep : ‖riemannZeta s‖ * (Real.exp (-(Real.pi / 6)) / 2
      * |s.im| ^ (-(1 / 2 - 2 * s.re / 3))) ≤ C * (3 * (1 + Real.log |s.im|)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hexpge (norm_nonneg _)) ?_
    refine hkey.trans ?_
    exact mul_le_mul_of_nonneg_left hL hCpos.le
  have hexp0 : (0 : ℝ) < Real.exp (-(Real.pi / 6)) / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hstep
    (le_of_lt (Real.rpow_pos_of_pos hT0 (1 / 2 - 2 * s.re / 3)))
  have hrw : ‖riemannZeta s‖ * (Real.exp (-(Real.pi / 6)) / 2
      * |s.im| ^ (-(1 / 2 - 2 * s.re / 3))) * |s.im| ^ (1 / 2 - 2 * s.re / 3)
      = (Real.exp (-(Real.pi / 6)) / 2) * ‖riemannZeta s‖
        * (|s.im| ^ (-(1 / 2 - 2 * s.re / 3)) * |s.im| ^ (1 / 2 - 2 * s.re / 3)) := by
    ring
  rw [hrw, hcancel, mul_one] at hmul
  -- `hmul : e^(-π/6)/2 * ‖ζ s‖ ≤ C (3 (1 + log|t|)) |t|^(1/2 - 2σ/3)`
  have hinv : Real.exp (-(Real.pi / 6)) * Real.exp (Real.pi / 6) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpow0 : (0 : ℝ) ≤ |s.im| ^ (1 / 2 - 2 * s.re / 3) :=
    (Real.rpow_pos_of_pos hT0 _).le
  have hgoal := mul_le_mul_of_nonneg_left hmul
    (le_of_lt (Real.exp_pos (Real.pi / 6)))
  have hlhs : Real.exp (Real.pi / 6) * (Real.exp (-(Real.pi / 6)) / 2 * ‖riemannZeta s‖)
      = ‖riemannZeta s‖ / 2 := by
    field_simp
    nlinarith [hinv, norm_nonneg (riemannZeta s)]
  rw [hlhs] at hgoal
  have hfinal : ‖riemannZeta s‖
      ≤ 2 * Real.exp (Real.pi / 6) * (C * (3 * (1 + Real.log |s.im|)))
        * |s.im| ^ (1 / 2 - 2 * s.re / 3) := by
    nlinarith [hgoal]
  refine hfinal.trans (le_of_eq ?_)
  ring

end RiemannHypothesis

end
