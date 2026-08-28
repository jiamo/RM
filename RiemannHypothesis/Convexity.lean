/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ImaginaryAxis
import RiemannHypothesis.StripGrowth
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The convexity bound for `ζ` inside the critical strip

This file proves the *convexity* (Lindelöf) bound

`‖ζ(σ + i t)‖ ≤ C_ε |t| ^ ((1 - σ)/2 + ε)`   for `0 ≤ σ ≤ 1`, `|t| ≥ 3`,

for every `ε > 0`.  This is the first exit criterion of the board row `M1-GROWTH`; the
previously available bound inside the strip was the trivial exponent `1 - σ`
(`RiemannHypothesis.norm_riemannZeta_le_strip`).

The proof is the classical Phragmén–Lindelöf interpolation between the two edges of the strip:

* on `re s = 1` the logarithmic bound `‖ζ(1 + i t)‖ ≤ 6 + log(1 + |t|)`
  (`RiemannHypothesis.norm_riemannZeta_le_log`);
* on `re s = 0` the square-root bound `‖ζ(i t)‖ ≤ √(|t|/2π) (6 + log(1 + |t|))`
  (`RiemannHypothesis.norm_riemannZeta_mul_I_le`), obtained from the functional equation with
  the exact modulus of its `Γ`-factor.

The interpolation is applied to

`g(s) = ((s - 1)/(s + 3))² ζ(s) exp(-w(s) log u(s))`,  `u(s) = s(1 - s) + 4`,
`w(s) = (1 - s)/4 + ε/2`,

whose modulus is `≍ |ζ(s)| |t| ^ (-(1-σ)/2 - ε)` at large height: the square of `(s-1)/(s+3)`
removes the pole at `s = 1` (and tends to `1` at large height), and `u` has real part at least
`4` on the closed strip, so the logarithm is the principal branch of an analytic function there.
The hypothesis of Phragmén–Lindelöf that `g` grow at most doubly exponentially is supplied by a
crude bound for `ζ` on the closed strip, itself obtained from the functional equation and the
elementary estimate `‖Γ(s)‖ ≤ Γ(re s)`.

## Main results

* `norm_Gamma_le_Gamma_re` : `‖Γ(s)‖ ≤ Γ(re s)` for `0 < re s`.
* `norm_riemannZeta_le_exp_strip` : the crude bound `‖ζ(s)‖ ≤ 100 e^(π|t|/2) |t|²` on the
  closed strip.
* `norm_riemannZeta_le_convexity` : the convexity bound, for every `ε > 0`.
* `norm_riemannZeta_le_critical_line` : the case `σ = 1/2`, `‖ζ(1/2 + i t)‖ ≤ C |t|^(1/4 + ε)`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## Elementary bounds for the Gamma function -/

/-- `‖Γ(s)‖ ≤ Γ(re s)` for `0 < re s`, directly from Euler's integral. -/
lemma norm_Gamma_le_Gamma_re {s : ℂ} (h : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral h, Complex.GammaIntegral, Real.Gamma_eq_integral h]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp

/-- `Γ ≤ 1` on `[1, 2]`, by log-convexity and `Γ(1) = Γ(2) = 1`. -/
lemma Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hseg : x ∈ segment ℝ (1 : ℝ) 2 := by
    rw [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)]
    exact ⟨h1, h2⟩
  have hle := Real.convexOn_log_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi (0 : ℝ))
    (by norm_num : (2 : ℝ) ∈ Set.Ioi (0 : ℝ)) hseg
  exact (Real.log_nonpos_iff hpos.le).1 (by simpa [Function.comp, Real.Gamma_one] using hle)

/-- `Γ ≤ 2` on `[1/2, 1]`, from `Γ(x) = Γ(x+1)/x`. -/
lemma Gamma_le_two_of_mem_Icc {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) : Real.Gamma x ≤ 2 := by
  have hx0 : x ≠ 0 := by intro h; rw [h] at h1; linarith
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0
  have hle : Real.Gamma (x + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by linarith) (by linarith)
  have hxpos : 0 < x := by linarith
  nlinarith [Real.Gamma_pos_of_pos hxpos]

/-- `‖cos z‖ ≤ e^{|Im z|}`. -/
lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div, norm_ofNat]
  have h1 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h3 := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  rw [h1, h2] at h3
  have hle : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-! ## A crude exponential bound on the closed strip -/

/-- A crude bound for `ζ` on the whole closed critical strip, including the line `re s = 0`,
uniform in `re s`: `‖ζ(s)‖ ≤ 100 e^(π |t| / 2) |t|²` for `0 ≤ re s ≤ 1` and `|t| ≥ 3`.

For `1/2 ≤ re s` this is the trivial bound of `StripGrowth`; for `re s ≤ 1/2` it is the
functional equation, whose `Γ`-factor is bounded by `Γ(1 - re s) ≤ 2` and whose cosine factor
is bounded by `cosh(π t / 2) ≤ e^(π |t| / 2)`. -/
lemma norm_riemannZeta_le_sixteen {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h1 : s.re ≤ 1)
    (ht : 3 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 16 * |s.im| * |s.im| := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlogT : 1 + Real.log |s.im| ≤ |s.im| := by
    have := Real.log_le_sub_one_of_pos hT0
    linarith
  have hlogpos : (0 : ℝ) ≤ 1 + Real.log |s.im| := by
    have : (0 : ℝ) ≤ Real.log |s.im| := Real.log_nonneg hT1
    linarith
  have hpow : |s.im| ^ (1 - s.re) ≤ |s.im| := by
    calc |s.im| ^ (1 - s.re) ≤ |s.im| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = |s.im| := Real.rpow_one _
  have hpowpos : (0 : ℝ) ≤ |s.im| ^ (1 - s.re) := Real.rpow_nonneg hT0.le _
  have hcoef : 8 / s.re ≤ 16 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine (norm_riemannZeta_le_strip (by linarith) h1 ht).trans ?_
  calc 8 / s.re * |s.im| ^ (1 - s.re) * (1 + Real.log |s.im|)
      ≤ 16 * |s.im| * (1 + Real.log |s.im|) := by
        refine mul_le_mul_of_nonneg_right ?_ hlogpos
        exact mul_le_mul hcoef hpow hpowpos (by norm_num)
    _ ≤ 16 * |s.im| * |s.im| := by
        exact mul_le_mul_of_nonneg_left hlogT (by positivity)

theorem norm_riemannZeta_le_exp_strip {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 100 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2 := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi * |s.im| / 2) :=
    Real.one_le_exp (by positivity)
  rcases le_or_gt (1 / 2 : ℝ) s.re with hge | hlt
  · -- the right half of the strip: the trivial bound suffices
    have h := norm_riemannZeta_le_sixteen hge h1 ht
    nlinarith [sq_nonneg |s.im|]
  · -- the left half of the strip: the functional equation
    have hs0 : s.im ≠ 0 := by
      intro hcon
      rw [hcon] at ht
      simp at ht
      linarith
    have hne : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n hcon
      have hre : (1 - s).re = (-(n : ℂ)).re := by rw [hcon]
      simp at hre
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hne1 : (1 - s) ≠ 1 := by
      intro hcon
      have him : (1 - s).im = (1 : ℂ).im := by rw [hcon]
      exact hs0 (by simpa using him)
    have hFE := riemannZeta_one_sub hne hne1
    rw [show (1 : ℂ) - (1 - s) = s by ring] at hFE
    rw [hFE]
    have hbase : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ ≤ 1 := by
      have h : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
      rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith [Real.pi_gt_three]
      · simp
        linarith
    have hgamma : ‖Complex.Gamma (1 - s)‖ ≤ 2 := by
      have hre : (1 - s).re = 1 - s.re := by simp
      refine le_trans (norm_Gamma_le_Gamma_re (by rw [hre]; linarith)) ?_
      rw [hre]
      exact Gamma_le_two_of_mem_Icc (by linarith) (by linarith)
    have him : |(1 - s).im| = |s.im| := by simp
    have hcos : ‖Complex.cos ((Real.pi : ℂ) * (1 - s) / 2)‖
        ≤ Real.exp (Real.pi * |s.im| / 2) := by
      refine le_trans (norm_cos_le_exp_abs_im _) (Real.exp_le_exp.2 ?_)
      have himm : ((Real.pi : ℂ) * (1 - s) / 2).im = -(Real.pi * s.im) / 2 := by
        simp [Complex.mul_im]
      rw [himm, abs_div, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      simp
    have hzeta1 : ‖riemannZeta (1 - s)‖ ≤ 16 * |s.im| * |s.im| := by
      have hre : (1 - s).re = 1 - s.re := by simp
      have h := norm_riemannZeta_le_sixteen (s := 1 - s) (by rw [hre]; linarith)
        (by rw [hre]; linarith) (by rw [him]; exact ht)
      rwa [him] at h
    have hprod : ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s)
        * Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) * riemannZeta (1 - s)‖
        ≤ 2 * 1 * 2 * Real.exp (Real.pi * |s.im| / 2) * (16 * |s.im| * |s.im|) := by
      simp only [norm_mul, Complex.norm_ofNat]
      gcongr
    refine hprod.trans ?_
    nlinarith [sq_nonneg |s.im|, hexp1]

/-! ## The auxiliary function -/

/-- `u(s) = s (1 - s) + 4`; on the closed critical strip its real part is at least `4`. -/
def uAux (s : ℂ) : ℂ := s * (1 - s) + 4

/-- `w(s) = (1 - s)/4 + ε/2`; the exponent used in the interpolation. -/
def wAux (e : ℝ) (s : ℂ) : ℂ := (1 - s) / 4 + (e : ℂ) / 2

/-- The interpolating factor `u(s) ^ (-w(s))`, written through the principal logarithm. -/
def expAux (e : ℝ) (s : ℂ) : ℂ := Complex.exp (-(wAux e s) * Complex.log (uAux s))

/-- The function to which Phragmén–Lindelöf is applied. -/
def gAux (e : ℝ) (s : ℂ) : ℂ := ((s - 1) / (s + 3)) ^ 2 * riemannZeta s * expAux e s

lemma uAux_re (s : ℂ) : (uAux s).re = s.re * (1 - s.re) + s.im ^ 2 + 4 := by
  simp [uAux, Complex.add_re, Complex.mul_re]
  ring

lemma uAux_im (s : ℂ) : (uAux s).im = s.im * (1 - 2 * s.re) := by
  simp [uAux, Complex.add_im, Complex.mul_im]
  ring

lemma uAux_re_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : s.im ^ 2 + 4 ≤ (uAux s).re := by
  rw [uAux_re]
  nlinarith

lemma uAux_ne_zero {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : uAux s ≠ 0 := by
  intro hcon
  have := uAux_re_ge h0 h1
  rw [hcon] at this
  simp at this
  nlinarith [sq_nonneg s.im]

lemma uAux_mem_slitPlane {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : uAux s ∈ Complex.slitPlane := by
  have h := uAux_re_ge h0 h1
  refine Or.inl ?_
  nlinarith [sq_nonneg s.im]

/-- The modulus of the interpolating factor, in closed form. -/
lemma norm_expAux (e : ℝ) (s : ℂ) :
    ‖expAux e s‖ = Real.exp (-((1 - s.re) / 4 + e / 2) * Real.log ‖uAux s‖
      + (-s.im / 4) * Complex.arg (uAux s)) := by
  rw [expAux, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.log_re, Complex.log_im, wAux]

/-- On the closed strip the modulus of `u` is at least `t² + 4`. -/
lemma norm_uAux_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : s.im ^ 2 + 4 ≤ ‖uAux s‖ :=
  le_trans (uAux_re_ge h0 h1) (Complex.re_le_norm _)

/-- At height at least `3` the modulus of `u` is at most `2 t²`. -/
lemma norm_uAux_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    ‖uAux s‖ ≤ 2 * s.im ^ 2 := by
  have hre : |(uAux s).re| ≤ s.im ^ 2 + 4 + 1 := by
    rw [uAux_re, abs_of_nonneg (by nlinarith [sq_nonneg s.im])]
    nlinarith
  have him : |(uAux s).im| ≤ |s.im| := by
    rw [uAux_im, abs_mul]
    have : |1 - 2 * s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg s.im]
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have := Complex.norm_le_abs_re_add_abs_im (uAux s)
  nlinarith [abs_nonneg s.im]

/-- The argument of `u` is small at large height: `|arg u| ≤ (π/2) |t| / ‖u‖`. -/
lemma abs_arg_uAux_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    |Complex.arg (uAux s)| ≤ Real.pi / 2 * (|s.im| / ‖uAux s‖) := by
  have hre : (0 : ℝ) ≤ (uAux s).re := le_trans (by nlinarith [sq_nonneg s.im]) (uAux_re_ge h0 h1)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : |Complex.arg (uAux s)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.2 hre
  have hsin : 2 / Real.pi * |Complex.arg (uAux s)| ≤ Real.sin |Complex.arg (uAux s)| :=
    Real.mul_le_sin (abs_nonneg _) habs
  have hsin' : Real.sin |Complex.arg (uAux s)| = |Real.sin (Complex.arg (uAux s))| := by
    have hle := abs_le.1 habs
    rcases le_or_gt 0 (Complex.arg (uAux s)) with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hle.2, Real.pi_pos]))]
    · have hneg : 0 ≤ Real.sin (-Complex.arg (uAux s)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hle.1, Real.pi_pos])
      rw [Real.sin_neg] at hneg
      rw [abs_of_neg h, Real.sin_neg, abs_of_nonpos (by linarith)]
  have hnorm : 0 < ‖uAux s‖ := by
    have := norm_uAux_ge h0 h1
    nlinarith [sq_nonneg s.im]
  have hval : |Real.sin (Complex.arg (uAux s))| = |(uAux s).im| / ‖uAux s‖ := by
    rw [Complex.sin_arg, abs_div, abs_of_pos hnorm]
  have him : |(uAux s).im| ≤ |s.im| := by
    rw [uAux_im, abs_mul]
    have h : |1 - 2 * s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg s.im]
  have hstep : 2 / Real.pi * |Complex.arg (uAux s)| ≤ |s.im| / ‖uAux s‖ := by
    refine hsin.trans ?_
    rw [hsin', hval]
    gcongr
  calc |Complex.arg (uAux s)|
      = Real.pi / 2 * (2 / Real.pi * |Complex.arg (uAux s)|) := by field_simp
    _ ≤ Real.pi / 2 * (|s.im| / ‖uAux s‖) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- Upper bound for the interpolating factor at large height. -/
lemma norm_expAux_le {e : ℝ} (he : 0 ≤ e) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ht : 3 ≤ |s.im|) :
    ‖expAux e s‖ ≤ Real.exp (Real.pi / 8) * |s.im| ^ (-((1 - s.re) / 2 + e)) := by
  have hT : (0 : ℝ) < |s.im| := by linarith
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hu1 : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1
  have hupos : (0 : ℝ) < ‖uAux s‖ := by nlinarith [sq_nonneg s.im]
  have hA : 0 ≤ (1 - s.re) / 4 + e / 2 := by linarith
  have harg : |(-s.im / 4) * Complex.arg (uAux s)| ≤ Real.pi / 8 := by
    have hb := abs_arg_uAux_le h0 h1
    rw [abs_mul]
    have h1' : |(-s.im / 4)| = |s.im| / 4 := by
      rw [abs_div, abs_neg]
      simp
    rw [h1']
    have hstep : |s.im| / 4 * |Complex.arg (uAux s)|
        ≤ |s.im| / 4 * (Real.pi / 2 * (|s.im| / ‖uAux s‖)) := by
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    refine hstep.trans ?_
    have hle : |s.im| * |s.im| ≤ ‖uAux s‖ := by nlinarith
    have hrw : |s.im| / 4 * (Real.pi / 2 * (|s.im| / ‖uAux s‖))
        = Real.pi / 8 * ((|s.im| * |s.im|) / ‖uAux s‖) := by ring
    rw [hrw, mul_le_iff_le_one_right (by positivity), div_le_one hupos]
    exact hle
  have hlog : Real.log (|s.im| ^ 2) ≤ Real.log ‖uAux s‖ := by
    refine Real.log_le_log (by positivity) ?_
    nlinarith
  rw [norm_expAux]
  have hrpow : |s.im| ^ (-((1 - s.re) / 2 + e))
      = Real.exp (-((1 - s.re) / 4 + e / 2) * Real.log (|s.im| ^ 2)) := by
    rw [Real.rpow_def_of_pos hT, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : (-s.im / 4) * Complex.arg (uAux s) ≤ Real.pi / 8 :=
    le_trans (le_abs_self _) harg
  nlinarith [hlog, hA]

/-- Lower bound for the interpolating factor at large height. -/
lemma norm_expAux_ge {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ht : 3 ≤ |s.im|) :
    Real.exp (-(Real.pi / 8)) / 2 * |s.im| ^ (-((1 - s.re) / 2 + e)) ≤ ‖expAux e s‖ := by
  have hT : (0 : ℝ) < |s.im| := by linarith
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have hu1 : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1
  have hu2 : ‖uAux s‖ ≤ 2 * s.im ^ 2 := norm_uAux_le h0 h1 ht
  have hupos : (0 : ℝ) < ‖uAux s‖ := by nlinarith [sq_nonneg s.im]
  have hA : 0 ≤ (1 - s.re) / 4 + e / 2 := by linarith
  have hA1 : (1 - s.re) / 4 + e / 2 ≤ 1 := by linarith
  have harg : |(-s.im / 4) * Complex.arg (uAux s)| ≤ Real.pi / 8 := by
    have hb := abs_arg_uAux_le h0 h1
    rw [abs_mul]
    have h1' : |(-s.im / 4)| = |s.im| / 4 := by
      rw [abs_div, abs_neg]
      simp
    rw [h1']
    have hstep : |s.im| / 4 * |Complex.arg (uAux s)|
        ≤ |s.im| / 4 * (Real.pi / 2 * (|s.im| / ‖uAux s‖)) := by
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    refine hstep.trans ?_
    have hle : |s.im| * |s.im| ≤ ‖uAux s‖ := by nlinarith
    have hrw : |s.im| / 4 * (Real.pi / 2 * (|s.im| / ‖uAux s‖))
        = Real.pi / 8 * ((|s.im| * |s.im|) / ‖uAux s‖) := by ring
    rw [hrw, mul_le_iff_le_one_right (by positivity), div_le_one hupos]
    exact hle
  have hlog : Real.log ‖uAux s‖ ≤ Real.log 2 + Real.log (|s.im| ^ 2) := by
    have h := Real.log_le_log hupos (by nlinarith : ‖uAux s‖ ≤ 2 * |s.im| ^ 2)
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  rw [norm_expAux]
  have hrpow : |s.im| ^ (-((1 - s.re) / 2 + e))
      = Real.exp (-((1 - s.re) / 4 + e / 2) * Real.log (|s.im| ^ 2)) := by
    rw [Real.rpow_def_of_pos hT, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [hrpow]
  have hhalf : Real.exp (-(Real.pi / 8)) / 2
      = Real.exp (-(Real.pi / 8) - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [hhalf, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : -(Real.pi / 8) ≤ (-s.im / 4) * Complex.arg (uAux s) := by
    have := neg_abs_le ((-s.im / 4) * Complex.arg (uAux s))
    linarith [harg]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hlog, hA, hA1]

/-- A bound for the interpolating factor valid on the whole closed strip. -/
lemma norm_expAux_le_of_le {e : ℝ} (he : 0 ≤ e) {s : ℂ} (h0 : 0 ≤ s.re)
    (h1 : s.re ≤ 1) : ‖expAux e s‖ ≤ Real.exp (Real.pi * |s.im| / 4) := by
  have hu1 : s.im ^ 2 + 4 ≤ ‖uAux s‖ := norm_uAux_ge h0 h1
  have hu4 : (4 : ℝ) ≤ ‖uAux s‖ := by nlinarith [sq_nonneg s.im]
  have hA : 0 ≤ (1 - s.re) / 4 + e / 2 := by linarith
  have hlog : 0 ≤ Real.log ‖uAux s‖ := Real.log_nonneg (by linarith)
  have harg : |Complex.arg (uAux s)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.2 (by nlinarith [sq_nonneg s.im, uAux_re_ge h0 h1])
  rw [norm_expAux]
  refine Real.exp_le_exp.2 ?_
  have h2 : (-s.im / 4) * Complex.arg (uAux s) ≤ Real.pi * |s.im| / 4 := by
    have hb : |(-s.im / 4) * Complex.arg (uAux s)| ≤ |s.im| / 4 * (Real.pi / 2) := by
      rw [abs_mul]
      have h1' : |(-s.im / 4)| = |s.im| / 4 := by
        rw [abs_div, abs_neg]
        simp
      rw [h1']
      exact mul_le_mul_of_nonneg_left harg (by positivity)
    have := le_trans (le_abs_self _) hb
    nlinarith [abs_nonneg s.im, Real.pi_pos]
  nlinarith [hlog, hA]

/-! ## Analyticity -/

lemma differentiableAt_expAux (e : ℝ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    DifferentiableAt ℂ (expAux e) s := by
  have hu : DifferentiableAt ℂ uAux s := by
    unfold uAux
    fun_prop
  have hlog : DifferentiableAt ℂ Complex.log (uAux s) :=
    Complex.differentiableAt_log (uAux_mem_slitPlane h0 h1)
  have hw : DifferentiableAt ℂ (wAux e) s := by
    unfold wAux
    fun_prop
  exact (hw.neg.mul (hlog.comp s hu)).cexp

lemma differentiableAt_gAux (e : ℝ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (hs : s ≠ 1) :
    DifferentiableAt ℂ (gAux e) s := by
  have h3 : s + 3 ≠ 0 := by
    intro hcon
    have : (s + 3).re = 0 := by rw [hcon]; simp
    simp at this
    linarith
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have hden : DifferentiableAt ℂ (fun z : ℂ => z + 3) s := by fun_prop
  exact ((hnum.div hden h3).pow 2).mul (differentiableAt_riemannZeta hs)
    |>.mul (differentiableAt_expAux e h0 h1)

lemma continuousAt_gAux (e : ℝ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ContinuousAt (gAux e) s := by
  rcases eq_or_ne s 1 with rfl | hs
  · -- the pole of `ζ` is cancelled by the double zero of `((s-1)/(s+3))²`
    refine continuousAt_iff_punctured_nhds.mpr ?_
    have hval : gAux e 1 = 0 := by simp [gAux]
    rw [hval]
    have haux : ContinuousAt (fun z : ℂ => (z - 1) / (z + 3) ^ 2 * expAux e z) 1 := by
      refine ContinuousAt.mul ?_
        (differentiableAt_expAux e (by norm_num) (by norm_num)).continuousAt
      have h4 : ((1 : ℂ) + 3) ^ 2 ≠ 0 := by norm_num
      exact (continuousAt_id.sub continuousAt_const).div
        ((continuousAt_id.add continuousAt_const).pow 2) h4
    have hlim : Tendsto (fun z : ℂ => ((z - 1) * riemannZeta z)
        * ((z - 1) / (z + 3) ^ 2 * expAux e z)) (𝓝[≠] (1 : ℂ)) (𝓝 (1 * 0)) := by
      refine riemannZeta_residue_one.mul ?_
      have : ((1 : ℂ) - 1) / ((1 : ℂ) + 3) ^ 2 * expAux e 1 = 0 := by simp
      simpa [this] using (haux.tendsto.mono_left nhdsWithin_le_nhds)
    rw [mul_zero] at hlim
    refine hlim.congr' ?_
    have hne3 : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z + 3 ≠ 0 := by
      have hcont : ContinuousAt (fun z : ℂ => z + 3) 1 := by fun_prop
      exact (hcont.eventually_ne (by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hne3] with z h3
    change (z - 1) * riemannZeta z * ((z - 1) / (z + 3) ^ 2 * expAux e z)
      = ((z - 1) / (z + 3)) ^ 2 * riemannZeta z * expAux e z
    field_simp
  · exact (differentiableAt_gAux e h0 h1 hs).continuousAt

lemma diffContOnCl_gAux (e : ℝ) :
    DiffContOnCl ℂ (gAux e) (Complex.re ⁻¹' Set.Ioo 0 1) := by
  constructor
  · intro s hs
    have hs1 : s ≠ 1 := by
      intro hcon
      have : s.re = 1 := by rw [hcon]; simp
      exact absurd this (ne_of_lt hs.2)
    exact (differentiableAt_gAux e hs.1.le hs.2.le hs1).differentiableWithinAt
  · intro s hs
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hs
    exact (continuousAt_gAux e hs.1 hs.2).continuousWithinAt

/-! ## The boundary bounds and the growth hypothesis -/

/-- The rational factor of `g` has modulus at most one on the closed strip. -/
lemma norm_ratio_sq_le_one {s : ℂ} (h0 : 0 ≤ s.re) :
    ‖((s - 1) / (s + 3)) ^ 2‖ ≤ 1 := by
  have h3 : s + 3 ≠ 0 := by
    intro hcon
    have hre : (s + 3).re = 0 := by rw [hcon]; simp
    simp at hre
    linarith
  have hsq : ‖s - 1‖ ^ 2 ≤ ‖s + 3‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  have hle : ‖s - 1‖ ≤ ‖s + 3‖ := by
    nlinarith [norm_nonneg (s - 1), norm_nonneg (s + 3)]
  have hpos : 0 < ‖s + 3‖ := norm_pos_iff.2 h3
  rw [norm_pow, norm_div]
  have hr : ‖s - 1‖ / ‖s + 3‖ ≤ 1 := (div_le_one hpos).2 hle
  have hr0 : 0 ≤ ‖s - 1‖ / ‖s + 3‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- On the closed strip, `‖g‖` is bounded by a single exponential in `|t|`. -/
lemma norm_gAux_le_exp {e : ℝ} (he : 0 ≤ e) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ht : 3 ≤ |s.im|) :
    ‖gAux e s‖ ≤ 100 * Real.exp (3 * Real.pi * |s.im| / 4) * |s.im| ^ 2 := by
  have hzeta := norm_riemannZeta_le_exp_strip h0 h1 ht
  have hexp := norm_expAux_le_of_le he h0 h1
  have hratio := norm_ratio_sq_le_one h0
  have hcomb : Real.exp (Real.pi * |s.im| / 2) * Real.exp (Real.pi * |s.im| / 4)
      = Real.exp (3 * Real.pi * |s.im| / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [gAux, norm_mul, norm_mul]
  calc ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖ * ‖expAux e s‖
      ≤ 1 * (100 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2)
        * Real.exp (Real.pi * |s.im| / 4) := by
        gcongr
    _ = 100 * (Real.exp (Real.pi * |s.im| / 2) * Real.exp (Real.pi * |s.im| / 4))
        * |s.im| ^ 2 := by ring
    _ = 100 * Real.exp (3 * Real.pi * |s.im| / 4) * |s.im| ^ 2 := by rw [hcomb]

lemma isBigO_gAux {e : ℝ} (he : 0 ≤ e) :
    ∃ c < Real.pi / (1 - 0), ∃ B : ℝ, (gAux e) =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)] fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  refine ⟨1, by rw [sub_zero]; linarith [Real.pi_gt_three], 5, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨100, ?_⟩
  have hmem : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo 0 1), 3 ≤ |z.im| ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 := by
    refine Filter.eventually_inf.2 ⟨{z : ℂ | 3 ≤ |z.im|}, ?_, Complex.re ⁻¹' Set.Ioo 0 1,
      Filter.mem_principal_self _, ?_⟩
    · exact Filter.mem_comap.2 ⟨Set.Ici 3, Filter.Ici_mem_atTop 3, fun z hz => hz⟩
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hz2⟩
  filter_upwards [hmem] with z hz
  obtain ⟨ht, hre⟩ := hz
  have hT0 : (0 : ℝ) < |z.im| := by linarith
  have hg := norm_gAux_le_exp he hre.1.le hre.2.le ht
  have hsq : |z.im| ^ 2 ≤ Real.exp (2 * |z.im|) := by
    have hone : |z.im| ≤ Real.exp |z.im| := by
      have := Real.add_one_le_exp |z.im|
      linarith
    calc |z.im| ^ 2 ≤ Real.exp |z.im| ^ 2 := by
          exact pow_le_pow_left₀ hT0.le hone 2
      _ = Real.exp (2 * |z.im|) := by
          rw [← Real.exp_nsmul]
          norm_num
  have hcomb : Real.exp (3 * Real.pi * |z.im| / 4) * |z.im| ^ 2
      ≤ Real.exp (5 * Real.exp (1 * |z.im|)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hle : |z.im| ≤ Real.exp (1 * |z.im|) := by
      have := Real.add_one_le_exp |z.im|
      rw [one_mul]
      linarith
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hstep : 3 * Real.pi * |z.im| / 4 + 2 * |z.im| ≤ 5 * |z.im| := by nlinarith
    linarith
  calc ‖gAux e z‖ ≤ 100 * Real.exp (3 * Real.pi * |z.im| / 4) * |z.im| ^ 2 := hg
    _ = 100 * (Real.exp (3 * Real.pi * |z.im| / 4) * |z.im| ^ 2) := by ring
    _ ≤ 100 * Real.exp (5 * Real.exp (1 * |z.im|)) := by linarith
    _ = 100 * ‖Real.exp (5 * Real.exp (1 * |z.im|))‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- On either edge of the strip, `ζ` obeys the boundary bound with the convexity exponent:
the logarithmic bound on `re s = 1` and the square-root bound on `re s = 0`. -/
lemma norm_riemannZeta_le_boundary {s : ℂ} (hs : s.re = 0 ∨ s.re = 1) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ |s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|)) := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hlogpos : 0 ≤ 6 + Real.log (1 + |s.im|) := by
    have : (0 : ℝ) ≤ Real.log (1 + |s.im|) := Real.log_nonneg (by linarith)
    linarith
  rcases hs with h0 | h1
  · have hs' : s = ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [h0]
    have h := norm_riemannZeta_mul_I_le (t := s.im) (by linarith)
    rw [← hs'] at h
    refine h.trans ?_
    have hexp : |s.im| ^ ((1 - s.re) / 2) = Real.sqrt |s.im| := by
      rw [h0, Real.sqrt_eq_rpow]
      norm_num
    rw [hexp]
    refine mul_le_mul_of_nonneg_right ?_ hlogpos
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  · have hexp : |s.im| ^ ((1 - s.re) / 2) = 1 := by
      rw [h1]
      norm_num
    rw [hexp, one_mul]
    exact norm_riemannZeta_le_log (by rw [h1]) (by rw [h1]; norm_num) (by linarith)

/-- At large height the two edges of the strip give a bound for `‖g‖` depending only on `ε`. -/
lemma norm_gAux_le_boundary_large {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) {s : ℂ}
    (hs : s.re = 0 ∨ s.re = 1) (ht : 3 ≤ |s.im|) :
    ‖gAux e s‖ ≤ Real.exp (Real.pi / 8) * (6 + 2 / e) := by
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have h0 : 0 ≤ s.re := by rcases hs with h | h <;> simp [h]
  have h1 : s.re ≤ 1 := by rcases hs with h | h <;> simp [h]
  have hzeta := norm_riemannZeta_le_boundary hs ht
  have hexp := norm_expAux_le he.le h0 h1 ht
  have hratio := norm_ratio_sq_le_one h0
  have hlogpos : 0 ≤ 6 + Real.log (1 + |s.im|) := by
    have : (0 : ℝ) ≤ Real.log (1 + |s.im|) := Real.log_nonneg (by linarith)
    linarith
  have hpowmul : |s.im| ^ ((1 - s.re) / 2) * |s.im| ^ (-((1 - s.re) / 2 + e))
      = |s.im| ^ (-e) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have hneg : |s.im| ^ (-e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT1 (by linarith)
  have hnegpos : (0 : ℝ) < |s.im| ^ (-e) := Real.rpow_pos_of_pos hT0 _
  have hlogle : Real.log (1 + |s.im|) ≤ 2 * |s.im| ^ e / e := by
    have hb := Real.log_le_rpow_div (x := 1 + |s.im|) (by linarith) he
    refine hb.trans ?_
    have hmul : (1 + |s.im|) ^ e ≤ 2 * |s.im| ^ e := by
      have h2 : (1 + |s.im|) ^ e ≤ (2 * |s.im|) ^ e :=
        Real.rpow_le_rpow (by linarith) (by linarith) he.le
      have h3 : (2 * |s.im|) ^ e = (2 : ℝ) ^ e * |s.im| ^ e :=
        Real.mul_rpow (by norm_num) hT0.le
      have h4 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
      rw [Real.rpow_one] at h4
      have h5 : (0 : ℝ) < |s.im| ^ e := Real.rpow_pos_of_pos hT0 _
      nlinarith
    exact div_le_div_of_nonneg_right hmul he.le
  have hkey : (6 + Real.log (1 + |s.im|)) * |s.im| ^ (-e) ≤ 6 + 2 / e := by
    have hcancel : |s.im| ^ e * |s.im| ^ (-e) = 1 := by
      rw [← Real.rpow_add hT0]
      simp
    have hstep : (6 + Real.log (1 + |s.im|)) * |s.im| ^ (-e)
        ≤ (6 + 2 * |s.im| ^ e / e) * |s.im| ^ (-e) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hnegpos.le
    refine hstep.trans ?_
    have hexpand : (6 + 2 * |s.im| ^ e / e) * |s.im| ^ (-e)
        = 6 * |s.im| ^ (-e) + 2 / e * (|s.im| ^ e * |s.im| ^ (-e)) := by
      field_simp
    rw [hexpand, hcancel, mul_one]
    have : 6 * |s.im| ^ (-e) ≤ 6 := by nlinarith
    linarith
  have hb1 : ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖
      ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|))) :=
    mul_le_mul hratio hzeta (norm_nonneg _) zero_le_one
  have hrhs1 : (0 : ℝ) ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|))) := by
    have hnn := Real.rpow_nonneg hT0.le ((1 - s.re) / 2)
    nlinarith
  have hb2 := mul_le_mul hb1 hexp (norm_nonneg _) hrhs1
  rw [gAux, norm_mul, norm_mul]
  calc ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖ * ‖expAux e s‖
      ≤ 1 * (|s.im| ^ ((1 - s.re) / 2) * (6 + Real.log (1 + |s.im|)))
        * (Real.exp (Real.pi / 8) * |s.im| ^ (-((1 - s.re) / 2 + e))) := hb2
    _ = Real.exp (Real.pi / 8) * ((6 + Real.log (1 + |s.im|))
        * (|s.im| ^ ((1 - s.re) / 2) * |s.im| ^ (-((1 - s.re) / 2 + e)))) := by ring
    _ = Real.exp (Real.pi / 8) * ((6 + Real.log (1 + |s.im|)) * |s.im| ^ (-e)) := by
        rw [hpowmul]
    _ ≤ Real.exp (Real.pi / 8) * (6 + 2 / e) := by
        exact mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le

/-- The two edges of the strip: `‖g‖` is bounded there by a constant depending only on `ε`. -/
lemma exists_bound_boundary {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 0 ∨ s.re = 1 → ‖gAux e s‖ ≤ C := by
  classical
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
  have hcont : ContinuousOn (gAux e) K := fun z hz =>
    (continuousAt_gAux e hz.1 hz.2.1).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hcont
  have hpos2 : (0 : ℝ) < Real.exp (Real.pi / 8) * (6 + 2 / e) := by positivity
  refine ⟨max C₁ (Real.exp (Real.pi / 8) * (6 + 2 / e)), ?_, ?_⟩
  · exact lt_of_lt_of_le hpos2 (le_max_right _ _)
  · intro s hs
    have h0 : 0 ≤ s.re := by rcases hs with h | h <;> simp [h]
    have h1 : s.re ≤ 1 := by rcases hs with h | h <;> simp [h]
    rcases le_or_gt |s.im| 3 with hsm | hlg
    · exact (hC₁ s ⟨h0, h1, hsm⟩).trans (le_max_left _ _)
    · exact (norm_gAux_le_boundary_large he he1 hs hlg.le).trans (le_max_right _ _)

/-! ## The convexity bound -/

/-- At large height the rational factor of `g` is bounded below on the closed strip. -/
lemma norm_ratio_sq_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    (9 : ℝ) / 25 ≤ ‖((s - 1) / (s + 3)) ^ 2‖ := by
  have hsq : |s.im| ^ 2 = s.im ^ 2 := sq_abs s.im
  have ht2 : (9 : ℝ) ≤ s.im ^ 2 := by nlinarith
  have h3 : s + 3 ≠ 0 := by
    intro hcon
    have hre : (s + 3).re = 0 := by rw [hcon]; simp
    simp at hre
    linarith
  have hpos : 0 < ‖s + 3‖ := norm_pos_iff.2 h3
  have hkey : 9 * ‖s + 3‖ ^ 2 ≤ 25 * ‖s - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  rw [norm_pow, norm_div, div_pow]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **The convexity bound for `ζ` in the critical strip.**  For every `ε ∈ (0, 1]` there is a
constant `C` with `‖ζ(σ + i t)‖ ≤ C |t| ^ ((1 - σ)/2 + ε)` for `0 ≤ σ ≤ 1` and `|t| ≥ 3`. -/
theorem norm_riemannZeta_le_convexity {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ((1 - s.re) / 2 + e) := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_boundary he he1
  set a : ℝ := 9 / 25 * (Real.exp (-(Real.pi / 8)) / 2) with ha
  have hapos : 0 < a := by
    rw [ha]
    positivity
  refine ⟨C / a, by positivity, ?_⟩
  intro s h0 h1 ht
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hPL : ‖gAux e s‖ ≤ C :=
    PhragmenLindelof.vertical_strip (diffContOnCl_gAux e) (isBigO_gAux he.le)
      (fun z hz => hC z (Or.inl hz)) (fun z hz => hC z (Or.inr hz)) h0 h1
  have hPpos : (0 : ℝ) < |s.im| ^ (-((1 - s.re) / 2 + e)) := Real.rpow_pos_of_pos hT0 _
  have hQpos : (0 : ℝ) < |s.im| ^ ((1 - s.re) / 2 + e) := Real.rpow_pos_of_pos hT0 _
  have hPQ : |s.im| ^ (-((1 - s.re) / 2 + e)) * |s.im| ^ ((1 - s.re) / 2 + e) = 1 := by
    rw [← Real.rpow_add hT0, neg_add_cancel, Real.rpow_zero]
  have hratio_ge := norm_ratio_sq_ge h0 h1 ht
  have hexp_ge := norm_expAux_ge he.le he1 h0 h1 ht
  have hnorm : ‖gAux e s‖
      = ‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖ * ‖expAux e s‖ := by
    rw [gAux, norm_mul, norm_mul]
  have hstep : a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + e)) ≤ C := by
    calc a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + e))
        = (9 / 25 * ‖riemannZeta s‖)
          * (Real.exp (-(Real.pi / 8)) / 2 * |s.im| ^ (-((1 - s.re) / 2 + e))) := by
          rw [ha]; ring
      _ ≤ (‖((s - 1) / (s + 3)) ^ 2‖ * ‖riemannZeta s‖) * ‖expAux e s‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hratio_ge (norm_nonneg _)) hexp_ge
            (mul_nonneg (by positivity) hPpos.le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖gAux e s‖ := hnorm.symm
      _ ≤ C := hPL
  have hfinal : a * ‖riemannZeta s‖ ≤ C * |s.im| ^ ((1 - s.re) / 2 + e) := by
    have hmul := mul_le_mul_of_nonneg_right hstep hQpos.le
    calc a * ‖riemannZeta s‖
        = a * ‖riemannZeta s‖ * (|s.im| ^ (-((1 - s.re) / 2 + e))
            * |s.im| ^ ((1 - s.re) / 2 + e)) := by rw [hPQ]; ring
      _ = a * ‖riemannZeta s‖ * |s.im| ^ (-((1 - s.re) / 2 + e))
            * |s.im| ^ ((1 - s.re) / 2 + e) := by ring
      _ ≤ C * |s.im| ^ ((1 - s.re) / 2 + e) := hmul
  rw [div_mul_eq_mul_div, le_div_iff₀ hapos]
  linarith

/-- The convexity bound on the critical line: `‖ζ(1/2 + i t)‖ ≤ C |t| ^ (1/4 + ε)`. -/
theorem norm_riemannZeta_le_critical_line {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ (1 / 4 + e) := by
  obtain ⟨C, hCpos, hC⟩ := norm_riemannZeta_le_convexity he he1
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
