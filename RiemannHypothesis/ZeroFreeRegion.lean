/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.NearLine
import RiemannHypothesis.ZeroFree

/-!
# A quantitative zero-free region for `ζ` to the left of the line `re s = 1`

Mathlib's `riemannZeta_ne_zero_of_one_le_re` gives `ζ(s) ≠ 0` for `re s ≥ 1`.  This file
proves a *region*: there is an absolute constant `c > 0` with

`ζ(s) ≠ 0` whenever `|im s| ≥ 4` and `re s > 1 - c / (log |im s|)^9`.

The three ingredients are all proved in this repository:

* the quantitative lower bound `x³/(8(6 + log(1+2|y|))) ≤ ‖ζ(1 + x + iy)‖⁴`
  (`RiemannHypothesis.norm_riemannZeta_pow_four_ge`, from the Mertens `3-4-1` inequality);
* the logarithmic upper bound `‖ζ(s)‖ ≤ 18 log|t|` in a neighbourhood of the line
  (`RiemannHypothesis.norm_riemannZeta_le_log_near_line`);
* Cauchy's estimate, which turns the upper bound into the derivative bound
  `‖ζ'(s)‖ ≤ 288 (log|t|)²` (`norm_deriv_riemannZeta_le_near_line`), and then the mean value
  inequality along a horizontal segment, which transfers the lower bound across the line.

The exponent `9` is what this elementary route gives.  The classical de la Vallée Poussin
region has exponent `1`; reaching it requires the Landau/Borel–Carathéodory estimate for
`ζ'/ζ`, which is not available here (see `RiemannHypothesis.ZeroFreeRegion`, the *statement*
of the classical region, in `RiemannHypothesis.Partial`).
-/

noncomputable section

open Complex Filter

namespace RiemannHypothesis

/-- **Cauchy's estimate for `ζ` near the line `re s = 1`.**  For `|t| ≥ 4` and
`1 - 1/(8 log|t|) ≤ re s ≤ 5/4`, `‖ζ'(s)‖ ≤ 288 (log |t|)²`. -/
theorem norm_deriv_riemannZeta_le_near_line {s : ℂ} (ht : 4 ≤ |s.im|)
    (h1 : 1 - 1 / (8 * Real.log |s.im|) ≤ s.re) (h2 : s.re ≤ 5 / 4) :
    ‖deriv riemannZeta s‖ ≤ 288 * Real.log |s.im| ^ 2 := by
  set t : ℝ := |s.im| with htdef
  set L : ℝ := Real.log t with hLdef
  have hL1 : 1 ≤ L := one_le_log_of_three_le (by linarith)
  have hr0 : (0 : ℝ) < 1 / (8 * L) := by positivity
  set r : ℝ := 1 / (8 * L) with hrdef
  have hrle : r ≤ 1 / 8 := by
    rw [hrdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- every point of the closed ball is in the region of the logarithmic bound
  have hball : ∀ w : ℂ, ‖w - s‖ ≤ r → 3 ≤ |w.im| ∧ 1 - 1 / (2 * Real.log |w.im|) ≤ w.re ∧
      w.re ≤ 2 ∧ ‖riemannZeta w‖ ≤ 36 * L := by
    intro w hw
    have hre : |w.re - s.re| ≤ r := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [Complex.sub_re] at h
      linarith
    have him : |w.im - s.im| ≤ r := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [Complex.sub_im] at h
      linarith
    have himabs : |(|w.im| - t)| ≤ r := by
      rw [htdef]
      exact le_trans (abs_abs_sub_abs_le_abs_sub w.im s.im) him
    have himlow : t - r ≤ |w.im| := by
      have := abs_le.mp himabs
      linarith [this.1]
    have himhigh : |w.im| ≤ t + r := by
      have := abs_le.mp himabs
      linarith [this.2]
    have h3 : 3 ≤ |w.im| := by
      have : r ≤ 1 / 8 := hrle
      linarith
    have hLw1 : 1 ≤ Real.log |w.im| := one_le_log_of_three_le h3
    have hLw2 : Real.log |w.im| ≤ 2 * L := by
      have hle : |w.im| ≤ 2 * t := by
        have : r ≤ 1 / 8 := hrle
        linarith
      calc Real.log |w.im| ≤ Real.log (2 * t) := Real.log_le_log (by linarith) hle
        _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 * L := by
            have : Real.log 2 ≤ 1 := by
              have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            linarith
    have hrew : 1 - 1 / (2 * Real.log |w.im|) ≤ w.re := by
      have hstep : 1 / (2 * Real.log |w.im|) ≥ 1 / (4 * L) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      have hlow : s.re - r ≤ w.re := by
        have := abs_le.mp hre
        linarith [this.1]
      have hquarter : 1 / (4 * L) = r + r := by
        rw [hrdef]
        field_simp
        ring
      linarith
    have hre2 : w.re ≤ 2 := by
      have := abs_le.mp hre
      have : w.re ≤ s.re + r := by linarith [(abs_le.mp hre).2]
      have : r ≤ 1 / 8 := hrle
      linarith
    refine ⟨h3, hrew, hre2, ?_⟩
    calc ‖riemannZeta w‖ ≤ 18 * Real.log |w.im| :=
          norm_riemannZeta_le_log_near_line h3 hrew hre2
      _ ≤ 36 * L := by linarith
  have hne : ∀ w : ℂ, ‖w - s‖ ≤ r → w ≠ 1 := by
    intro w hw hw1
    have h := (hball w hw).1
    rw [hw1] at h
    simp at h
    linarith
  have hdiffcont : DiffContOnCl ℂ riemannZeta (Metric.ball s r) := by
    constructor
    · intro w hw
      refine (differentiableAt_riemannZeta (hne w ?_)).differentiableWithinAt
      have := Metric.mem_ball.mp hw
      rw [Complex.dist_eq] at this
      linarith
    · rw [closure_ball s hr0.ne']
      intro w hw
      have := Metric.mem_closedBall.mp hw
      rw [Complex.dist_eq] at this
      exact (differentiableAt_riemannZeta (hne w this)).continuousAt.continuousWithinAt
  have hsphere : ∀ w ∈ Metric.sphere s r, ‖riemannZeta w‖ ≤ 36 * L := by
    intro w hw
    have hd : dist w s = r := hw
    rw [Complex.dist_eq] at hd
    exact (hball w hd.le).2.2.2
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hdiffcont hsphere
  calc ‖deriv riemannZeta s‖ ≤ 36 * L / r := hcauchy
    _ = 288 * L ^ 2 := by
        rw [hrdef]
        field_simp
        ring

/-- The mean value inequality along the horizontal segment from `s` to `1 + x + i·im s`:
if `ζ(s) = 0`, then `‖ζ(1 + x + i·im s)‖ ≤ 288 (log|t|)² (1 + x - re s)`. -/
theorem norm_riemannZeta_le_of_zero {s : ℂ} {x : ℝ} (ht : 4 ≤ |s.im|)
    (h1 : 1 - 1 / (8 * Real.log |s.im|) ≤ s.re) (h2 : s.re ≤ 1) (hx0 : 0 < x) (hx : x ≤ 1 / 4)
    (hzero : riemannZeta s = 0) :
    ‖riemannZeta (1 + (x : ℂ) + I * (s.im : ℂ))‖
      ≤ 288 * Real.log |s.im| ^ 2 * (1 + x - s.re) := by
  set y : ℝ := s.im with hy
  set w : ℂ := 1 + (x : ℂ) + I * (y : ℂ) with hw
  have hwre : w.re = 1 + x := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hsw : s = (s.re : ℂ) + I * (y : ℂ) := by
    apply Complex.ext <;> simp [hy]
  set S : Set ℂ := segment ℝ s w with hS
  have hmem : ∀ z ∈ S, z.im = y ∧ s.re ≤ z.re ∧ z.re ≤ 1 + x := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, hzdef⟩ := mem_segment_real_comb hz
    have hzim : z.im = y := by
      rw [hzdef]
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hwim, ← hy]
      linear_combination y * hab
    have hzre : z.re = a * s.re + b * (1 + x) := by
      rw [hzdef]
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hwre]
    refine ⟨hzim, ?_, ?_⟩
    · rw [hzre]
      nlinarith [hab, hx0]
    · rw [hzre]
      nlinarith [hab, hx0]
  have hdiff : ∀ z ∈ S, DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    obtain ⟨hzim, hzre1, hzre2⟩ := hmem z hz
    refine differentiableAt_riemannZeta ?_
    intro hz1
    rw [hz1] at hzim
    simp only [Complex.one_im] at hzim
    rw [← hzim] at ht
    simp at ht
    linarith
  have hbound : ∀ z ∈ S, ‖deriv riemannZeta z‖ ≤ 288 * Real.log |y| ^ 2 := by
    intro z hz
    obtain ⟨hzim, hzre1, hzre2⟩ := hmem z hz
    have hzimabs : |z.im| = |y| := by rw [hzim]
    have h := norm_deriv_riemannZeta_le_near_line (s := z) (by rw [hzimabs]; exact ht)
      (by rw [hzimabs]; linarith) (by linarith)
    rwa [hzimabs] at h
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_segment (𝕜 := ℝ) s w) (left_mem_segment ℝ s w) (right_mem_segment ℝ s w)
  rw [hzero, sub_zero] at hmvt
  have hnorm : ‖w - s‖ = 1 + x - s.re := by
    have hws : w - s = ((1 + x - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hw, ← hy]
    rw [hws, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at hmvt
  exact hmvt

/-- **A zero-free region for `ζ` to the left of the line `re s = 1`.**
For `|im s| ≥ 4`, `ζ(s) ≠ 0` whenever `re s > 1 - 2^(-45) / (log |im s|)^9`. -/
theorem riemannZeta_ne_zero_of_near_one {s : ℂ} (ht : 4 ≤ |s.im|)
    (hre : 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 < s.re) : riemannZeta s ≠ 0 := by
  intro hzero
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log |s.im| := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hL]; exact one_le_log_of_three_le (by linarith)
  have hL9 : L ≤ L ^ 9 := by nlinarith [pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 9)]
  rw [← hL] at hre
  -- to the right of the line mathlib already gives the result
  have hlt1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hzero
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (1 / 2 ^ 45 : ℝ) / L ^ 9 := ⟨_, rfl⟩
  have hLpos : (0 : ℝ) < L := by linarith
  have hL9pos : (0 : ℝ) < L ^ 9 := by positivity
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxc : x ≤ 1 / 2 ^ 45 := by
    rw [hxdef, div_le_iff₀ hL9pos]
    nlinarith
  have hxsmall : x ≤ 1 / 4 := by
    have : (1 / 2 ^ 45 : ℝ) ≤ 1 / 4 := by norm_num
    linarith
  have hdelta : 1 - x < s.re := by rw [hxdef]; exact hre
  have hxle8 : x ≤ 1 / (8 * L) := by
    rw [hxdef, div_le_div_iff₀ hL9pos (by positivity)]
    nlinarith
  have hregion : 1 - 1 / (8 * L) ≤ s.re := by linarith
  -- the upper bound coming from the hypothetical zero
  have hup : ‖riemannZeta (1 + (x : ℂ) + I * (s.im : ℂ))‖ ≤ 288 * L ^ 2 * (1 + x - s.re) := by
    have h := norm_riemannZeta_le_of_zero (s := s) (x := x) ht (by rw [← hL]; exact hregion)
      hlt1.le hx0 hxsmall hzero
    rw [← hL] at h
    exact h
  have hup2 : ‖riemannZeta (1 + (x : ℂ) + I * (s.im : ℂ))‖ ≤ 576 * L ^ 2 * x := by
    refine le_trans hup ?_
    have hd : 1 + x - s.re ≤ 2 * x := by linarith
    have : 288 * L ^ 2 * (1 + x - s.re) ≤ 288 * L ^ 2 * (2 * x) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith
  -- the lower bound coming from the Mertens inequality
  have hyabs : 1 ≤ |s.im| := by linarith
  have hlow := norm_riemannZeta_pow_four_ge (x := x) (y := s.im) hx0 (by linarith) hyabs
  have hlognn : 0 ≤ Real.log (1 + 2 * |s.im|) := Real.log_nonneg (by linarith)
  have hlogbd : 8 * (6 + Real.log (1 + 2 * |s.im|)) ≤ 64 * L := by
    have h1 : 1 + 2 * |s.im| ≤ |s.im| ^ 2 := by nlinarith
    have h2 : Real.log (1 + 2 * |s.im|) ≤ 2 * L := by
      calc Real.log (1 + 2 * |s.im|) ≤ Real.log (|s.im| ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * L := by rw [hL, Real.log_pow]; push_cast; ring
    linarith
  have hlow2 : x ^ 3 / (64 * L) ≤ ‖riemannZeta (1 + (x : ℂ) + I * (s.im : ℂ))‖ ^ 4 :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (by linarith) hlogbd) hlow
  -- combine
  have hpow : ‖riemannZeta (1 + (x : ℂ) + I * (s.im : ℂ))‖ ^ 4 ≤ (576 * L ^ 2 * x) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hup2 4
  have hkey : x ^ 3 / (64 * L) ≤ (576 * L ^ 2 * x) ^ 4 := le_trans hlow2 hpow
  have hxpow : (0 : ℝ) < x ^ 3 := by positivity
  have hfinal : 1 ≤ 64 * 576 ^ 4 * L ^ 9 * x := by
    have hexp : (576 * L ^ 2 * x) ^ 4 = 576 ^ 4 * L ^ 8 * x ^ 4 := by ring
    rw [hexp, div_le_iff₀ (by positivity)] at hkey
    have hcancel : 576 ^ 4 * L ^ 8 * x ^ 4 * (64 * L) = (64 * 576 ^ 4 * L ^ 9 * x) * x ^ 3 := by
      ring
    rw [hcancel] at hkey
    exact le_of_mul_le_mul_right (by linarith) hxpow
  have hxval : 64 * 576 ^ 4 * L ^ 9 * x = 64 * 576 ^ 4 * (1 / 2 ^ 45 : ℝ) := by
    rw [hxdef]
    field_simp
  rw [hxval] at hfinal
  norm_num at hfinal

/-- The zero-free region, in the existential form of `RiemannHypothesis.ZeroFreeRegion` but
with `log|t|` replaced by `(log|t|)^9`: there is an absolute constant `c > 0` such that
`ζ(s) ≠ 0` whenever `|im s| ≥ 4` and `re s > 1 - c/(log |im s|)^9`. -/
def ZeroFreeRegionNinth : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 4 ≤ |s.im| → 1 - c / Real.log |s.im| ^ 9 < s.re → riemannZeta s ≠ 0

/-- **The zero-free region with exponent `9` holds**, with the explicit constant `2^(-45)`. -/
theorem zeroFreeRegionNinth : ZeroFreeRegionNinth :=
  ⟨1 / 2 ^ 45, by norm_num, fun _ ht hre => riemannZeta_ne_zero_of_near_one ht hre⟩

end RiemannHypothesis

end
