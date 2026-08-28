/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ArgumentBacklund
import RiemannHypothesis.ZeroCountRadii
import RiemannHypothesis.StripGrowth

/-!
# `S(t) = O(log t)`: the variation of the argument of `ζ` along a horizontal segment

This file bounds the two horizontal argument terms left open by
`RiemannHypothesis.LittlewoodZetaBound`, by Backlund's classical argument.

Let `T` be large and let `θ` be a continuous branch of the argument of `ζ` along the horizontal
segment from `u + iT` to `3 + iT` (`1/2 ≤ u ≤ 3`).  Since `ζ = ‖ζ‖ e^{iθ}`, the cosine of `θ`
vanishes exactly where `re ζ` does, so `abs_sub_le_of_ncard_cos_eq_zero` bounds the variation of
`θ` by `(n + 1) π`, where `n` is the number of zeroes of `re ζ` on the segment.  Those zeroes are
counted by Jensen's inequality applied to the *reflected* function

`zetaRefl T z = (ζ(z) + ζ(z − 2iT)) / 2`,

which is analytic near `3 + iT`, equals `re ζ` on the line `im s = T` (because
`ζ(s̄) = conj ζ(s)`), equals `re ζ(3 + iT) ≥ 1/2` at the centre, and is `O(T²)` on the circle of
radius `14/5` about `3 + iT` — a circle that stays inside the half-plane `re s ≥ 1/5`, where the
convexity bound of `RiemannHypothesis.StripGrowth` applies.

## Main results

* `norm_riemannZeta_le_sq_of_tenth_le_re` — `‖ζ(s)‖ ≤ 80 (im s)²` for `re s ≥ 1/10` and
  `|im s| ≥ 3`.
* `zetaRefl`, `zetaRefl_horizontal` — the reflected function and the fact that it computes
  `re ζ` on the horizontal line.
* `exists_ncard_re_riemannZeta_eq_zero_le` — the number of zeroes of `x ↦ re ζ(x + iT)` on
  `[1/2, 3]` is `O(log T)`.
* `exists_abs_im_HIntegral_logDeriv_riemannZeta_le` — **the `S(t) = O(log t)` bound in the form
  needed here**: `|im (HIntegral (ζ′/ζ) u 3 T)| ≤ C log T`, uniformly in `u ∈ [1/2, 3]`, whenever
  `ζ` does not vanish on the segment.
-/

noncomputable section

open Complex Real Set Metric Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

/-! ## A crude polynomial bound for `ζ` to the right of `re s = 1/10` -/

/-- **A polynomial bound for `ζ` on `re s ≥ 1/10`.**  For `|im s| ≥ 3` one has
`‖ζ(s)‖ ≤ 80 (im s)²`.  Inside the strip this is the convexity bound of
`RiemannHypothesis.StripGrowth`, wastefully rounded off. -/
theorem norm_riemannZeta_le_sq_of_tenth_le_re {s : ℂ} (h : 1 / 10 ≤ s.re) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 80 * s.im ^ 2 := by
  have habs : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
  have ht0 : (0 : ℝ) < |s.im| := by linarith
  have hlog : Real.log |s.im| ≤ |s.im| - 1 := Real.log_le_sub_one_of_pos ht0
  rcases le_or_gt s.re 1 with hre1 | hre1
  · have hb := norm_riemannZeta_le_strip (s := s) (by linarith) hre1 ht
    have h1 : 8 / s.re ≤ 80 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h2 : |s.im| ^ (1 - s.re) ≤ |s.im| := by
      calc |s.im| ^ (1 - s.re) ≤ |s.im| ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = |s.im| := Real.rpow_one _
    have h3 : 1 + Real.log |s.im| ≤ |s.im| := by linarith
    have h4 : (0 : ℝ) ≤ |s.im| ^ (1 - s.re) := Real.rpow_nonneg (le_of_lt ht0) _
    have h5 : (0 : ℝ) ≤ 1 + Real.log |s.im| := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ |s.im|)
      linarith
    calc ‖riemannZeta s‖ ≤ 8 / s.re * |s.im| ^ (1 - s.re) * (1 + Real.log |s.im|) := hb
      _ ≤ 80 * |s.im| * |s.im| := by
          apply mul_le_mul (mul_le_mul h1 h2 h4 (by norm_num)) h3 h5 (by positivity)
      _ = 80 * s.im ^ 2 := by rw [← habs]; ring
  · rcases le_or_gt s.re 2 with hre2 | hre2
    · have hb := norm_riemannZeta_le_log (s := s) (by linarith) hre2 (by linarith)
      have h1 : Real.log (1 + |s.im|) ≤ |s.im| := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + |s.im| by linarith)
        linarith
      have h2 : (6 : ℝ) + |s.im| ≤ 80 * s.im ^ 2 := by nlinarith
      linarith
    · have hb := norm_riemannZeta_le_two_of_two_le_re (s := s) (by linarith)
      nlinarith

/-! ## The reflected function -/

/-- The function `z ↦ (ζ(z) + ζ(z − 2iT)) / 2`, whose restriction to the horizontal line
`im s = T` is the real part of `ζ`. -/
def zetaRefl (T : ℝ) (z : ℂ) : ℂ := (riemannZeta z + riemannZeta (z - 2 * (T : ℂ) * I)) / 2

/-- On the line `im s = T` the reflected function is the real part of `ζ`, because
`ζ(s̄) = conj ζ(s)`. -/
theorem zetaRefl_horizontal (T x : ℝ) :
    zetaRefl T ((x : ℂ) + (T : ℂ) * I) = ((riemannZeta ((x : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  have hconj : (x : ℂ) + (T : ℂ) * I - 2 * (T : ℂ) * I
      = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
    ring
  rw [zetaRefl, hconj, riemannZeta_conj, Complex.add_conj]
  push_cast
  ring

/-- The reflected function is analytic on a neighbourhood of the closed ball of radius `14/5`
about `3 + iT`: the only singularity of `ζ` is the pole at `1`, and both `1` and `1 + 2iT` are at
distance at least `T` from the centre. -/
theorem analyticOnNhd_zetaRefl {T : ℝ} (hT : 6 ≤ T) :
    AnalyticOnNhd ℂ (zetaRefl T) (closedBall ((3 : ℂ) + (T : ℂ) * I) (14 / 5)) := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  have hre : |z.re - 3| ≤ 14 / 5 := by
    have := Complex.abs_re_le_norm (z - ((3 : ℂ) + (T : ℂ) * I))
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    simp only [Complex.re_ofNat] at this
    norm_num at this
    linarith
  have him : |z.im - T| ≤ 14 / 5 := by
    have := Complex.abs_im_le_norm (z - ((3 : ℂ) + (T : ℂ) * I))
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    simp only [Complex.im_ofNat] at this
    norm_num at this
    linarith
  have habs := abs_le.1 him
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at habs
    simp at habs
    linarith [habs.1]
  have hz2 : z - 2 * (T : ℂ) * I ≠ 1 := by
    intro h
    have : z = 1 + 2 * (T : ℂ) * I := by linear_combination h
    rw [this] at habs
    simp at habs
    linarith [habs.2]
  have hzeta : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ riemannZeta w := fun w hw =>
    DifferentiableOn.analyticAt (s := {u : ℂ | u ≠ 1})
      (fun u hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
      (isOpen_ne.mem_nhds hw)
  have ha1 : AnalyticAt ℂ riemannZeta z := hzeta z hz1
  have ha2 : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w - 2 * (T : ℂ) * I)) z := by
    have hshift : AnalyticAt ℂ (fun w : ℂ => w - 2 * (T : ℂ) * I) z := by fun_prop
    exact AnalyticAt.comp (g := riemannZeta) (f := fun w : ℂ => w - 2 * (T : ℂ) * I)
      (hzeta _ hz2) hshift
  change AnalyticAt ℂ (fun w : ℂ => (riemannZeta w + riemannZeta (w - 2 * (T : ℂ) * I)) / 2) z
  exact (ha1.add ha2).div_const

/-- On the circle of radius `14/5` about `3 + iT` the reflected function is `O(T²)`. -/
theorem norm_zetaRefl_le {T : ℝ} (hT : 6 ≤ T) {z : ℂ}
    (hz : z ∈ sphere ((3 : ℂ) + (T : ℂ) * I) (14 / 5)) :
    ‖zetaRefl T z‖ ≤ 80 * (T + 3) ^ 2 := by
  rw [mem_sphere, Complex.dist_eq] at hz
  have hnorm : ‖z - ((3 : ℂ) + (T : ℂ) * I)‖ = 14 / 5 := hz
  have hre : |z.re - 3| ≤ 14 / 5 := by
    have := Complex.abs_re_le_norm (z - ((3 : ℂ) + (T : ℂ) * I))
    rw [hnorm] at this
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    simp only [Complex.re_ofNat] at this
    norm_num at this
    linarith
  have him : |z.im - T| ≤ 14 / 5 := by
    have := Complex.abs_im_le_norm (z - ((3 : ℂ) + (T : ℂ) * I))
    rw [hnorm] at this
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    simp only [Complex.im_ofNat] at this
    norm_num at this
    linarith
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  -- the first term
  have h1 : ‖riemannZeta z‖ ≤ 80 * (T + 3) ^ 2 := by
    have hb := norm_riemannZeta_le_sq_of_tenth_le_re (s := z) (by linarith [hre'.1])
      (by rw [abs_of_pos (by linarith [him'.1])]; linarith [him'.1])
    nlinarith [him'.1, him'.2, hb]
  -- the reflected term
  have h2 : ‖riemannZeta (z - 2 * (T : ℂ) * I)‖ ≤ 80 * (T + 3) ^ 2 := by
    have hre2 : (z - 2 * (T : ℂ) * I).re = z.re := by simp
    have him2 : (z - 2 * (T : ℂ) * I).im = z.im - 2 * T := by simp
    have hb := norm_riemannZeta_le_sq_of_tenth_le_re (s := z - 2 * (T : ℂ) * I)
      (by rw [hre2]; linarith [hre'.1])
      (by rw [him2, abs_of_nonpos (by linarith [him'.2])]; linarith [him'.2])
    rw [him2] at hb
    nlinarith [him'.1, him'.2, hb]
  rw [zetaRefl, norm_div]
  simp only [Complex.norm_ofNat]
  have := norm_add_le (riemannZeta z) (riemannZeta (z - 2 * (T : ℂ) * I))
  linarith

/-! ## Counting the zeroes of `re ζ` on a horizontal segment -/

/-- **Backlund's count.**  The number of points of `[1/2, 3]` at which `re ζ(x + iT)` vanishes is
`O(log T)`. -/
theorem exists_ncard_re_riemannZeta_eq_zero_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 6 ≤ T →
      ({x : ℝ | x ∈ Icc (1 / 2 : ℝ) 3 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0}.Finite ∧
        ({x : ℝ | x ∈ Icc (1 / 2 : ℝ) 3 ∧
          (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0}.ncard : ℝ) ≤ C * Real.log T) := by
  have hlogratio : 0 < Real.log (28 / 25) := Real.log_pos (by norm_num)
  have hlog80 : 0 < Real.log 80 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := Real.log 80 + 3 * Real.log 2 + 2 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  refine ⟨K / Real.log (28 / 25), by positivity, fun T hT => ?_⟩
  set A : Set ℝ :=
    {x : ℝ | x ∈ Icc (1 / 2 : ℝ) 3 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0} with hA
  set c : ℂ := (3 : ℂ) + (T : ℂ) * I with hcdef
  have hc3 : ((3 : ℝ) : ℂ) + (T : ℂ) * I = c := by rw [hcdef]; push_cast; ring
  have hcre : c.re = 3 := by rw [hcdef]; simp
  have hfc : zetaRefl T c = ((riemannZeta c).re : ℂ) := by
    rw [← hc3]; exact zetaRefl_horizontal T 3
  have hre : 1 / 2 ≤ (riemannZeta c).re :=
    half_le_re_riemannZeta_of_three_le_re (by rw [hcre])
  have hcne : zetaRefl T c ≠ 0 := by
    rw [hfc]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h
    rw [h] at hre
    linarith
  have hnormfc : 1 / 2 ≤ ‖zetaRefl T c‖ := by
    rw [hfc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact hre
  have hM1 : (1 : ℝ) ≤ 80 * (T + 3) ^ 2 := by nlinarith
  have hMbound : ∀ z ∈ sphere c (14 / 5), ‖zetaRefl T z‖ ≤ 80 * (T + 3) ^ 2 := by
    intro z hz
    exact norm_zetaRefl_le hT (by rw [hcdef] at hz; exact hz)
  have hanal : AnalyticOnNhd ℂ (zetaRefl T) (closedBall c (14 / 5)) := by
    rw [hcdef]; exact analyticOnNhd_zetaRefl hT
  have hZfin : {z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0}.Finite :=
    finite_setOf_zeros_radii (by norm_num) (by norm_num) hanal hcne hM1 hMbound
  have hZcard : ({z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0}.ncard : ℝ)
      * Real.log ((14 / 5) / (5 / 2)) ≤ Real.log (80 * (T + 3) ^ 2) - Real.log ‖zetaRefl T c‖ :=
    ncard_setOf_zeros_le_radii (by norm_num) (by norm_num) hanal hcne hM1 hMbound
  -- transport the count along `x ↦ x + iT`
  set phi : ℝ → ℂ := fun x => (x : ℂ) + (T : ℂ) * I with hphi
  have hinj : Function.Injective phi := by
    intro x y hxy
    have := congrArg Complex.re hxy
    simpa [hphi] using this
  have hsub : phi '' A ⊆ {z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0} := by
    rintro _ ⟨x, ⟨⟨hx1, hx2⟩, hx0⟩, rfl⟩
    constructor
    · have hval : phi x - c = ((x - 3 : ℝ) : ℂ) := by
        rw [hphi, hcdef]; push_cast; ring
      rw [Complex.dist_eq, hval, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · rw [hphi]
      simp only
      rw [zetaRefl_horizontal T x, hx0]
      simp
  have hAfin : A.Finite := Set.Finite.of_finite_image (hZfin.subset hsub) hinj.injOn
  have hAcard : (A.ncard : ℝ) ≤ ({z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0}.ncard : ℝ) := by
    have h1 : A.ncard = (phi '' A).ncard := (Set.ncard_image_of_injective A hinj).symm
    have h2 : (phi '' A).ncard ≤ {z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0}.ncard :=
      Set.ncard_le_ncard hsub hZfin
    rw [h1]
    exact_mod_cast h2
  refine ⟨hAfin, ?_⟩
  -- arithmetic: `log (80 (T+3)²) + log 2 ≤ K log T`
  have hlogT : 1 ≤ Real.log T := by
    have hexp : Real.exp 1 ≤ T := by
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hexp
  have hratio : Real.log ((14 / 5) / (5 / 2)) = Real.log (28 / 25) := by norm_num
  have hlogfc : -Real.log 2 ≤ Real.log ‖zetaRefl T c‖ := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1 / 2) hnormfc
    have e : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [e] at h
    exact h
  have hlogM : Real.log (80 * (T + 3) ^ 2) ≤ Real.log 80 + 2 * (Real.log 2 + Real.log T) := by
    have hTpos : (0 : ℝ) < T := by linarith
    have h1 : Real.log (80 * (T + 3) ^ 2) = Real.log 80 + 2 * Real.log (T + 3) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h2 : Real.log (T + 3) ≤ Real.log (2 * T) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (2 * T) = Real.log 2 + Real.log T :=
      Real.log_mul (by norm_num) (by positivity)
    rw [h1]
    rw [h3] at h2
    linarith
  have hfinal : (A.ncard : ℝ) * Real.log (28 / 25) ≤ K * Real.log T := by
    have h := hZcard
    rw [hratio] at h
    have h1 : (A.ncard : ℝ) * Real.log (28 / 25)
        ≤ ({z : ℂ | dist z c ≤ 5 / 2 ∧ zetaRefl T z = 0}.ncard : ℝ) * Real.log (28 / 25) :=
      mul_le_mul_of_nonneg_right hAcard hlogratio.le
    have h2 : Real.log (80 * (T + 3) ^ 2) - Real.log ‖zetaRefl T c‖ ≤ K * Real.log T := by
      rw [hK]
      nlinarith [hlogM, hlogfc, hlogT, hlog80, hlog2]
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hlogratio]
  exact hfinal

/-! ## The variation of the argument -/

/-- **`S(t) = O(log t)`, in the form needed for Littlewood's lemma.**  If `ζ` does not vanish on
the horizontal segment from `u + iT` to `3 + iT`, the variation of its argument along that
segment — the imaginary part of the integral of `ζ′/ζ` — is `O(log T)`, uniformly in
`u ∈ [1/2, 3]`. -/
theorem exists_abs_im_HIntegral_logDeriv_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 6 ≤ T → ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 →
      (∀ x ∈ [[u, (3 : ℝ)]], riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |(HIntegral (logDeriv riemannZeta) u 3 T).im| ≤ C * Real.log T := by
  obtain ⟨C₀, hC₀, hcount⟩ := exists_ncard_re_riemannZeta_eq_zero_le
  have hpi : 0 < π := Real.pi_pos
  refine ⟨(C₀ + 2) * π, by positivity, fun T hT u hu hu3 hne => ?_⟩
  have hlogT : 1 ≤ Real.log T := by
    have hexp : Real.exp 1 ≤ T := by
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hexp
  have huIcc : [[u, (3 : ℝ)]] = Icc u 3 := uIcc_of_le hu3
  -- a continuous branch of the argument along the segment
  have hanal : ∀ x ∈ [[u, (3 : ℝ)]], AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
    intro x _
    have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    exact DifferentiableOn.analyticAt (s := {w : ℂ | w ≠ 1})
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      (isOpen_ne.mem_nhds hne1)
  obtain ⟨theta, hcont, hpolar, hint⟩ := exists_continuousOn_arg_horizontal hanal hne
  -- the cosine of the argument vanishes exactly where the real part of `ζ` does
  have hcos : ∀ x ∈ [[u, (3 : ℝ)]],
      (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re
        = ‖riemannZeta ((x : ℂ) + (T : ℂ) * I)‖ * Real.cos (theta x) := by
    intro x hx
    conv_lhs => rw [hpolar x hx]
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re]
  obtain ⟨hAfin, hAcard⟩ := hcount T hT
  set A : Set ℝ :=
    {x : ℝ | x ∈ Icc (1 / 2 : ℝ) 3 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0} with hA
  set S : Set ℝ := {x ∈ Ioc u 3 | Real.cos (theta x) = 0} with hS
  have hSsub : S ⊆ A := by
    intro x hx
    obtain ⟨⟨hx1, hx2⟩, hx0⟩ := hx
    have hmem : x ∈ [[u, (3 : ℝ)]] := by
      rw [huIcc]; exact ⟨hx1.le, hx2⟩
    refine ⟨⟨by linarith, hx2⟩, ?_⟩
    rw [hcos x hmem, hx0, mul_zero]
  have hSfin : S.Finite := hAfin.subset hSsub
  have hScard : (S.ncard : ℝ) ≤ C₀ * Real.log T :=
    le_trans (by exact_mod_cast Set.ncard_le_ncard hSsub hAfin) hAcard
  -- Backlund's bound
  set n : ℕ := ⌈C₀ * Real.log T⌉₊ with hn
  have hSn : S.ncard ≤ n := by
    have h1 : (S.ncard : ℝ) ≤ (n : ℝ) := le_trans hScard (Nat.le_ceil _)
    exact_mod_cast h1
  have hbound := abs_sub_le_of_ncard_cos_eq_zero (theta := theta) n u 3 hu3
    (by rw [← huIcc]; exact hcont) hSfin hSn
  rw [hint u left_mem_uIcc 3 right_mem_uIcc] at hbound
  -- and the numerical clean-up
  have hceil : (n : ℝ) ≤ C₀ * Real.log T + 1 := by
    have := Nat.ceil_lt_add_one (a := C₀ * Real.log T) (by positivity)
    linarith
  have h2 : (2 : ℝ) ≤ 2 * Real.log T := by linarith
  have hmono : ((n : ℝ) + 1) * π ≤ (C₀ + 2) * π * Real.log T := by
    have hstep : (n : ℝ) + 1 ≤ (C₀ + 2) * Real.log T := by nlinarith
    nlinarith
  exact le_trans hbound hmono

end RiemannHypothesis
