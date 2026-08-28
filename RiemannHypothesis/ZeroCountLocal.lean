/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.GammaVertical
import RiemannHypothesis.ZeroCount

/-!
# The local Riemann–von Mangoldt bound `N(T+1) - N(T) = O(log T)`

`RiemannHypothesis.ZeroCount` bounds the *total* number of zeroes of `ζ` in the critical strip up
to height `T` by `C T log T`, by applying the counting lemma once, on a disc of radius comparable
to `T`.  That argument cannot see the finer structure: the zeroes near a single height `T` are far
fewer, only `O(log T)` of them, and this is the local form of the Riemann–von Mangoldt formula.

The extra input is the exponential decay of the `Γ`-factor on vertical lines, proved in
`RiemannHypothesis.GammaVertical`.  On a disc of *bounded* radius about `4 + i T` both

* the upper bound `‖ξ(s)‖ ≤ 128 (13 + ‖s‖) ^ 16 e ^ (-π |im s| / 4)`, and
* the lower bound `‖ξ(4 + i T)‖ ≥ e ^ (-π T / 4)`

hold, and their ratio is only polynomial in `T`: the exponential factors cancel.  The counting
lemma then gives `O(log T)` zeroes in that disc, and every zero of `ζ` in the critical strip with
`|im s - T| ≤ 1` lies in it.

## Main results

* `norm_xiFn_le_exp_neg_pi_im` : the sharp-in-`t` upper bound for `ξ` on `1/2 ≤ re s ≤ 24`.
* `exp_le_norm_xiFn_centre` : the matching lower bound at the centre `4 + i T`.
* `ncard_zerosNearHeight_le` : `#{ρ : ζ(ρ) = 0, 0 < re ρ < 1, |im ρ - T| ≤ 1} ≤ C log T`.
-/

noncomputable section

open Complex Metric

namespace RiemannHypothesis

/-! ## A lower bound for `ζ` in the half-plane of absolute convergence -/

/-- For `re s ≥ 3` the Dirichlet series of `ζ` is dominated by its first term:
`‖ζ(s) - 1‖ ≤ 1/2`. -/
theorem norm_riemannZeta_sub_one_le_half_of_three_le_re {s : ℂ} (hs : 3 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 1 / 2 := by
  have hre : 1 < s.re := by linarith
  set g : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hg
  set G : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-s.re) with hG
  have hnorm : ∀ n : ℕ, ‖g n‖ = G n := by
    intro n
    rw [hg, hG]
    simp only
    rw [norm_div, norm_one]
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rw [one_div]
  have hGsummable : Summable G := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp_apply, hG]
    push_cast
    ring_nf
  have hnormsummable : Summable (fun n => ‖g n‖) := hGsummable.congr fun n => (hnorm n).symm
  have hsum : Summable g := hnormsummable.of_norm
  have hzeta : riemannZeta s = g 0 + ∑' n : ℕ, g (n + 1) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
    exact hsum.tsum_eq_zero_add
  have hg0 : g 0 = 1 := by simp [hg]
  have hnormtail : Summable (fun n : ℕ => ‖g (n + 1)‖) :=
    hnormsummable.comp_injective (add_left_injective 1)
  have hGtail : ∑' n : ℕ, G (n + 1) = (∑' n : ℕ, G n) - G 0 := by
    have h := hGsummable.tsum_eq_zero_add
    linarith [h]
  have hG0 : G 0 = 1 := by simp [hG]
  have htail : ‖∑' n : ℕ, g (n + 1)‖ ≤ 1 / 2 := by
    refine le_trans (norm_tsum_le_tsum_norm hnormtail) ?_
    have hcongr : ∑' n : ℕ, ‖g (n + 1)‖ = ∑' n : ℕ, G (n + 1) :=
      tsum_congr fun n => hnorm (n + 1)
    rw [hcongr, hGtail, hG0]
    have hb : (∑' n : ℕ, G n) ≤ 1 + 1 / (s.re - 1) := tsum_natAddOne_rpow_neg_le hre
    have hhalf : (1 : ℝ) / (s.re - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  rw [hzeta, hg0]
  simpa using htail

/-- For `re s ≥ 3` the Dirichlet series of `ζ` is dominated by its first term:
`‖ζ(s)‖ ≥ 1/2`. -/
theorem half_le_norm_riemannZeta_of_three_le_re {s : ℂ} (hs : 3 ≤ s.re) :
    1 / 2 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le_half_of_three_le_re hs
  have h2 : ‖(1 : ℂ)‖ - ‖riemannZeta s‖ ≤ ‖(1 : ℂ) - riemannZeta s‖ :=
    norm_sub_norm_le _ _
  rw [norm_sub_rev, norm_one] at h2
  linarith

/-! ## The upper bound for `ξ`, with the exponential decay of the `Γ`-factor -/

/-- `‖Γ_ℝ(s)‖ ≤ ‖Γ(s/2)‖` for `re s ≥ 0`: the factor `π ^ (-s/2)` has modulus at most one. -/
lemma norm_Gammaℝ_le_norm_Gamma {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Gammaℝ s‖ ≤ ‖Complex.Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul]
  have h1 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp
    linarith
  nlinarith [norm_nonneg ((Real.pi : ℂ) ^ (-s / 2)), norm_nonneg (Complex.Gamma (s / 2))]

/-- **The upper bound for `ξ` with exponential decay in `|t|`**, on `1/2 ≤ re s ≤ 24`. -/
theorem norm_xiFn_le_exp_neg_pi_im {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h1 : s.re ≤ 24)
    (ht : 3 ≤ |s.im|) :
    ‖xiFn s‖ ≤ 128 * (12 + ‖s‖) ^ 16 * Real.exp (-(Real.pi * |s.im| / 4)) := by
  have hre0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro hcon; rw [hcon] at hre0; simp at hre0
  have hs1 : s ≠ 1 := by
    intro hcon
    rw [hcon] at ht
    simp at ht
    linarith
  have hu : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  set E : ℝ := Real.exp (-(Real.pi * |s.im| / 4)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- the `Γ`-factor, with its exponential decay
  have hre_half : (s / 2).re = s.re / 2 := by simp
  have hhalf_re : 1 / 4 ≤ (s / 2).re := by rw [hre_half]; linarith
  have hhalf_re' : (s / 2).re ≤ 5 + (7 : ℕ) := by
    rw [hre_half]
    push_cast
    linarith
  have hhalf_im : |(s / 2).im| = |s.im| / 2 := by
    rw [show (s / 2).im = s.im / 2 by simp, abs_div]
    norm_num
  have hhalf_im1 : 1 ≤ |(s / 2).im| := by rw [hhalf_im]; linarith
  have hGdecay := norm_Gamma_le_exp_decay_of_le 7 hhalf_re hhalf_re' hhalf_im1
  rw [hhalf_im] at hGdecay
  have hexp_eq : Real.exp (-(Real.pi * (|s.im| / 2) / 2)) = E := by
    rw [hE]; congr 1; ring
  rw [hexp_eq] at hGdecay
  have hnormhalf : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div]
    norm_num
  rw [hnormhalf] at hGdecay
  have hGamma : ‖Gammaℝ s‖ ≤ 8 * (12 + ‖s‖) ^ 12 * E := by
    refine le_trans (norm_Gammaℝ_le_norm_Gamma hre0.le) (le_trans hGdecay ?_)
    have hb : (5 + ((7 : ℕ) : ℝ) + ‖s‖ / 2) ^ (5 + 7) ≤ (12 + ‖s‖) ^ 12 := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      push_cast
      linarith
    nlinarith [hEpos.le]
  have hzeta : ‖riemannZeta s‖ ≤ 16 * ‖s‖ ^ 2 + 2 :=
    norm_riemannZeta_le_sq h0 (Or.inr ht)
  have hs1norm : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    have h := norm_sub_le s (1 : ℂ)
    simp only [norm_one] at h
    linarith
  rw [xiFn_eq_completed hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul hre0]
  have hsplit : ‖s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s)‖
      = ‖s‖ * ‖s - 1‖ / 2 * (‖Gammaℝ s‖ * ‖riemannZeta s‖) := by simp
  rw [hsplit]
  have hstep : ‖s‖ * ‖s - 1‖ / 2 * (‖Gammaℝ s‖ * ‖riemannZeta s‖)
      ≤ ‖s‖ * (‖s‖ + 1) / 2 * ((8 * (12 + ‖s‖) ^ 12 * E) * (16 * ‖s‖ ^ 2 + 2)) := by
    have hA : ‖s‖ * ‖s - 1‖ / 2 ≤ ‖s‖ * (‖s‖ + 1) / 2 := by nlinarith
    have hB : ‖Gammaℝ s‖ * ‖riemannZeta s‖
        ≤ (8 * (12 + ‖s‖) ^ 12 * E) * (16 * ‖s‖ ^ 2 + 2) :=
      mul_le_mul hGamma hzeta (norm_nonneg _) (by positivity)
    exact mul_le_mul hA hB (by positivity) (by positivity)
  refine le_trans hstep ?_
  have hpoly : ‖s‖ * (‖s‖ + 1) / 2 * (8 * (16 * ‖s‖ ^ 2 + 2)) ≤ 128 * (12 + ‖s‖) ^ 4 := by
    nlinarith [pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, sq_nonneg ‖s‖]
  have hfactor : (12 + ‖s‖) ^ 4 * (12 + ‖s‖) ^ 12 = (12 + ‖s‖) ^ 16 := by ring
  have hcube : 0 ≤ (12 + ‖s‖) ^ 12 := by positivity
  calc ‖s‖ * (‖s‖ + 1) / 2 * ((8 * (12 + ‖s‖) ^ 12 * E) * (16 * ‖s‖ ^ 2 + 2))
      = (‖s‖ * (‖s‖ + 1) / 2 * (8 * (16 * ‖s‖ ^ 2 + 2))) * (12 + ‖s‖) ^ 12 * E := by ring
    _ ≤ (128 * (12 + ‖s‖) ^ 4) * (12 + ‖s‖) ^ 12 * E := by
        have := mul_le_mul_of_nonneg_right hpoly hcube
        nlinarith [hEpos.le]
    _ = 128 * (12 + ‖s‖) ^ 16 * E := by rw [← hfactor]; ring

/-- The same bound on the reflected region `-23 ≤ re s ≤ 24`, by the functional equation. -/
theorem norm_xiFn_le_exp_neg_pi_im' {s : ℂ} (h0 : -23 ≤ s.re) (h1 : s.re ≤ 24)
    (ht : 3 ≤ |s.im|) :
    ‖xiFn s‖ ≤ 128 * (13 + ‖s‖) ^ 16 * Real.exp (-(Real.pi * |s.im| / 4)) := by
  have hEpos : 0 < Real.exp (-(Real.pi * |s.im| / 4)) := Real.exp_pos _
  have hu : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  rcases le_or_gt (1 / 2 : ℝ) s.re with hhalf | hhalf
  · refine le_trans (norm_xiFn_le_exp_neg_pi_im hhalf h1 ht) ?_
    have hb : (12 + ‖s‖) ^ 16 ≤ (13 + ‖s‖) ^ 16 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    nlinarith [hEpos.le]
  · -- use the functional equation `ξ(1 - s) = ξ(s)`
    have hre : (1 - s).re = 1 - s.re := by simp
    have him : (1 - s).im = -s.im := by simp
    have hre0 : 1 / 2 ≤ (1 - s).re := by rw [hre]; linarith
    have hre1 : (1 - s).re ≤ 24 := by rw [hre]; linarith
    have habs : |(1 - s).im| = |s.im| := by rw [him, abs_neg]
    have hbound := norm_xiFn_le_exp_neg_pi_im hre0 hre1 (by rw [habs]; exact ht)
    rw [habs, xiFn_one_sub] at hbound
    refine le_trans hbound ?_
    have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      have h := norm_sub_le (1 : ℂ) s
      simp only [norm_one] at h
      linarith
    have hb : (12 + ‖1 - s‖) ^ 16 ≤ (13 + ‖s‖) ^ 16 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    nlinarith [hEpos.le]

/-! ## The lower bound at the centre -/

/-- **The lower bound at the centre `4 + i T`**: `‖ξ(4 + i T)‖ ≥ e ^ (-π T / 4)` for `T ≥ 25`. -/
theorem exp_le_norm_xiFn_centre {T : ℝ} (hT : 25 ≤ T) :
    Real.exp (-(Real.pi * T / 4)) ≤ ‖xiFn (4 + (T : ℂ) * I)‖ := by
  set c : ℂ := 4 + (T : ℂ) * I with hc
  have hcre : c.re = 4 := by simp [hc]
  have hcim : c.im = T := by simp [hc]
  have hT0 : (0 : ℝ) < T := by linarith
  have hpi := Real.pi_pos
  have hEpos : 0 < Real.exp (-(Real.pi * T / 4)) := Real.exp_pos _
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcre
    simp at hcre
  have hc1 : c ≠ 1 := by
    intro h
    rw [h] at hcre
    simp at hcre
  -- the modulus of `Γ(1 + i T / 2)`
  have hu0 : (T / 2 : ℝ) ≠ 0 := by positivity
  have hGsq := norm_Gamma_one_add_mul_I_sq (t := T / 2) hu0
  have hsinh : Real.sinh (Real.pi * (T / 2)) ≤ Real.exp (Real.pi * (T / 2)) / 2 := by
    rw [Real.sinh_eq]
    have := (Real.exp_pos (-(Real.pi * (T / 2)))).le
    linarith
  have hsinh0 : 0 < Real.sinh (Real.pi * (T / 2)) := by
    have : (0 : ℝ) < Real.pi * (T / 2) := by positivity
    simpa using Real.sinh_lt_sinh.2 this
  have hexp2 : Real.exp (-(Real.pi * T / 4)) ^ 2 = Real.exp (-(Real.pi * (T / 2))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hGlow : Real.exp (-(Real.pi * T / 4)) ≤ ‖Complex.Gamma (1 + ((T / 2 : ℝ) : ℂ) * I)‖ := by
    have hsq : Real.exp (-(Real.pi * T / 4)) ^ 2
        ≤ ‖Complex.Gamma (1 + ((T / 2 : ℝ) : ℂ) * I)‖ ^ 2 := by
      rw [hGsq, hexp2]
      have hkey : Real.exp (-(Real.pi * (T / 2)))
          ≤ Real.pi * (T / 2) / Real.sinh (Real.pi * (T / 2)) := by
        rw [le_div_iff₀ hsinh0, Real.exp_neg]
        have hexppos : 0 < Real.exp (Real.pi * (T / 2)) := Real.exp_pos _
        have h1 : (Real.exp (Real.pi * (T / 2)))⁻¹ * Real.sinh (Real.pi * (T / 2))
            ≤ (Real.exp (Real.pi * (T / 2)))⁻¹ * (Real.exp (Real.pi * (T / 2)) / 2) := by
          apply mul_le_mul_of_nonneg_left hsinh (by positivity)
        have h2 : (Real.exp (Real.pi * (T / 2)))⁻¹ * (Real.exp (Real.pi * (T / 2)) / 2)
            = 1 / 2 := by
          field_simp
        rw [h2] at h1
        have h3 : (1 : ℝ) / 2 ≤ Real.pi * (T / 2) := by nlinarith [Real.pi_gt_three]
        linarith
      exact hkey
    have hnn : 0 ≤ ‖Complex.Gamma (1 + ((T / 2 : ℝ) : ℂ) * I)‖ := norm_nonneg _
    nlinarith [hEpos.le]
  -- pass to `Γ(c/2) = (1 + i T/2) Γ(1 + i T/2)`
  have hchalf : c / 2 = (1 + ((T / 2 : ℝ) : ℂ) * I) + 1 := by
    rw [hc]
    push_cast
    ring
  have hne : (1 : ℂ) + ((T / 2 : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have : ((1 : ℂ) + ((T / 2 : ℝ) : ℂ) * I).re = 0 := by rw [h]; simp
    simp at this
  have hGammahalf : ‖Complex.Gamma (c / 2)‖
      = ‖1 + ((T / 2 : ℝ) : ℂ) * I‖ * ‖Complex.Gamma (1 + ((T / 2 : ℝ) : ℂ) * I)‖ := by
    rw [hchalf, Complex.Gamma_add_one _ hne, norm_mul]
  have hnormone : (T / 2 : ℝ) ≤ ‖1 + ((T / 2 : ℝ) : ℂ) * I‖ := by
    have h := Complex.abs_im_le_norm (1 + ((T / 2 : ℝ) : ℂ) * I)
    have him : (1 + ((T / 2 : ℝ) : ℂ) * I).im = T / 2 := by simp
    rw [him, abs_of_nonneg (by positivity : (0 : ℝ) ≤ T / 2)] at h
    exact h
  have hGammahalf_low : (T / 2) * Real.exp (-(Real.pi * T / 4)) ≤ ‖Complex.Gamma (c / 2)‖ := by
    rw [hGammahalf]
    exact mul_le_mul hnormone hGlow hEpos.le (norm_nonneg _)
  -- the `π`-power factor
  have hpiPow : (1 : ℝ) / 16 ≤ ‖(Real.pi : ℂ) ^ (-c / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-c / 2).re = -2 := by
      simp [hc]
      norm_num
    rw [hre]
    have h : (Real.pi : ℝ) ^ (-2 : ℝ) = 1 / Real.pi ^ (2 : ℕ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg Real.pi_pos.le,
        Real.rpow_natCast]
      field_simp
    rw [h]
    have hpi2 : Real.pi ^ (2 : ℕ) ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hGammaR : (T / 2) * Real.exp (-(Real.pi * T / 4)) / 16 ≤ ‖Gammaℝ c‖ := by
    rw [Gammaℝ_def, norm_mul]
    have h1 : (1 : ℝ) / 16 * ((T / 2) * Real.exp (-(Real.pi * T / 4)))
        ≤ ‖(Real.pi : ℂ) ^ (-c / 2)‖ * ‖Complex.Gamma (c / 2)‖ :=
      mul_le_mul hpiPow hGammahalf_low (by positivity) (norm_nonneg _)
    linarith
  -- the remaining factors
  have hzeta : 1 / 2 ≤ ‖riemannZeta c‖ :=
    half_le_norm_riemannZeta_of_three_le_re (by rw [hcre]; norm_num)
  have hcnorm : T ≤ ‖c‖ := by
    have h := Complex.abs_im_le_norm c
    rw [hcim, abs_of_nonneg hT0.le] at h
    exact h
  have hc1norm : T ≤ ‖c - 1‖ := by
    have h := Complex.abs_im_le_norm (c - 1)
    have him : (c - 1).im = T := by simp [hc]
    rw [him, abs_of_nonneg hT0.le] at h
    exact h
  rw [xiFn_eq_completed hc0 hc1,
    completedRiemannZeta_eq_Gammaℝ_mul (by rw [hcre]; norm_num)]
  have hsplit : ‖c * (c - 1) / 2 * (Gammaℝ c * riemannZeta c)‖
      = ‖c‖ * ‖c - 1‖ / 2 * (‖Gammaℝ c‖ * ‖riemannZeta c‖) := by simp
  rw [hsplit]
  have hA : T * T / 2 ≤ ‖c‖ * ‖c - 1‖ / 2 := by nlinarith [norm_nonneg c, norm_nonneg (c - 1)]
  have hB : ((T / 2) * Real.exp (-(Real.pi * T / 4)) / 16) * (1 / 2)
      ≤ ‖Gammaℝ c‖ * ‖riemannZeta c‖ :=
    mul_le_mul hGammaR hzeta (by norm_num) (norm_nonneg _)
  have hprod : (T * T / 2) * (((T / 2) * Real.exp (-(Real.pi * T / 4)) / 16) * (1 / 2))
      ≤ ‖c‖ * ‖c - 1‖ / 2 * (‖Gammaℝ c‖ * ‖riemannZeta c‖) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  refine le_trans ?_ hprod
  have hcube : (25 : ℝ) * 25 * 25 ≤ T * T * T := by nlinarith
  nlinarith [hEpos.le]

/-! ## The local count -/

/-- The zeroes of `ζ` in the critical strip at height within `1` of `T`. -/
def zerosNearHeight (T : ℝ) : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im - T| ≤ 1}

/-- Such a zero is a zero of `ξ` in the disc of radius `5` about `4 + i T`. -/
lemma zerosNearHeight_subset (T : ℝ) :
    zerosNearHeight T ⊆ {z : ℂ | dist z (4 + (T : ℂ) * I) ≤ 20 / 4 ∧ xiFn z = 0} := by
  intro s hs
  obtain ⟨hzero, h0, h1, hT⟩ := hs
  refine ⟨?_, xiFn_eq_zero_of_zeta h0 h1 hzero⟩
  have hdist : dist s (4 + (T : ℂ) * I) = ‖s - (4 + (T : ℂ) * I)‖ := Complex.dist_eq _ _
  have hre : |(s - (4 + (T : ℂ) * I)).re| ≤ 4 := by
    have hr : (s - (4 + (T : ℂ) * I)).re = s.re - 4 := by simp
    rw [hr, abs_le]
    constructor <;> linarith
  have him : |(s - (4 + (T : ℂ) * I)).im| ≤ 1 := by
    have hi : (s - (4 + (T : ℂ) * I)).im = s.im - T := by simp
    rw [hi]
    exact hT
  have := Complex.norm_le_abs_re_add_abs_im (s - (4 + (T : ℂ) * I))
  rw [hdist]
  linarith

/-- **The disc at height `T`.**  For `T ≥ 25` there is a bound `M` for `ξ` on the circle of
radius `20` about the centre `c = 4 + i T`; the centre value `ξ(c)` is nonzero; and the
logarithmic ratio `log (M / ‖ξ(c)‖)` — the quantity that controls every Jensen-type count in
that disc — is at most `41 log T`. -/
theorem exists_disc_data_near_height {T : ℝ} (hT : 25 ≤ T) :
    ∃ M : ℝ, 0 < M ∧ (∀ z ∈ sphere (4 + (T : ℂ) * I) 20, ‖xiFn z‖ ≤ M) ∧
      xiFn (4 + (T : ℂ) * I) ≠ 0 ∧
      Real.log (M / ‖xiFn (4 + (T : ℂ) * I)‖) ≤ 41 * Real.log T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpi := Real.pi_pos
  set c : ℂ := 4 + (T : ℂ) * I with hc
  have hcre : c.re = 4 := by simp [hc]
  have hcim : c.im = T := by simp [hc]
  have hcnorm : ‖c‖ ≤ 4 + T := by
    have h := Complex.norm_le_abs_re_add_abs_im c
    rw [hcre, hcim, abs_of_nonneg hT0.le] at h
    simpa using h
  set M : ℝ := 128 * (37 + T) ^ 16 * Real.exp (-(Real.pi * (T - 20) / 4)) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  -- the upper bound on the circle of radius `20`
  have hsphere : ∀ z ∈ sphere c 20, ‖xiFn z‖ ≤ M := by
    intro z hz
    have hd : ‖z - c‖ = 20 := by
      have h : dist z c = 20 := hz
      rwa [Complex.dist_eq] at h
    have hre : |(z - c).re| ≤ 20 := by
      have := Complex.abs_re_le_norm (z - c)
      rw [hd] at this; exact this
    have him : |(z - c).im| ≤ 20 := by
      have := Complex.abs_im_le_norm (z - c)
      rw [hd] at this; exact this
    rw [show (z - c).re = z.re - 4 by rw [Complex.sub_re, hcre], abs_le] at hre
    rw [show (z - c).im = z.im - T by rw [Complex.sub_im, hcim], abs_le] at him
    have h0 : (-23 : ℝ) ≤ z.re := by linarith [hre.1]
    have h1 : z.re ≤ 24 := by linarith [hre.2]
    have himabs : T - 20 ≤ |z.im| := le_trans (by linarith [him.1]) (le_abs_self z.im)
    have ht : (3 : ℝ) ≤ |z.im| := by linarith
    have hznorm : ‖z‖ ≤ T + 24 := by
      have h := norm_le_norm_add_norm_sub' z c
      rw [hd] at h
      linarith
    refine le_trans (norm_xiFn_le_exp_neg_pi_im' h0 h1 ht) ?_
    have hb : (13 + ‖z‖) ^ 16 ≤ (37 + T) ^ 16 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hexp : Real.exp (-(Real.pi * |z.im| / 4)) ≤ Real.exp (-(Real.pi * (T - 20) / 4)) := by
      apply Real.exp_le_exp.2
      have : Real.pi * (T - 20) ≤ Real.pi * |z.im| := by nlinarith
      linarith
    rw [hM]
    have h1' : (0 : ℝ) ≤ Real.exp (-(Real.pi * |z.im| / 4)) := (Real.exp_pos _).le
    nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 13 + ‖z‖) 16,
      Real.exp_pos (-(Real.pi * (T - 20) / 4))]
  -- the lower bound at the centre
  have hL : Real.exp (-(Real.pi * T / 4)) ≤ ‖xiFn c‖ := by
    rw [hc]; exact exp_le_norm_xiFn_centre hT
  have hxic : 0 < ‖xiFn c‖ := lt_of_lt_of_le (Real.exp_pos _) hL
  have hcne : xiFn c ≠ 0 := by
    intro h
    rw [h] at hxic
    simp at hxic
  refine ⟨M, hMpos, hsphere, hcne, ?_⟩
  -- estimate the logarithm
  have hlogM : Real.log M
      = Real.log 128 + 16 * Real.log (37 + T) + -(Real.pi * (T - 20) / 4) := by
    rw [hM, Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hratio : Real.log (M / ‖xiFn c‖)
      ≤ Real.log 128 + 16 * Real.log (37 + T) + 5 * Real.pi := by
    have h1 : M / ‖xiFn c‖ ≤ M / Real.exp (-(Real.pi * T / 4)) := by
      gcongr
    have h2 : Real.log (M / ‖xiFn c‖) ≤ Real.log (M / Real.exp (-(Real.pi * T / 4))) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (M / Real.exp (-(Real.pi * T / 4))) = Real.log M + Real.pi * T / 4 := by
      rw [Real.log_div hMpos.ne' (Real.exp_ne_zero _), Real.log_exp]
      ring
    rw [h3, hlogM] at h2
    linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogT3 : (3 : ℝ) ≤ Real.log T := by
    have h25 : (3 : ℝ) ≤ Real.log 25 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h3 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by rw [Real.exp_one_pow]; norm_num
      rw [h3]
      have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
      nlinarith [pow_le_pow_left₀ (Real.exp_pos 1).le he 3]
    exact le_trans h25 (Real.log_le_log (by norm_num) hT)
  have hlog128 : Real.log 128 ≤ 5 := by
    have h : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h]
    linarith [Real.log_two_lt_d9]
  have hlog37 : Real.log (37 + T) ≤ 2 * Real.log T := by
    have h : (37 : ℝ) + T ≤ T ^ 2 := by nlinarith
    have h2 := Real.log_le_log (by linarith) h
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hnum : Real.log (M / ‖xiFn c‖) ≤ 41 * Real.log T := by
    have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  exact hnum

/-- **The local Riemann–von Mangoldt bound.**  The number of zeroes of `ζ` in the critical strip
with `|im s - T| ≤ 1`, counted without multiplicity, is `O(log T)`. -/
theorem ncard_zerosNearHeight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 25 ≤ T → ((zerosNearHeight T).ncard : ℝ) ≤ C * Real.log T := by
  refine ⟨41, by norm_num, ?_⟩
  intro T hT
  obtain ⟨M, hMpos, hsphere, hcne, hnum⟩ := exists_disc_data_near_height hT
  set c : ℂ := 4 + (T : ℂ) * I with hc
  have hcount := ncard_setOf_zeros_le (f := xiFn) (c := c) (R := 20) (M := M) (by norm_num)
    differentiable_xiFn.diffContOnCl hsphere hcne
  have hfin := finite_setOf_zeros (f := xiFn) (c := c) (R := 20) (M := M) (by norm_num)
    differentiable_xiFn.diffContOnCl hsphere hcne
  have hsub : zerosNearHeight T ⊆ {z : ℂ | dist z c ≤ 20 / 4 ∧ xiFn z = 0} := by
    rw [hc]; exact zerosNearHeight_subset T
  have hmono : (zerosNearHeight T).ncard ≤ {z : ℂ | dist z c ≤ 20 / 4 ∧ xiFn z = 0}.ncard :=
    Set.ncard_le_ncard hsub hfin
  have hstep : ((zerosNearHeight T).ncard : ℝ) ≤ Real.log (M / ‖xiFn c‖) / Real.log 3 :=
    le_trans (by exact_mod_cast hmono) hcount
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  refine le_trans hstep ?_
  rcases le_or_gt (Real.log (M / ‖xiFn c‖)) 0 with h | h
  · have hnp : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  · have hle : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ Real.log (M / ‖xiFn c‖) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

end RiemannHypothesis
