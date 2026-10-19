/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AFEProof

/-!
# The approximate functional equation on the critical line, proved

This file assembles `RiemannHypothesis.AFEProof` into the statement `AFECriticalLine` of
`RiemannHypothesis.ApproximateFunctionalEquation`, with the explicit constant `250`:

* `AFEProof.norm_afe_error_le_large` — for `t ≥ 200` the error of the approximate functional
  equation is at most `80/√(N + 1/2)`, `N = ⌊√(t/2π)⌋`;
* `AFEProof.norm_afe_error_le_small` — for `2 ≤ t ≤ 200` the error is at most
  `2√t + 13 + 4 t^(1/4)` (Theorem 4.11 at `x = t` and the trivial bound for the two sums);
* `afeCriticalLine` — **`AFECriticalLine 250`**, unconditionally;
* `norm_riemannZeta_criticalLine_le` — **`‖ζ(1/2 + it)‖ ≤ 254 t^(1/4)` for `t ≥ 2`**,
  unconditionally, from `norm_riemannZeta_criticalLine_le_of_afe`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset

namespace RiemannHypothesis.AFEProof

open VanDerCorput Oscillatory ZetaMellinPhase

theorem afe_error_le_of_params {t c : ℝ} {N B : ℕ} (ht : 0 < t) (hN : 5 ≤ N) (hNB : N ≤ B)
    (hc : t = 2 * Real.pi * ((N : ℝ) + 1 / 2) * c) (hcl : (N : ℝ) - 1 ≤ c) (hcu : c ≤ N + 2)
    (hb1 : 1 ≤ (B : ℝ) + 1 / 2) (hbt : 2 * t ≤ 2 * Real.pi * ((B : ℝ) + 1 / 2))
    (h2ab : 2 * ((N : ℝ) + 1 / 2) ≤ (B : ℝ) + 1 / 2) (hBt : t ≤ (B : ℝ) + 1 / 2)
    (h4a : 4 * ((N : ℝ) + 1 / 2) ^ 2 ≤ t) (hsb : t ≤ Real.sqrt ((B : ℝ) + 1 / 2)) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum N (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual N (1 / 2 + (t : ℂ) * I)‖
      ≤ 80 / Real.sqrt ((N : ℝ) + 1 / 2) := by
  have hS := hasSum_Fν t hNB
  have h1 := norm_zeta_sub_zetaSum_sub_le ht hNB hBt hS
    (zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual N (1 / 2 + (t : ℂ) * I))
  have h2 := norm_poisson_sub_main_le ht hN hNB hc hcl hcu hb1 hbt h2ab hS
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 := afe_bound_numeric (c := c) hN rfl h4a (by linarith) hsb
  linarith

theorem norm_afe_error_le_large {t : ℝ} (ht : 200 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 80 / Real.sqrt ((afeLength t : ℝ) + 1 / 2) := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have ht0 : 0 < t := by linarith
  have hpos : 0 < 2 * Real.pi := by positivity
  obtain ⟨x, hx⟩ : ∃ x, x = Real.sqrt (t / (2 * Real.pi)) := ⟨_, rfl⟩
  have hx2 : x ^ 2 = t / (2 * Real.pi) := by rw [hx]; exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.sqrt_nonneg _
  have hAL : afeLength t = ⌊x⌋₊ := by rw [hx]; rfl
  rw [hAL]
  obtain ⟨N, hNdef⟩ : ∃ N, N = ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hNdef]
  have hNx : (N : ℝ) ≤ x := by rw [hNdef]; exact Nat.floor_le hx0
  have hxN : x < N + 1 := by rw [hNdef]; exact Nat.lt_floor_add_one x
  have htx : t = 2 * Real.pi * x ^ 2 := by rw [hx2]; field_simp
  have hx25 : 25 ≤ x ^ 2 := by
    rw [hx2, le_div_iff₀ hpos]; nlinarith
  have hx5 : (5 : ℝ) ≤ x := by nlinarith
  have hN5 : 5 ≤ N := by rw [hNdef]; exact Nat.le_floor (by exact_mod_cast hx5)
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN5
  have hNsq : (N : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hNx 2
  have hxsq : x ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hx0 hxN.le 2
  have ha0 : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  obtain ⟨c, hcdef⟩ : ∃ c, c = t / (2 * Real.pi * ((N : ℝ) + 1 / 2)) := ⟨_, rfl⟩
  have hc : t = 2 * Real.pi * ((N : ℝ) + 1 / 2) * c := by rw [hcdef]; field_simp
  have hcl : (N : ℝ) - 1 ≤ c := by
    rw [hcdef, le_div_iff₀ (by positivity), htx]
    have : ((N : ℝ) - 1) * ((N : ℝ) + 1 / 2) ≤ x ^ 2 := by nlinarith
    nlinarith
  have hcu : c ≤ N + 2 := by
    rw [hcdef, div_le_iff₀ (by positivity), htx]
    have : x ^ 2 ≤ ((N : ℝ) + 2) * ((N : ℝ) + 1 / 2) := by nlinarith
    nlinarith
  -- truncation point
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = ⌈t⌉₊ ^ 2 := ⟨_, rfl⟩
  have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have htt : t ≤ t ^ 2 := by nlinarith
  have hBt2 : t ^ 2 ≤ (B : ℝ) := by
    rw [hB]; push_cast; exact pow_le_pow_left₀ ht0.le hceil 2
  have hxt : x ≤ t := by
    have : x ^ 2 ≤ t ^ 2 := by
      rw [hx2, div_le_iff₀ hpos]; nlinarith
    exact (pow_le_pow_iff_left₀ hx0 ht0.le (by norm_num)).mp this
  have hNB : N ≤ B := by
    have : (N : ℝ) ≤ B := by linarith
    exact_mod_cast this
  have hsb : t ≤ Real.sqrt ((B : ℝ) + 1 / 2) := by
    rw [show t = Real.sqrt (t ^ 2) by rw [Real.sqrt_sq ht0.le]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h4a : 4 * ((N : ℝ) + 1 / 2) ^ 2 ≤ t := by
    have hc0 : 0 ≤ c := by linarith
    have h6 : 6 * ((N : ℝ) + 1 / 2) * c ≤ t := by
      rw [hc]
      have := mul_le_mul_of_nonneg_right (show 6 ≤ 2 * Real.pi by linarith)
        (mul_nonneg ha0.le hc0)
      linarith [mul_assoc (6:ℝ) ((N : ℝ) + 1 / 2) c, mul_assoc (2 * Real.pi) ((N : ℝ) + 1 / 2) c]
    have h7 : 6 * ((N : ℝ) + 1 / 2) * ((N : ℝ) - 1) ≤ 6 * ((N : ℝ) + 1 / 2) * c :=
      mul_le_mul_of_nonneg_left hcl (by positivity)
    nlinarith
  have hb1 : 1 ≤ (B : ℝ) + 1 / 2 := by linarith only [hBt2, htt, ht]
  have hbt : 2 * t ≤ 2 * Real.pi * ((B : ℝ) + 1 / 2) := by
    have h1 : t ≤ (B : ℝ) + 1 / 2 := by linarith only [hBt2, htt]
    have h2 : t ≤ Real.pi * t := le_mul_of_one_le_left ht0.le (by linarith only [hpi3])
    have h3 : Real.pi * t ≤ Real.pi * ((B : ℝ) + 1 / 2) :=
      mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    linarith only [h2, h3]
  have h2ab : 2 * ((N : ℝ) + 1 / 2) ≤ (B : ℝ) + 1 / 2 := by
    have : 2 * t + 1 ≤ t ^ 2 := by nlinarith only [ht]
    linarith only [this, hBt2, hNx, hxt]
  have hBt : t ≤ (B : ℝ) + 1 / 2 := by linarith only [hBt2, htt]
  exact afe_error_le_of_params ht0 hN5 hNB hc hcl hcu hb1 hbt h2ab hBt h4a hsb


/-- For `t > 0`, `80/√(N + 1/2) ≤ 200 t^(-1/4)`, `N = ⌊√(t/2π)⌋`. -/
theorem eighty_div_sqrt_le {t : ℝ} (ht : 0 < t) :
    80 / Real.sqrt ((afeLength t : ℝ) + 1 / 2) ≤ 200 * t ^ (-(1 / 4) : ℝ) := by
  have hpi4 := Real.pi_lt_four
  have hpi3 := Real.pi_gt_three
  obtain ⟨x, hx⟩ : ∃ x, x = Real.sqrt (t / (2 * Real.pi)) := ⟨_, rfl⟩
  have hx2 : x ^ 2 = t / (2 * Real.pi) := by rw [hx]; exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.sqrt_nonneg _
  have hxN : x < (afeLength t : ℝ) + 1 := by
    rw [afeLength, ← hx]; exact Nat.lt_floor_add_one x
  set a : ℝ := (afeLength t : ℝ) + 1 / 2 with ha
  have ha0 : 0 < a := by positivity
  set u : ℝ := t ^ ((1 : ℝ) / 4) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht _
  have hu4 : u ^ 4 = t := by
    rw [hu, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul ht.le]; norm_num
  have hneg : t ^ (-(1 / 4) : ℝ) = 1 / u := by
    rw [hu, Real.rpow_neg ht.le, one_div]; norm_num
  rw [hneg]
  have hxa : x ≤ 2 * a := by linarith
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hu4' : u ^ 4 ≤ 2 * Real.pi * (2 * a) ^ 2 := by
    rw [hu4, show t = 2 * Real.pi * x ^ 2 by rw [hx2]; field_simp]
    have := pow_le_pow_left₀ hx0 hxa 2
    nlinarith
  have hu2 : u ^ 2 ≤ 6 * a := by
    have h1 : (u ^ 2) ^ 2 ≤ (6 * a) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h1
  have hu' : u ≤ (5 / 2) * Real.sqrt a := by
    have h1 : u ^ 2 ≤ ((5 / 2) * Real.sqrt a) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hu0.le (by positivity) (by norm_num)).mp h1
  rw [div_le_iff₀ hsa0]
  rw [show 200 * (1 / u) * Real.sqrt a = 200 * Real.sqrt a / u by ring, le_div_iff₀ hu0]
  nlinarith

/-- For `2 ≤ t`, the trivial bound `‖ζ(1/2+it)‖ ≤ 2√t + 13`, from Theorem 4.11 at `x = t`. -/
theorem norm_riemannZeta_criticalLine_le_small {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * Real.sqrt t + 13 := by
  have ht0 : 0 < t := by linarith
  have h := ZetaPartialSum.norm_riemannZeta_criticalLine_sub_partialSum_le ht0
    (le_of_eq (abs_of_pos ht0))
  have hc : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; ring
  rw [hc] at h
  have hS : ‖∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖ ≤ 2 * Real.sqrt t := by
    have := norm_zetaSum_criticalLine_le ⌊t⌋₊ t
    rw [zetaSum] at this
    refine this.trans ?_
    have : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have := Real.sqrt_le_sqrt this
    linarith
  have hT : ‖(t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (1 / 2 - (t : ℂ) * I).re = 1 / 2 := by simp
    rw [hre, ← Real.sqrt_eq_rpow]
    have him : t ≤ ‖(1 / 2 - (t : ℂ) * I)‖ := by
      have := Complex.abs_im_le_norm (1 / 2 - (t : ℂ) * I)
      rwa [show ((1 : ℂ) / 2 - (t : ℂ) * I).im = -t by simp, abs_neg, abs_of_pos ht0] at this
    rw [div_le_one (by linarith)]
    refine le_trans ?_ him
    have := Real.sqrt_le_sqrt (show t ≤ t ^ 2 by nlinarith)
    rwa [Real.sqrt_sq ht0.le] at this
  have hE : 11 * t ^ (-(1 / 2 : ℝ)) ≤ 11 := by
    have : t ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    linarith
  have key : riemannZeta (1 / 2 + (t : ℂ) * I)
      = (riemannZeta (1 / 2 + (t : ℂ) * I) - ∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
          + (t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I))
        + ∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
        - (t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I) := by ring
  rw [key]
  have h1 := norm_sub_le (riemannZeta (1 / 2 + (t : ℂ) * I)
      - ∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
      + (t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I)
      + ∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)))
    ((t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I))
  have h2 := norm_add_le (riemannZeta (1 / 2 + (t : ℂ) * I)
      - ∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
      + (t : ℂ) ^ (1 / 2 - (t : ℂ) * I) / (1 / 2 - (t : ℂ) * I))
    (∑ n ∈ Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)))
  linarith

/-- For `2 ≤ t`, the error of the approximate functional equation is at most
`2√t + 13 + 4 t^(1/4)` (no cancellation used). -/
theorem norm_afe_error_le_small {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 2 * Real.sqrt t + 13 + 4 * t ^ ((1 : ℝ) / 4) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hS : ‖zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * t ^ ((1 : ℝ) / 4) := by
    refine (norm_zetaSum_criticalLine_le (afeLength t) t).trans ?_
    have := sqrt_afeLength_le ht0.le
    linarith
  have hD : ‖zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 2 * t ^ ((1 : ℝ) / 4) := by
    rw [norm_mul, norm_zetaChi_criticalLine, one_mul, zetaSumDual_criticalLine,
      RCLike.norm_conj]
    exact hS
  have hZ := norm_riemannZeta_criticalLine_le_small ht
  have h1 := norm_sub_le (riemannZeta (1 / 2 + (t : ℂ) * I)
      - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I))
    (zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I))
  have h2 := norm_sub_le (riemannZeta (1 / 2 + (t : ℂ) * I))
    (zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I))
  linarith

end AFEProof

open AFEProof

/-- **The approximate functional equation of Hardy and Littlewood on the critical line**, with
the explicit constant `250`: for every `t ≥ 2`,
`‖ζ(1/2+it) − ∑_{n ≤ x} n^(-1/2-it) − χ(1/2+it) ∑_{n ≤ x} n^(-1/2+it)‖ ≤ 250 t^(-1/4)`,
`x = √(t/2π)`. -/
theorem afeCriticalLine : AFECriticalLine 250 := by
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  rcases le_or_gt 200 t with hbig | hsmall
  · refine (norm_afe_error_le_large hbig).trans ((eighty_div_sqrt_le ht0).trans ?_)
    have := Real.rpow_pos_of_pos ht0 (-(1 / 4) : ℝ)
    nlinarith
  · refine (norm_afe_error_le_small ht).trans ?_
    set u : ℝ := t ^ ((1 : ℝ) / 4) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 _
    have hu4 : u ^ 4 = t := by
      rw [hu, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul ht0.le]; norm_num
    have hneg : t ^ (-(1 / 4) : ℝ) = 1 / u := by
      rw [hu, Real.rpow_neg ht0.le, one_div]; norm_num
    have hsq : Real.sqrt t = u ^ 2 := by
      rw [← hu4, show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hneg, hsq]
    have hu1 : 1 ≤ u := Real.one_le_rpow (by linarith) (by norm_num)
    have hu38 : u ≤ 4 := by
      by_contra h
      push Not at h
      have : (4 : ℝ) ^ 4 < u ^ 4 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
      linarith
    rw [show 250 * (1 / u) = 250 / u by ring, le_div_iff₀ hu0]
    nlinarith

/-- **The convexity bound on the critical line, unconditionally**:
`‖ζ(1/2 + it)‖ ≤ 254 t^(1/4)` for `t ≥ 2`. -/
theorem norm_riemannZeta_criticalLine_le {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ (250 + 4) * t ^ ((1 : ℝ) / 4) :=
  norm_riemannZeta_criticalLine_le_of_afe afeCriticalLine ht

end RiemannHypothesis
