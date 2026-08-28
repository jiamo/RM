/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.DirichletSeriesBounds
import RiemannHypothesis.ZeroCount
import RiemannHypothesis.Partial
import Zeta23.XiPrime.Hardy.ZeroFree

/-!
# The de la Vallée Poussin zero-free region

This file proves `RiemannHypothesis.ZeroFreeRegion`: there is an absolute constant `c > 0` with
`ζ(s) ≠ 0` whenever `|Im s| ≥ 3` and `Re s > 1 - c / log|Im s|`.  This is the classical
exponent-one region of de la Vallée Poussin; the repository previously proved only the weaker
region with `log^9` in the denominator (`RiemannHypothesis.zeroFreeRegionNinth`).

## The argument

Write `f(s) = -Re ζ'/ζ(s)`.  Three inequalities are combined.

* Mertens' `3 - 4 - 1` inequality `0 ≤ 3 f(σ) + 4 f(σ + it) + f(σ + 2it)` for `σ > 1`
  (`RiemannHypothesis.three_four_one`, proved from the Dirichlet series of `Λ`).
* On the real axis, the sharp bound `f(σ) ≤ (1 + o(1))/(σ - 1)`
  (`RiemannHypothesis.negReLogDerivZeta_real_le`).
* Off the real axis, the Hadamard product for the completed zeta function `ξ` gives
  `f(σ + it) ≤ ½ log|t| + C - Σ_ρ Re 1/(s - ρ)`, and every term of the sum over the nontrivial
  zeroes is nonnegative for `σ > 1`.  Dropping all terms gives `f(σ + it) ≤ ½ log|t| + C`;
  keeping the term of a zero `ρ = β + it` at the same height gives
  `f(σ + it) ≤ ½ log|t| + C - 1/(σ - β)`.

The Hadamard input is the vendored `Zeta23` library's `re_logDeriv_xi_eq_tsum`, together with its
Stirling estimates for the archimedean factors (`Zeta23.XiPrime.Hardy.ZeroFree.abs_re_Lm_le` and
the upper bound `re_L2_le` proved below, the companion of that library's `re_L2_ge`).

Feeding the three inequalities into each other at `σ = 1 + δ/log|t|` and choosing `δ` small
gives `β ≤ 1 - c/log|γ|` for every nontrivial zero `ρ = β + iγ` of large ordinate; the finitely
many zeroes of small ordinate are absorbed into the constant, using
`RiemannHypothesis.finite_nontrivialZeros`.
-/

noncomputable section

open Complex Zeta23 Zeta23.XiPrime Zeta23.XiPrime.ZeroFree Zeta23.XiPrime.Hardy.ZeroFree

namespace RiemannHypothesis

/-! ## The archimedean factor -/

/-- Upper companion of `Zeta23`'s `re_digamma_ge`: `Re ψ(z) ≤ log‖z‖ + 4`. -/
private lemma re_digamma_le {z : ℂ} (hz : 0 < z.re) (hi : 1 ≤ |z.im|) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + 4 := by
  have h : |(Complex.digamma z - Complex.log z).re| ≤ 4 :=
    (Complex.abs_re_le_norm _).trans (norm_digamma_sub_log_le hz hi)
  have h' := (abs_le.mp h).2
  rw [Complex.sub_re, Complex.log_re] at h'
  linarith

/-- Upper bound for `Re L₂`, the companion of `Zeta23`'s `re_L2_ge`:
`Re L₂(σ + it) ≤ ½ log|t| + C` for `1 ≤ σ ≤ 2` and `|t| ≥ 4`. -/
lemma re_L2_le : ∃ C : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| →
    (L2 s).re ≤ Real.log |s.im| / 2 + C := by
  refine ⟨3, fun s h1 h2 hi => ?_⟩
  have hs : s.im ≠ 0 := fun h => by rw [h, abs_zero] at hi; linarith
  have habs : 0 < |s.im| := by linarith
  -- a uniform bound on the norm of the two digamma arguments
  have hnorm : ∀ w : ℂ, |w.re| ≤ 2 → |w.im| = |s.im| / 2 → Real.log ‖w‖ ≤ Real.log |s.im| := by
    intro w hwr hwi
    have hle : ‖w‖ ≤ |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [hwi] at this
      linarith
    rcases le_or_gt ‖w‖ 0 with h | h
    · have : ‖w‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [this, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log h hle
  -- first digamma factor
  have hA : (Complex.digamma (s / 2)).re ≤ Real.log |s.im| + 4 := by
    have hzre : (s / 2).re = s.re / 2 := by simp
    have hzim : (s / 2).im = s.im / 2 := by simp
    have hi1 : 1 ≤ |(s / 2).im| := by rw [hzim, abs_div, abs_two]; linarith
    have := re_digamma_le (z := s / 2) (by rw [hzre]; linarith) hi1
    have hb := hnorm (s / 2)
      (by rw [hzre, abs_div, abs_two, abs_of_pos (by linarith : (0:ℝ) < s.re)]; linarith)
      (by rw [hzim, abs_div, abs_two])
    linarith
  -- second digamma factor, after one functional-equation shift
  have hB : (Complex.digamma ((1 - s) / 2)).re ≤ Real.log |s.im| + 4 + 1 / 8 := by
    set z : ℂ := (1 - s) / 2 with hzdef
    have hzre : z.re = (1 - s.re) / 2 := by simp [hzdef]
    have hzim : z.im = -s.im / 2 := by simp [hzdef]
    have hz : z.im ≠ 0 := by rw [hzim]; intro h; apply hs; linarith
    have key := digamma_add_nat_offreal hz 1
    simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at key
    have hw : (1 : ℝ) ≤ |(z + 1).im| := by
      rw [Complex.add_im, Complex.one_im, add_zero, hzim, abs_div, abs_neg, abs_two]; linarith
    have hwre : (z + 1).re = (3 - s.re) / 2 := by rw [Complex.add_re, Complex.one_re, hzre]; ring
    have hup := re_digamma_le (z := z + 1) (by rw [hwre]; linarith) hw
    have hb := hnorm (z + 1)
      (by rw [hwre, abs_of_pos (by linarith : (0:ℝ) < (3 - s.re) / 2)]; linarith)
      (by rw [Complex.add_im, Complex.one_im, add_zero, hzim, abs_div, abs_neg, abs_two])
    -- the correction term is at most 1/8
    have hnsq : 4 ≤ Complex.normSq z := by
      rw [Complex.normSq_apply]
      have h4 : (2:ℝ) ≤ |z.im| := by rw [hzim, abs_div, abs_neg, abs_two]; linarith
      nlinarith [sq_nonneg z.re, sq_abs z.im, abs_nonneg z.im]
    have hcorr : -((1 : ℂ) / z).re ≤ 1 / 8 := by
      rw [one_div, Complex.inv_re, neg_le, le_div_iff₀ (by linarith)]
      nlinarith [hzre]
    have : (Complex.digamma z).re = (Complex.digamma (z + 1)).re - ((1 : ℂ) / z).re := by
      rw [key, Complex.add_re]; ring
    rw [this]
    linarith
  have e : (L2 s).re = -(Real.log Real.pi) / 2
      + 1 / 4 * ((Complex.digamma (s / 2)).re + (Complex.digamma ((1 - s) / 2)).re) := by
    rw [L2_eq_digamma hs, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.add_re,
      Complex.re_ofReal_mul, Complex.add_re]
    congr 1
    rw [show (-(Real.log Real.pi : ℂ) / 2) = (((-(Real.log Real.pi) / 2 : ℝ)) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  rw [e]
  linarith

/-! ## The Hadamard bounds for `-Re ζ'/ζ` -/

/-- The decomposition `-Re ζ'/ζ = -Re ξ'/ξ + Re L₋ + Re L₂` off the real axis. -/
private lemma negReLogDerivZeta_eq_xi {s : ℂ} (h1 : 1 < s.re) (hi : s.im ≠ 0) :
    negReLogDerivZeta s = -(logDeriv xi s).re + (Lm s).re + (L2 s).re := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1.le
  have key := congrArg Complex.re (logDeriv_zeta_add_L2 hi (by linarith) hz)
  rw [Complex.add_re, Complex.sub_re] at key
  have hld : logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := logDeriv_apply _ _
  unfold negReLogDerivZeta
  rw [Complex.neg_re, ← hld]
  linarith

/-- The core Hadamard estimate: `-Re ζ'/ζ(s) + Re ξ'/ξ(s) ≤ ½ log|t| + C`. -/
private lemma negReLogDerivZeta_add_re_logDeriv_xi_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 4 ≤ |s.im| →
      negReLogDerivZeta s + (logDeriv xi s).re ≤ Real.log |s.im| / 2 + C := by
  obtain ⟨C1, hC1, hLm⟩ := abs_re_Lm_le
  obtain ⟨C2, hL2⟩ := re_L2_le
  refine ⟨C1 / 16 + |C2|, by positivity, fun s h1 h2 hi => ?_⟩
  have hs : s.im ≠ 0 := fun h => by rw [h, abs_zero] at hi; linarith
  have hsq : (16 : ℝ) ≤ s.im ^ 2 := by nlinarith [sq_abs s.im]
  have hb1 : (Lm s).re ≤ C1 / 16 := by
    have h := (abs_le.mp (hLm s h1.le h2 hi)).2
    have : C1 / s.im ^ 2 ≤ C1 / 16 := by
      apply div_le_div_of_nonneg_left hC1 (by norm_num) hsq
    linarith
  have hb2 := hL2 s h1.le h2 hi
  have hC2 : C2 ≤ |C2| := le_abs_self C2
  rw [negReLogDerivZeta_eq_xi h1 hs]
  linarith

/-- **Hadamard, all zero terms dropped**: `-Re ζ'/ζ(σ + it) ≤ ½ log|t| + C` for `1 < σ ≤ 2`,
`|t| ≥ 4`. -/
lemma negReLogDerivZeta_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 4 ≤ |s.im| →
    negReLogDerivZeta s ≤ Real.log |s.im| / 2 + C := by
  obtain ⟨C, hC, h⟩ := negReLogDerivZeta_add_re_logDeriv_xi_le
  refine ⟨C, hC, fun s h1 h2 hi => ?_⟩
  have hpos := re_logDeriv_xi_pos (s := s) h1.le
  have := h s h1 h2 hi
  linarith

/-- One zero of `ξ` at the height of `s` contributes at least `1/(σ - β)` to `Re ξ'/ξ(s)`. -/
private lemma re_logDeriv_xi_ge_one_div {s ρ : ℂ} (h1 : 1 ≤ s.re) (hρ : IsNontrivialZero ρ)
    (him : ρ.im = s.im) : 1 / (s.re - ρ.re) ≤ (logDeriv xi s).re := by
  have hxi := xi_ne_zero_of_one_le_re h1
  have hsum := summable_re_one_div hxi
  have hnn : ∀ w : zetaZeroConfig.carrier,
      0 ≤ (zeroMult w : ℝ) * ((s.re - (w : ℂ).re) / Complex.normSq (s - w)) := by
    intro w
    have hw : IsNontrivialZero (w : ℂ) := w.2
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by linarith [hw.2.2]) (Complex.normSq_nonneg _))
  have hd : 0 < s.re - ρ.re := by linarith [hρ.2.2]
  have hnsq : Complex.normSq (s - ρ) = (s.re - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, him]
    ring
  have hm : (1 : ℝ) ≤ (zeroMult ρ : ℝ) := by exact_mod_cast zetaSeam.one_le_mult ρ hρ
  have hterm : 1 / (s.re - ρ.re)
      ≤ (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)) := by
    have heq : (s.re - ρ.re) / (s.re - ρ.re) ^ 2 = 1 / (s.re - ρ.re) := by
      rw [sq, ← div_div, div_self hd.ne']
    rw [hnsq, heq]
    have hpos : 0 < 1 / (s.re - ρ.re) := by positivity
    nlinarith
  rw [re_logDeriv_xi_eq_tsum hxi]
  exact hterm.trans (hsum.le_tsum (⟨ρ, hρ⟩ : zetaZeroConfig.carrier) (fun j _ => hnn j))

/-- **Hadamard, keeping one zero**: if `ρ` is a nontrivial zero at the same height as `s`, then
`-Re ζ'/ζ(s) ≤ ½ log|t| + C - 1/(σ - β)`. -/
lemma negReLogDerivZeta_le_of_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ρ : ℂ, 1 < s.re → s.re ≤ 2 →
    4 ≤ |s.im| → IsNontrivialZero ρ → ρ.im = s.im →
    negReLogDerivZeta s ≤ Real.log |s.im| / 2 + C - 1 / (s.re - ρ.re) := by
  obtain ⟨C, hC, h⟩ := negReLogDerivZeta_add_re_logDeriv_xi_le
  refine ⟨C, hC, fun s ρ h1 h2 hi hρ him => ?_⟩
  have hge := re_logDeriv_xi_ge_one_div h1.le hρ him
  have := h s h1 h2 hi
  linarith

/-! ## The zero-free region -/

/-- **de la Vallée Poussin for large ordinates**: there are `c > 0` and `t₀` such that every
nontrivial zero `ρ = β + iγ` with `|γ| ≥ t₀` satisfies `β ≤ 1 - c/log|γ|`. -/
theorem exists_re_le_one_sub_of_nontrivialZero :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 4 ≤ t₀ ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → t₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / Real.log |ρ.im| := by
  obtain ⟨C, hC, hzero⟩ := negReLogDerivZeta_le_of_zero
  obtain ⟨C', hC', hplain⟩ := negReLogDerivZeta_le
  set K : ℝ := 30 + 4 * C + C' + Real.log 2 / 2 + 1 with hKdef
  refine ⟨1 / 125, by norm_num, max 4 (Real.exp K), le_max_left _ _, fun ρ hρ hT => ?_⟩
  have hT4 : (4 : ℝ) ≤ |ρ.im| := le_trans (le_max_left _ _) hT
  have hTe : Real.exp K ≤ |ρ.im| := le_trans (le_max_right _ _) hT
  set L : ℝ := Real.log |ρ.im| with hLdef
  have hLK : K ≤ L := (Real.le_log_iff_exp_le (by linarith)).mpr hTe
  have hK30 : (30 : ℝ) ≤ K := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [hKdef]; linarith
  have hL30 : (30 : ℝ) ≤ L := le_trans hK30 hLK
  have hLpos : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  set u : ℝ := 1 / (10 * L) with hu
  have hupos : 0 < u := by rw [hu]; positivity
  have hune : u ≠ 0 := hupos.ne'
  have hule : u ≤ 1 / 300 := by
    rw [hu]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  set σ : ℝ := 1 + u with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  -- (i) the real-axis bound
  have hf1 : negReLogDerivZeta (σ : ℂ) ≤ 100 * L / 9 + 10 := by
    have h := negReLogDerivZeta_real_le (σ := σ) (a := u / 10) (by linarith)
      (by rw [hσdef]; linarith)
    have e1 : σ - 1 - u / 10 = 9 * u / 10 := by rw [hσdef]; ring
    have e2 : (σ - 1) / (u / 10) = 10 := by
      rw [hσdef, add_sub_cancel_left]
      field_simp
    have e3 : 1 / (9 * u / 10) = 100 * L / 9 := by
      rw [hu]; field_simp; ring
    rw [e1, e2, e3] at h
    exact h
  -- (ii) the bound at the height of the zero, keeping the term of `ρ`
  have hd : 0 < σ - ρ.re := by linarith [hρ.2.2]
  have hf2 : negReLogDerivZeta ((σ : ℂ) + (ρ.im : ℂ) * I)
      ≤ L / 2 + C - 1 / (σ - ρ.re) := by
    have hre : ((σ : ℂ) + (ρ.im : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (ρ.im : ℂ) * I).im = ρ.im := by simp
    have h := hzero ((σ : ℂ) + (ρ.im : ℂ) * I) ρ (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
      (by rw [him]; exact hT4) hρ (by rw [him])
    rwa [hre, him, ← hLdef] at h
  -- (iii) the bound at twice that height
  have hf3 : negReLogDerivZeta ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
      ≤ (Real.log 2 + L) / 2 + C' := by
    have hre : ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I).im = 2 * ρ.im := by simp
    have habs : |2 * ρ.im| = 2 * |ρ.im| := by rw [abs_mul, abs_two]
    have h := hplain ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I) (by rw [hre]; exact hσ1)
      (by rw [hre]; exact hσ2) (by rw [him, habs]; linarith)
    rw [him, habs, Real.log_mul (by norm_num) (by intro h0; rw [h0] at hT4; linarith),
      ← hLdef] at h
    exact h
  -- combine with the 3-4-1 inequality
  have h341 := three_four_one hσ1 ρ.im
  have hv : 4 * (1 / (σ - ρ.re)) ≤ 221 / 6 * L := by
    linarith [h341, hf1, hf2, hf3, hLK]
  have hdd : (1 / (σ - ρ.re)) * (σ - ρ.re) = 1 := one_div_mul_cancel hd.ne'
  have hmul := mul_le_mul_of_nonneg_right hv hd.le
  rw [mul_assoc, hdd, mul_one] at hmul
  have hstep : (27 / 250 : ℝ) / L ≤ σ - ρ.re := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hmul, hLpos, hd]
  have hu' : u = (27 / 250 : ℝ) / L - (1 / 125 : ℝ) / L := by
    rw [hu]; field_simp; ring
  linarith [hstep, hu']

/-- **The de la Vallée Poussin zero-free region.**  There is an absolute `c > 0` with
`ζ(s) ≠ 0` for `|Im s| ≥ 3` and `Re s > 1 - c/log|Im s|`. -/
theorem zeroFreeRegion : ZeroFreeRegion := by
  obtain ⟨c₀, hc₀, t₀, ht₀, hbig⟩ := exists_re_le_one_sub_of_nontrivialZero
  have hfin := finite_absWindow t₀
  obtain ⟨e, he, hsmall⟩ : ∃ e : ℝ, 0 < e ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im| ≤ t₀ →
      ρ.re ≤ 1 - e := by
    rcases hfin.toFinset.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun ρ hρ him =>
        absurd (hfin.mem_toFinset.mpr ⟨hρ, him⟩) (by rw [hemp]; simp)⟩
    · refine ⟨hfin.toFinset.inf' hne (fun w => 1 - w.re), ?_, fun ρ hρ him => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro w hw
        have hw' : IsNontrivialZero w := (hfin.mem_toFinset.mp hw).1
        linarith [hw'.2.2]
      · have h := Finset.inf'_le (fun w : ℂ => 1 - w.re) (hfin.mem_toFinset.mpr ⟨hρ, him⟩)
        linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min (min c₀ (e * Real.log 3)) (Real.log 3 / 2), by positivity, fun s hs hlt => ?_⟩
  set c : ℝ := min (min c₀ (e * Real.log 3)) (Real.log 3 / 2) with hcdef
  have hc1 : c ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc2 : c ≤ e * Real.log 3 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc3 : c ≤ Real.log 3 / 2 := min_le_right _ _
  have hLg : Real.log 3 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) hs
  have hLgpos : 0 < Real.log |s.im| := lt_of_lt_of_le hlog3 hLg
  intro hzero
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hzero
  rcases le_or_gt s.re 0 with h0 | h0
  · -- `Re s ≤ 0` forces `c > log|Im s| ≥ log 3`, contradicting `c ≤ log 3 / 2`
    have : Real.log |s.im| < c := by
      have hq : 1 < c / Real.log |s.im| := by linarith
      rwa [lt_div_iff₀ hLgpos, one_mul] at hq
    linarith
  have hρ : IsNontrivialZero s := ⟨hzero, h0, h1⟩
  rcases le_or_gt t₀ |s.im| with hbg | hsm
  · have hb := hbig s hρ hbg
    have : c₀ / Real.log |s.im| < c / Real.log |s.im| := by linarith
    rw [div_lt_div_iff_of_pos_right hLgpos] at this
    linarith
  · have hb := hsmall s hρ hsm.le
    have hq : e < c / Real.log |s.im| := by linarith
    rw [lt_div_iff₀ hLgpos] at hq
    nlinarith [hq, hLg, he]

end RiemannHypothesis
