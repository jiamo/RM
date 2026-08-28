/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MultiplicityCountingLemma
import RiemannHypothesis.ZeroCountLocal
import RiemannHypothesis.ZeroMultiplicitySymmetry

/-!
# The multiplicity of a nontrivial zero is `O(log |γ|)`

The counting results of `RiemannHypothesis.ZeroCount` and `RiemannHypothesis.ZeroCountLocal` count
the zeroes of `ζ` in the critical strip *without* multiplicity.  This file bounds the multiplicity
itself, using the Jensen-type estimate of `RiemannHypothesis.MultiplicityCountingLemma` in the same
disc of radius `20` about `4 + i T` that produced the local count.

## Main results

* `analyticOrderAt_xiFn_eq` : inside the critical strip `ξ` and `ζ` vanish to the same order.

* `zeroMultiplicity_le_of_mem_zerosNearHeight` : a zero of `ζ` in the strip at height within `1`
  of `T ≥ 25` has multiplicity at most `41 log T`.

* `zeroMultiplicity_le_log_abs_im` : a nontrivial zero `ρ` with `|im ρ| ≥ 25` has multiplicity at
  most `41 log |im ρ|`.  This is the classical `O(log |γ|)` bound on the order of a zero.

* `sum_zeroMultiplicity_zerosNearHeight_le` : the local count with multiplicity — the zeroes at
  height within `1` of `T ≥ 25` number at most `41 log T` even when counted with multiplicity.

* `exists_zeroMultiplicity_bound` : there is an absolute constant `K` with
  `zeroMultiplicity ρ ≤ K log T` for every nontrivial zero of height at most `T` (`T ≥ 25`);
  the low zeroes are handled by a single fixed disc.

* `multCount_le` : the number of zeroes of height at most `T` **counted with multiplicity** is
  `O(T log T)`, by the same Jensen-type estimate applied to the total order of vanishing in the
  large disc about `s = 2`.
-/

noncomputable section

open Complex Metric Set

namespace RiemannHypothesis

/-! ## `ξ` and `ζ` vanish to the same order inside the strip -/

/-- Inside the critical strip the completed function `ξ` and `ζ` vanish to the same order: they
differ by the analytic factor `s (s - 1) / 2`, which is nonzero there, and by the nonvanishing
factor relating `Λ` and `ζ`. -/
lemma analyticOrderAt_xiFn_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt xiFn s = analyticOrderAt riemannZeta s := by
  have hne0 : s ≠ 0 := fun h => by simp [h] at h0
  have hne1 : s ≠ 1 := fun h => by simp [h] at h1
  have hfac : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) s :=
    DifferentiableOn.analyticAt (s := Set.univ)
      ((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).differentiableOn
      Filter.univ_mem
  have hev : xiFn =ᶠ[nhds s] (fun z : ℂ => z * (z - 1) / 2) * completedRiemannZeta := by
    filter_upwards [(isOpen_ne.inter isOpen_ne).mem_nhds
      (show s ∈ {z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1} from ⟨hne0, hne1⟩)] with z hz
    exact xiFn_eq_completed hz.1 hz.2
  have hfacne : s * (s - 1) / 2 ≠ 0 := by
    refine div_ne_zero (mul_ne_zero hne0 ?_) two_ne_zero
    exact sub_ne_zero.mpr hne1
  have hzero : analyticOrderAt (fun z : ℂ => z * (z - 1) / 2) s = 0 :=
    hfac.analyticOrderAt_eq_zero.2 hfacne
  rw [analyticOrderAt_congr hev,
    analyticOrderAt_mul hfac (analyticAt_completedRiemannZeta hne0 hne1), hzero, zero_add,
    analyticOrderAt_completedRiemannZeta_eq h0 h1]

/-- The multiplicity of a zero, viewed in `ℕ∞`, is at most the order of vanishing of `ξ`. -/
lemma zeroMultiplicity_le_analyticOrderAt_xiFn {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ((zeroMultiplicity s : ℕ) : ℕ∞) ≤ analyticOrderAt xiFn s := by
  rw [analyticOrderAt_xiFn_eq h0 h1]
  exact ENat.coe_toNat_le_self _

/-! ## The bound in the disc at height `T` -/

/-- **The multiplicity of a zero at height `T` is `O(log T)`.**  A zero of `ζ` in the critical
strip whose height differs from `T ≥ 25` by at most `1` has multiplicity at most `41 log T`. -/
theorem zeroMultiplicity_le_of_mem_zerosNearHeight {T : ℝ} (hT : 25 ≤ T) {ρ : ℂ}
    (hρ : ρ ∈ zerosNearHeight T) : (zeroMultiplicity ρ : ℝ) ≤ 41 * Real.log T := by
  obtain ⟨M, _, hsphere, hcne, hnum⟩ := exists_disc_data_near_height hT
  set c : ℂ := 4 + (T : ℂ) * I with hc
  obtain ⟨hdist, _⟩ := zerosNearHeight_subset T hρ
  have hord : ((zeroMultiplicity ρ : ℕ) : ℕ∞) ≤ analyticOrderAt xiFn ρ :=
    zeroMultiplicity_le_analyticOrderAt_xiFn hρ.2.1 hρ.2.2.1
  have hle := analyticOrder_le_log_div_log_three (f := xiFn) (c := c) (a := ρ) (R := 20) (M := M)
    (m := zeroMultiplicity ρ) (by norm_num) differentiable_xiFn.diffContOnCl hsphere hcne
    (by simpa using hdist) hord
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  refine le_trans hle ?_
  rcases le_or_gt (Real.log (M / ‖xiFn c‖)) 0 with h | h
  · have hnp : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  · have hstep : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ Real.log (M / ‖xiFn c‖) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

/-- **The classical `O(log |γ|)` bound on the multiplicity of a nontrivial zero**, for zeroes of
height at least `25`.  Zeroes of smaller height are covered by `exists_zeroMultiplicity_bound`. -/
theorem zeroMultiplicity_le_log_abs_im {ρ : ℂ} (hρ : ρ ∈ nontrivialZeroSet)
    (him : 25 ≤ |ρ.im|) : (zeroMultiplicity ρ : ℝ) ≤ 41 * Real.log |ρ.im| := by
  obtain ⟨hzero, h0, h1⟩ := hρ
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · have habs : |ρ.im| = ρ.im := abs_of_nonneg hpos
    refine zeroMultiplicity_le_of_mem_zerosNearHeight (T := |ρ.im|) him ?_
    exact ⟨hzero, h0, h1, by rw [habs]; simp⟩
  · -- reflect in the real axis: conjugation preserves both the zero set and the multiplicity
    have habs : |ρ.im| = -ρ.im := abs_of_neg hneg
    have hconj : (starRingEnd ℂ) ρ ∈ zerosNearHeight |ρ.im| := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := riemannZeta_conj_of_mem_strip h0 h1
        rw [this, hzero, map_zero]
      · simpa using h0
      · simpa using h1
      · simp only [Complex.conj_im, habs]
        simp
    have hmul := zeroMultiplicity_le_of_mem_zerosNearHeight (T := |ρ.im|) him hconj
    rwa [zeroMultiplicity_conj h0 h1] at hmul

/-! ## The local count with multiplicity -/

/-- The zeroes of `ζ` in the critical strip at height within `1` of `T ≥ 25` are finitely many. -/
theorem finite_zerosNearHeight {T : ℝ} (hT : 25 ≤ T) : (zerosNearHeight T).Finite := by
  obtain ⟨M, _, hsphere, hcne, _⟩ := exists_disc_data_near_height hT
  have hfin := finite_setOf_zeros (f := xiFn) (c := 4 + (T : ℂ) * I) (R := 20) (M := M)
    (by norm_num) differentiable_xiFn.diffContOnCl hsphere hcne
  exact hfin.subset (zerosNearHeight_subset T)

/-- **The local Riemann–von Mangoldt bound with multiplicity.**  The zeroes of `ζ` in the critical
strip at height within `1` of `T ≥ 25`, counted *with* multiplicity, number at most `41 log T`. -/
theorem sum_zeroMultiplicity_zerosNearHeight_le {T : ℝ} (hT : 25 ≤ T) :
    ((∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ : ℕ) : ℝ) ≤ 41 * Real.log T := by
  obtain ⟨M, _, hsphere, hcne, hnum⟩ := exists_disc_data_near_height hT
  set c : ℂ := 4 + (T : ℂ) * I with hc
  have hfin := finite_zerosNearHeight hT
  have hsum : (∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ)
      = ∑ ρ ∈ hfin.toFinset, zeroMultiplicity ρ := by
    rw [← finsum_mem_coe_finset]
    simp
  have hdist : ∀ ρ ∈ hfin.toFinset, dist ρ c ≤ 20 / 4 := by
    intro ρ hρ
    have h := zerosNearHeight_subset T (hfin.mem_toFinset.mp hρ)
    rw [hc]
    exact h.1
  have hord : ∀ ρ ∈ hfin.toFinset, ((zeroMultiplicity ρ : ℕ) : ℕ∞) ≤ analyticOrderAt xiFn ρ := by
    intro ρ hρ
    obtain ⟨_, h0, h1, _⟩ := hfin.mem_toFinset.mp hρ
    exact zeroMultiplicity_le_analyticOrderAt_xiFn h0 h1
  have hbound := sum_analyticOrder_le_log_div_log_three (f := xiFn) (c := c) (R := 20) (M := M)
    (m := zeroMultiplicity) (by norm_num) differentiable_xiFn.diffContOnCl hsphere hcne
    hfin.toFinset hdist hord
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  rw [hsum]
  refine le_trans hbound ?_
  rcases le_or_gt (Real.log (M / ‖xiFn c‖)) 0 with h | h
  · have hnp : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  · have hstep : Real.log (M / ‖xiFn c‖) / Real.log 3 ≤ Real.log (M / ‖xiFn c‖) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

/-! ## A uniform bound over the whole strip -/

/-- The multiplicities of the nontrivial zeroes of height at most `25` are bounded by an absolute
constant: they all lie in the single disc of radius `50` about `s = 2`. -/
theorem exists_zeroMultiplicity_bound_low :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ ∈ nontrivialZeroSet, |ρ.im| ≤ 25 → (zeroMultiplicity ρ : ℝ) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := norm_xiFn_le
  set M : ℝ := Real.exp (C * (1 + 202) * Real.log (2 + 202)) with hM
  have hsphere : ∀ z ∈ sphere (2 : ℂ) 200, ‖xiFn z‖ ≤ M := by
    intro z hz
    have h2 : ‖z - 2‖ = 200 := by simpa [Complex.dist_eq] using hz
    have hzn : ‖z‖ ≤ 202 := by
      have := norm_le_norm_add_norm_sub' z (2 : ℂ)
      simp only [Complex.norm_ofNat] at this
      linarith
    refine le_trans (hC z) (Real.exp_le_exp.mpr ?_)
    have hlog : Real.log (2 + ‖z‖) ≤ Real.log (2 + 202) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlognn : 0 ≤ Real.log (2 + ‖z‖) :=
      Real.log_nonneg (by linarith [norm_nonneg z])
    have h1 : C * (1 + ‖z‖) ≤ C * (1 + 202) := by nlinarith [norm_nonneg z]
    nlinarith [norm_nonneg z]
  have hxi2 : xiFn (2 : ℂ) ≠ 0 := xiFn_two_ne_zero
  refine ⟨|Real.log (M / ‖xiFn (2 : ℂ)‖) / Real.log 3| + 1, by positivity, ?_⟩
  intro ρ hρ him
  obtain ⟨hzero, h0, h1⟩ := hρ
  have hdist : dist ρ (2 : ℂ) ≤ 200 / 4 := by
    have hre : |(ρ - 2).re| ≤ 2 := by
      simp only [Complex.sub_re, Complex.re_ofNat]
      rw [abs_le]; constructor <;> linarith
    have hi : |(ρ - 2).im| ≤ 25 := by simpa using him
    have := Complex.norm_le_abs_re_add_abs_im (ρ - 2)
    rw [Complex.dist_eq]
    linarith
  have hord : ((zeroMultiplicity ρ : ℕ) : ℕ∞) ≤ analyticOrderAt xiFn ρ :=
    zeroMultiplicity_le_analyticOrderAt_xiFn h0 h1
  have hle := analyticOrder_le_log_div_log_three (f := xiFn) (c := (2 : ℂ)) (a := ρ) (R := 200)
    (M := M) (m := zeroMultiplicity ρ) (by norm_num) differentiable_xiFn.diffContOnCl hsphere
    hxi2 hdist hord
  refine le_trans hle ?_
  linarith [le_abs_self (Real.log (M / ‖xiFn (2 : ℂ)‖) / Real.log 3)]

/-- **A uniform `O(log T)` bound for the multiplicity of every zero of height at most `T`.** -/
theorem exists_zeroMultiplicity_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 25 ≤ T → ∀ ρ ∈ nontrivialZeros T,
      (zeroMultiplicity ρ : ℝ) ≤ K * Real.log T := by
  obtain ⟨K, hK0, hK⟩ := exists_zeroMultiplicity_bound_low
  have hlog25 : (3 : ℝ) ≤ Real.log 25 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h3 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by rw [Real.exp_one_pow]; norm_num
    rw [h3]
    have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    nlinarith [pow_le_pow_left₀ (Real.exp_pos 1).le he 3]
  refine ⟨41 + K, by linarith, ?_⟩
  intro T hT ρ hρ
  obtain ⟨hzero, h0, h1, hheight⟩ := hρ
  have hlogT : (3 : ℝ) ≤ Real.log T := le_trans hlog25 (Real.log_le_log (by norm_num) hT)
  rcases le_or_gt 25 |ρ.im| with hhigh | hlow
  · have hmul := zeroMultiplicity_le_log_abs_im ⟨hzero, h0, h1⟩ hhigh
    have hmono : Real.log |ρ.im| ≤ Real.log T :=
      Real.log_le_log (by linarith) hheight
    have hK0' : 0 ≤ K * Real.log T := by positivity
    nlinarith
  · have hmul := hK ρ ⟨hzero, h0, h1⟩ hlow.le
    nlinarith [Real.log_nonneg (show (1:ℝ) ≤ T by linarith)]

/-! ## Riemann–von Mangoldt with multiplicity -/

/-- **The Riemann–von Mangoldt upper bound with multiplicity.**  The number of zeroes of `ζ` in
the critical strip of height at most `T`, counted *with* multiplicity, is `O(T log T)` — the same
order as the count without multiplicity.

Every zero of height at most `T` lies in the disc of radius `4 (T + 2) / 4` about `s = 2`, and
`sum_analyticOrder_le_log_div_log_three` bounds the *total* order of vanishing of `ξ` there. -/
theorem multCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (multCount T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA0, hA⟩ := exists_global_disc_bound
  refine ⟨A, hA0, ?_⟩
  intro T hT
  obtain ⟨M, _, hsphere, hnum⟩ := hA T hT
  set R : ℝ := 4 * (T + 2) with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hfin := finite_nontrivialZeros T
  have hsum : multCount T = ∑ ρ ∈ hfin.toFinset, zeroMultiplicity ρ := by
    rw [multCount, ← finsum_mem_coe_finset]
    simp
  have hdist : ∀ ρ ∈ hfin.toFinset, dist ρ (2 : ℂ) ≤ R / 4 := by
    intro ρ hρ
    have h := (nontrivialZeros_subset T) (hfin.mem_toFinset.mp hρ)
    rw [hR]
    exact h.1
  have hord : ∀ ρ ∈ hfin.toFinset, ((zeroMultiplicity ρ : ℕ) : ℕ∞) ≤ analyticOrderAt xiFn ρ := by
    intro ρ hρ
    obtain ⟨_, h0, h1, _⟩ := hfin.mem_toFinset.mp hρ
    exact zeroMultiplicity_le_analyticOrderAt_xiFn h0 h1
  have hbound := sum_analyticOrder_le_log_div_log_three (f := xiFn) (c := 2) (R := R) (M := M)
    (m := zeroMultiplicity) hRpos differentiable_xiFn.diffContOnCl hsphere xiFn_two_ne_zero
    hfin.toFinset hdist hord
  rw [hsum]
  exact le_trans hbound hnum

end RiemannHypothesis
