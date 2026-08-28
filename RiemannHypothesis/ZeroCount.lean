/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.XiGrowth
import RiemannHypothesis.ZeroCountingLemma

/-!
# The Riemann–von Mangoldt upper bound: `N(T) = O(T log T)`

Combining the Jensen-type counting estimate of `RiemannHypothesis.ZeroCountingLemma` with the
order-one growth bound for the completed zeta function `ξ` of `RiemannHypothesis.XiGrowth`, we
obtain the classical upper bound for the number of nontrivial zeroes of `ζ` up to height `T`:

* `finite_nontrivialZeros` : for every height `T` the set of zeroes of `ζ` in the critical strip
  with `|im s| ≤ T` is **finite**;
* `ncard_nontrivialZeros_le` : there is an absolute constant `C` with
  `#{s : ζ s = 0, 0 < re s < 1, |im s| ≤ T} ≤ C · T · log T` for all `T ≥ 2`.

Zeroes are counted *without* multiplicity (the counting lemma counts distinct points).  The
matching lower bound `N(T) ≫ T log T`, and the asymptotic `N(T) = (T/2π) log (T/2πe) + O(log T)`,
are not proved here: they need the argument principle and Stirling's formula for the Gamma factor.

The argument is: a nontrivial zero with `|im s| ≤ T` is a zero of the entire function `ξ`, and
lies in the disc of radius `T + 2` about the point `s = 2`; the counting lemma applied on the
concentric disc of radius `4 (T + 2)` bounds the number of such zeroes by
`log (M / ‖ξ(2)‖) / log 3` where `M` is the maximum of `‖ξ‖` on the large circle, and the growth
bound gives `log M = O(T log T)`.  Note that `ξ(2) = Λ(2) ≠ 0`.
-/

noncomputable section

open Complex Metric

namespace RiemannHypothesis

/-- The nontrivial zeroes of `ζ` of height at most `T`. -/
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T}

/-- A nontrivial zero of height at most `T` is a zero of `ξ` inside the disc of radius `T + 2`
about `s = 2`. -/
lemma nontrivialZeros_subset (T : ℝ) :
    nontrivialZeros T ⊆ {z : ℂ | dist z 2 ≤ (4 * (T + 2)) / 4 ∧ xiFn z = 0} := by
  intro s hs
  obtain ⟨hzero, h0, h1, hT⟩ := hs
  refine ⟨?_, xiFn_eq_zero_of_zeta h0 h1 hzero⟩
  have hdist : dist s 2 = ‖s - 2‖ := Complex.dist_eq s 2
  have hre : |(s - 2).re| ≤ 2 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    rw [abs_le]; constructor <;> linarith
  have him : |(s - 2).im| ≤ T := by simpa using hT
  have := Complex.norm_le_abs_re_add_abs_im (s - 2)
  rw [hdist]
  linarith

/-- The two elementary numerical facts used below. -/
private lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private lemma mul_log_mono {C u v : ℝ} (hC : 0 < C) (hu : 0 ≤ u) (huv : u ≤ v) :
    C * (1 + u) * Real.log (2 + u) ≤ C * (1 + v) * Real.log (2 + v) := by
  have h1 : C * (1 + u) ≤ C * (1 + v) := by nlinarith
  have h2 : Real.log (2 + u) ≤ Real.log (2 + v) := Real.log_le_log (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  exact mul_le_mul h1 h2 h3 (by nlinarith)

private lemma log_twelve_le_three : Real.log 12 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h3 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by rw [Real.exp_one_pow]; norm_num
  rw [h3]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) he 3]

/-- **The set of nontrivial zeroes of `ζ` of bounded height is finite.** -/
theorem finite_nontrivialZeros (T : ℝ) : (nontrivialZeros T).Finite := by
  obtain ⟨C, hC0, hC⟩ := norm_xiFn_le
  set R : ℝ := 4 * (max T 0 + 2) with hR
  have hT0 : (0 : ℝ) ≤ max T 0 := le_max_right _ _
  have hRpos : 0 < R := by rw [hR]; linarith
  set M : ℝ := Real.exp (C * (1 + (R + 2)) * Real.log (2 + (R + 2))) with hM
  have hsphere : ∀ z ∈ sphere (2 : ℂ) R, ‖xiFn z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ ≤ R + 2 := by
      have h2 : ‖z - 2‖ = R := by simpa [Complex.dist_eq] using hz
      have := norm_le_norm_add_norm_sub' z (2 : ℂ)
      simp only [Complex.norm_ofNat] at this
      linarith [this, h2.le]
    exact le_trans (hC z) (Real.exp_le_exp.mpr (mul_log_mono hC0 (norm_nonneg z) hzn))
  have hfin := finite_setOf_zeros (f := xiFn) (c := 2) (R := R) (M := M) hRpos
    differentiable_xiFn.diffContOnCl hsphere xiFn_two_ne_zero
  refine Set.Finite.subset hfin ?_
  refine subset_trans (nontrivialZeros_subset T) ?_
  intro z hz
  refine ⟨?_, hz.2⟩
  have : (4 * (T + 2)) / 4 ≤ R / 4 := by
    rw [hR]
    have : T ≤ max T 0 := le_max_left _ _
    linarith
  exact le_trans hz.1 this

/-- **The disc about `s = 2` containing every zero of height at most `T`.**  For `T ≥ 2` there is
a bound `M` for `ξ` on the circle of radius `4 (T + 2)` about `s = 2`, whose logarithmic ratio
against the centre value `ξ(2) ≠ 0` — the quantity controlling every Jensen-type count in that
disc — is at most `A T log T`, for an absolute constant `A`. -/
theorem exists_global_disc_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T → ∃ M : ℝ, 0 < M ∧
      (∀ z ∈ sphere (2 : ℂ) (4 * (T + 2)), ‖xiFn z‖ ≤ M) ∧
      Real.log (M / ‖xiFn 2‖) / Real.log 3 ≤ A * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := norm_xiFn_le
  have hxi2 : 0 < ‖xiFn 2‖ := norm_pos_iff.mpr xiFn_two_ne_zero
  refine ⟨112 * C + |Real.log ‖xiFn (2 : ℂ)‖| + 1, by positivity, ?_⟩
  intro T hT
  set R : ℝ := 4 * (T + 2) with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  set M : ℝ := Real.exp (C * (1 + (R + 2)) * Real.log (2 + (R + 2))) with hM
  have hMpos : 0 < M := Real.exp_pos _
  have hsphere : ∀ z ∈ sphere (2 : ℂ) R, ‖xiFn z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ ≤ R + 2 := by
      have h2 : ‖z - 2‖ = R := by simpa [Complex.dist_eq] using hz
      have := norm_le_norm_add_norm_sub' z (2 : ℂ)
      simp only [Complex.norm_ofNat] at this
      linarith [this, h2.le]
    exact le_trans (hC z) (Real.exp_le_exp.mpr (mul_log_mono hC0 (norm_nonneg z) hzn))
  refine ⟨M, hMpos, hsphere, ?_⟩
  -- estimate the logarithm
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT0 : (1:ℝ) / 2 ≤ Real.log T := le_trans hlog2 hlogT
  have hdiv : Real.log (M / ‖xiFn 2‖) = Real.log M - Real.log ‖xiFn 2‖ :=
    Real.log_div (ne_of_gt hMpos) (ne_of_gt hxi2)
  have hlogM : Real.log M = C * (1 + (R + 2)) * Real.log (2 + (R + 2)) := Real.log_exp _
  have hRT : 1 + (R + 2) = 4 * T + 11 := by rw [hR]; ring
  have h2RT : 2 + (R + 2) = 4 * T + 12 := by rw [hR]; ring
  have hbound1 : (4 : ℝ) * T + 11 ≤ 16 * T := by linarith
  have hbound2 : Real.log (4 * T + 12) ≤ 7 * Real.log T := by
    have h1 : (4 : ℝ) * T + 12 ≤ 12 * T := by linarith
    have h2 : Real.log (4 * T + 12) ≤ Real.log (12 * T) := Real.log_le_log (by linarith) h1
    have h3 : Real.log (12 * T) = Real.log 12 + Real.log T := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    have h4 : Real.log 12 ≤ 3 := log_twelve_le_three
    have h5 : (3 : ℝ) ≤ 6 * Real.log T := by linarith
    linarith
  have hlogTpos : 0 < Real.log T := by linarith
  have hMle : Real.log M ≤ 112 * C * (T * Real.log T) := by
    rw [hlogM, hRT, h2RT]
    have h1 : C * (4 * T + 11) ≤ C * (16 * T) := by nlinarith
    have h2 : 0 ≤ C * (4 * T + 11) := by nlinarith
    nlinarith [hbound2, Real.log_nonneg (by linarith : (1:ℝ) ≤ 4 * T + 12)]
  have hconst : -Real.log ‖xiFn 2‖ ≤ |Real.log ‖xiFn (2:ℂ)‖| * (T * Real.log T) := by
    have h1 : -Real.log ‖xiFn 2‖ ≤ |Real.log ‖xiFn (2:ℂ)‖| := neg_le_abs _
    have h2 : (1 : ℝ) ≤ T * Real.log T := by nlinarith
    nlinarith [abs_nonneg (Real.log ‖xiFn (2:ℂ)‖)]
  have hnum : Real.log (M / ‖xiFn 2‖)
      ≤ (112 * C + |Real.log ‖xiFn (2:ℂ)‖|) * (T * Real.log T) := by
    rw [hdiv]; nlinarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
  have hnum0 : 0 ≤ Real.log (M / ‖xiFn 2‖) := by
    have : (1 : ℝ) ≤ M / ‖xiFn 2‖ := by
      rw [le_div_iff₀ hxi2, one_mul]
      have h2 : ‖xiFn 2‖ ≤ M := by
        refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (2 : ℂ) R)
          isBounded_ball differentiable_xiFn.diffContOnCl ?_ ?_
        · rw [frontier_ball (2 : ℂ) hRpos.ne']; exact hsphere
        · rw [closure_ball (2 : ℂ) hRpos.ne']; simp [hRpos.le]
      linarith
    exact Real.log_nonneg this
  calc Real.log (M / ‖xiFn 2‖) / Real.log 3
      ≤ Real.log (M / ‖xiFn 2‖) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
    _ ≤ (112 * C + |Real.log ‖xiFn (2:ℂ)‖|) * (T * Real.log T) := hnum
    _ ≤ (112 * C + |Real.log ‖xiFn (2:ℂ)‖| + 1) * T * Real.log T := by
        have : 0 ≤ T * Real.log T := by nlinarith
        nlinarith

/-- **The Riemann–von Mangoldt upper bound.**  The number of zeroes of `ζ` in the critical strip
of height at most `T`, counted without multiplicity, is `O(T log T)`. -/
theorem ncard_nontrivialZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ((nontrivialZeros T).ncard : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA0, hA⟩ := exists_global_disc_bound
  refine ⟨A, hA0, ?_⟩
  intro T hT
  obtain ⟨M, _, hsphere, hnum⟩ := hA T hT
  set R : ℝ := 4 * (T + 2) with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hcount := ncard_setOf_zeros_le (f := xiFn) (c := 2) (R := R) (M := M) hRpos
    differentiable_xiFn.diffContOnCl hsphere xiFn_two_ne_zero
  have hfin := finite_setOf_zeros (f := xiFn) (c := 2) (R := R) (M := M) hRpos
    differentiable_xiFn.diffContOnCl hsphere xiFn_two_ne_zero
  have hmono : (nontrivialZeros T).ncard ≤ {z : ℂ | dist z 2 ≤ R / 4 ∧ xiFn z = 0}.ncard :=
    Set.ncard_le_ncard (by rw [hR]; exact nontrivialZeros_subset T) hfin
  have hstep : ((nontrivialZeros T).ncard : ℝ) ≤ Real.log (M / ‖xiFn 2‖) / Real.log 3 := by
    refine le_trans ?_ hcount
    exact_mod_cast hmono
  exact le_trans hstep hnum

end RiemannHypothesis
