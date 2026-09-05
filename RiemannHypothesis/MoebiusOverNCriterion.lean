/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MoebiusCriterion

/-!
# The `∑ μ(n)/n` criterion

This is a fourth route to the Riemann hypothesis, a close relative of the Mertens criterion
of `RiemannHypothesis.MoebiusCriterion` but with a genuinely different arithmetic input:
instead of the Mertens function `M(N) = ∑_{n ≤ N} μ(n)` one bounds the *weighted* sums

`m(N) = ∑_{n ≤ N} μ(n)/n`   (`littleMertens`).

The classical statement equivalent to the Riemann hypothesis is `m(N) = O(N^{-1/2+ε})` for
every `ε > 0` (`LittleMertensBoundForm`); the implication towards the Riemann hypothesis is
proved here (`zeta_of_littleMertensBound`).

## The argument

Because the exponent is now `-1/2` rather than `1/2`, this uses the Abel-summation
machinery of `RiemannHypothesis.AbelDirichlet` at the exponent `θ = -1/2`: the series

`F(w) = ∑_{n ≥ 1} m(n) (n^{-w} - (n+1)^{-w})`

is holomorphic on the half-plane `re w > -1/2`, and for `re w > 0` it equals the L-series of
`n ↦ μ(n)/n`, that is `1/ζ(w+1)`.  Hence

`(w+1-1) ζ(w+1) · F(w) = w`

on `re w > 0`, and therefore on all of `re w > -1/2` by the identity theorem (the left-hand
side is holomorphic there because the pole of `ζ` is removed by the factor `w`).  A zero of
`ζ` at `s` with `re s > 1/2`, `s ≠ 1` would give `0 = s - 1 ≠ 0` at `w = s - 1`.
-/

noncomputable section

open Complex Filter Finset ArithmeticFunction
open scoped Topology

namespace RiemannHypothesis

/-- The weighted Mertens sums `m(N) = ∑_{n ≤ N} μ(n)/n`. -/
def littleMertens (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) / n

/-- **The weighted Mertens bound**: `∑_{n ≤ N} μ(n)/n = O(N^{-1/2+ε})` for every `ε > 0`. -/
def LittleMertensBoundForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |littleMertens N| ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ) + ε)

/-- The arithmetic function `n ↦ μ(n)/n`. -/
def moebiusOverN : ℕ → ℂ := fun n => (moebius n : ℂ) / n

/-- The Abel-summed Dirichlet series of `n ↦ μ(n)/n`. -/
def moebiusOverNAbel (w : ℂ) : ℂ := abelSum moebiusOverN w

lemma partialSum_moebiusOverN (N : ℕ) :
    partialSum moebiusOverN N = ((littleMertens N : ℝ) : ℂ) := by
  simp [partialSum, moebiusOverN, littleMertens]

lemma norm_partialSum_moebiusOverN (N : ℕ) :
    ‖partialSum moebiusOverN N‖ = |littleMertens N| := by
  rw [partialSum_moebiusOverN, Complex.norm_real, Real.norm_eq_abs]

/-- The weighted Mertens bound is a partial-sum bound of exponent `-1/2`. -/
lemma partialSumBound_moebiusOverN (hm : LittleMertensBoundForm) :
    PartialSumBound moebiusOverN (-(1 / 2 : ℝ)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hm ε hε
  exact ⟨C, fun N => by rw [norm_partialSum_moebiusOverN]; exact hC N⟩

lemma differentiableOn_moebiusOverNAbel (hm : LittleMertensBoundForm) :
    DifferentiableOn ℂ moebiusOverNAbel {w : ℂ | -(1 / 2 : ℝ) < w.re} :=
  differentiableOn_abelSum (by norm_num) (partialSumBound_moebiusOverN hm)

/-! ## Identification of the L-series -/

lemma term_moebiusOverN (w : ℂ) (n : ℕ) :
    LSeries.term moebiusOverN w n = LSeries.term moebiusC (w + 1) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn0,
      Complex.cpow_one]
    simp only [moebiusOverN, moebiusC]
    field_simp

lemma lSeriesSummable_moebiusOverN {w : ℂ} (hw : 0 < w.re) :
    LSeriesSummable moebiusOverN w := by
  have h : LSeriesSummable moebiusC (w + 1) := by
    refine ArithmeticFunction.LSeriesSummable_moebius_iff.mpr ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith
  exact (Summable.congr h (fun n => (term_moebiusOverN w n).symm))

lemma lSeries_moebiusOverN (w : ℂ) :
    LSeries moebiusOverN w = LSeries moebiusC (w + 1) :=
  tsum_congr (term_moebiusOverN w)

/-- For `re w > 0`, `ζ(w+1) · F(w) = 1`. -/
lemma riemannZeta_mul_moebiusOverNAbel (hm : LittleMertensBoundForm) {w : ℂ} (hw : 0 < w.re) :
    riemannZeta (w + 1) * moebiusOverNAbel w = 1 := by
  have hw1 : 1 < (w + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hwθ : -(1 / 2 : ℝ) < w.re := by linarith
  have hF : moebiusOverNAbel w = LSeries moebiusC (w + 1) := by
    rw [moebiusOverNAbel, abelSum_eq_LSeries (by norm_num) (partialSumBound_moebiusOverN hm)
      hwθ (lSeriesSummable_moebiusOverN hw), lSeries_moebiusOverN]
  rw [hF]
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := w + 1) hw1
  rwa [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hw1] at h

/-! ## The criterion -/

/-- **The weighted Mertens criterion**: if `∑_{n ≤ N} μ(n)/n = O(N^{-1/2+ε})` for every
`ε > 0`, then the Riemann hypothesis holds. -/
theorem zeta_of_littleMertensBound (hm : LittleMertensBoundForm) : ZetaForm := by
  refine zeta_iff_zeta_strip.mpr (zeta_strip_iff_nonvanishing_right.mpr ?_)
  intro s hs hs1 hzero
  set U : Set ℂ := {w : ℂ | -(1 / 2 : ℝ) < w.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hshift : Differentiable ℂ (fun w : ℂ => zetaPoleFree (w + 1)) :=
    differentiable_zetaPoleFree.comp (differentiable_id.add_const 1)
  have hG : AnalyticOnNhd ℂ (fun w => zetaPoleFree (w + 1) * moebiusOverNAbel w) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    exact hshift.differentiableOn.mul (differentiableOn_moebiusOverNAbel hm)
  have hH : AnalyticOnNhd ℂ (fun w : ℂ => w) U :=
    differentiable_id.differentiableOn.analyticOnNhd hUopen
  have hmem1 : (1 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : (fun w => zetaPoleFree (w + 1) * moebiusOverNAbel w) =ᶠ[nhds (1 : ℂ)]
      fun w : ℂ => w := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hopen.mem_nhds (by simp)
    filter_upwards [hmem] with w hw
    have hw0 : (0 : ℝ) < w.re := hw
    have hwne : w + 1 ≠ 1 := by
      intro h
      have : w = 0 := by linear_combination h
      rw [this] at hw0
      simp at hw0
    rw [zetaPoleFree_of_ne_one hwne, show w + 1 - 1 = w by ring, mul_assoc,
      riemannZeta_mul_moebiusOverNAbel hm hw0, mul_one]
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq hH hUconn hmem1 hev
  have hsU : s - 1 ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, Complex.sub_re, Complex.one_re]
    linarith
  have hval := heq hsU
  simp only [show s - 1 + 1 = s by ring] at hval
  rw [zetaPoleFree_of_ne_one hs1, hzero, mul_zero, zero_mul] at hval
  exact hs1 (by linear_combination -hval)

end RiemannHypothesis

end
