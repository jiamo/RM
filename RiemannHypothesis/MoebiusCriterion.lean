/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AbelDirichlet

/-!
# The Mertens criterion: a square-root bound for `M(x)` implies the Riemann hypothesis

This file formalizes one of the classical *routes* to the Riemann hypothesis, different in
character from the reformulations of `RiemannHypothesis.Criteria`: the hypothesis follows
from a square-root cancellation bound for the summatory function of the Möbius function,

`M(N) = ∑_{n ≤ N} μ(n)`,

namely `M(N) = O(N^{1/2 + ε})` for every `ε > 0` (`MertensBoundForm`).  This is the honest
Mertens-type criterion: the implication `MertensBoundForm → ZetaForm` is proved here.  (The
converse is also true classically, but its proof needs the explicit formula and is not
attempted here.)

## The argument

The analytic work is done once and for all in `RiemannHypothesis.AbelDirichlet`: summation
by parts turns the (only conditionally convergent) Dirichlet series `∑ μ(n) n^{-s}` into the
*absolutely* convergent series

`F(s) = ∑_{n ≥ 1} M(n) (n^{-s} - (n+1)^{-s})`   (`moebiusAbel`),

holomorphic on `re s > 1/2` and agreeing with the L-series of `μ` for `re s > 1`.  Hence
`ζ(s) F(s) = 1` there.  Both sides of

`(s - 1) ζ(s) · F(s) = s - 1`

are holomorphic on the *convex* half-plane `re s > 1/2` — on the left the pole of `ζ` is
removed by the factor `s - 1` (`zetaPoleFree`, from `RiemannHypothesis.Criteria`) — and they
agree on `re s > 1`, so they agree everywhere on the half-plane by the identity theorem.
Hence `ζ(s) ≠ 0` for `re s > 1/2`, `s ≠ 1`, which is the Riemann hypothesis.
-/

noncomputable section

open Complex Filter Finset ArithmeticFunction
open scoped Topology

namespace RiemannHypothesis

/-- The Mertens function `M(N) = ∑_{n ≤ N} μ(n)`. -/
def mertens (N : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 N, moebius n

/-- **The Mertens bound**: `M(N) = O(N^{1/2+ε})` for every `ε > 0`.  This is the classical
statement equivalent to the Riemann hypothesis; only the implication towards the Riemann
hypothesis is proved here. -/
def MertensBoundForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |(mertens N : ℝ)| ≤ C * (N : ℝ) ^ (1 / 2 + ε)

/-- The Möbius function viewed as a complex-valued arithmetic function. -/
def moebiusC : ℕ → ℂ := fun n => (moebius n : ℂ)

/-- The Abel-summed Möbius series `∑ M(n) (n^{-s} - (n+1)^{-s})`.  For `re s > 1/2` and under
the Mertens bound this series converges absolutely, and it agrees with `1/ζ(s)` for
`re s > 1`. -/
def moebiusAbel (s : ℂ) : ℂ := abelSum moebiusC s

/-! ## Elementary facts about the Mertens function -/

@[simp] lemma mertens_zero : mertens 0 = 0 := by simp [mertens]

@[simp] lemma mertens_one : mertens 1 = 1 := by simp [mertens]

lemma mertens_succ (N : ℕ) : mertens (N + 1) = mertens N + moebius (N + 1) := by
  simp [mertens, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

lemma partialSum_moebiusC (N : ℕ) : partialSum moebiusC N = (mertens N : ℂ) := by
  simp [partialSum, moebiusC, mertens]

lemma norm_partialSum_moebiusC (N : ℕ) : ‖partialSum moebiusC N‖ = |(mertens N : ℝ)| := by
  rw [partialSum_moebiusC, show ((mertens N : ℂ)) = ((mertens N : ℝ) : ℂ) by push_cast; ring]
  simp

/-- The Mertens bound is exactly square-root cancellation for the Möbius function. -/
lemma sqrtCancellation_moebiusC (hM : MertensBoundForm) : SqrtCancellation moebiusC := by
  intro ε hε
  obtain ⟨C, hC⟩ := hM ε hε
  exact ⟨C, fun N => by rw [norm_partialSum_moebiusC]; exact hC N⟩

/-! ## Holomorphy and the identity `ζ · F = 1` -/

lemma differentiableOn_moebiusAbel (hM : MertensBoundForm) :
    DifferentiableOn ℂ moebiusAbel {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_abelSum_of_sqrtCancellation (sqrtCancellation_moebiusC hM)

/-- For `re s > 1` the Abel-summed series is the L-series of the Möbius function. -/
lemma moebiusAbel_eq_LSeries (hM : MertensBoundForm) {s : ℂ} (hs : 1 < s.re) :
    moebiusAbel s = LSeries moebiusC s :=
  abelSum_eq_LSeries_of_sqrtCancellation (sqrtCancellation_moebiusC hM) (by linarith)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

/-- For `re s > 1`, `ζ(s) · F(s) = 1`. -/
lemma riemannZeta_mul_moebiusAbel (hM : MertensBoundForm) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * moebiusAbel s = 1 := by
  rw [moebiusAbel_eq_LSeries hM hs]
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := s) hs
  rwa [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h

/-! ## The criterion -/

/-- **The Mertens criterion**: if `M(N) = O(N^{1/2+ε})` for every `ε > 0`, then the Riemann
hypothesis holds. -/
theorem zeta_of_mertensBound (hM : MertensBoundForm) : ZetaForm := by
  refine zeta_iff_zeta_strip.mpr (zeta_strip_iff_nonvanishing_right.mpr ?_)
  intro s hs hs1 hzero
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hG : AnalyticOnNhd ℂ (fun z => zetaPoleFree z * moebiusAbel z) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    exact (differentiable_zetaPoleFree.differentiableOn).mul (differentiableOn_moebiusAbel hM)
  have hH : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    (differentiable_id.sub_const 1).differentiableOn.analyticOnNhd hUopen
  have hmem2 : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : (fun z => zetaPoleFree z * moebiusAbel z) =ᶠ[nhds (2 : ℂ)] fun z : ℂ => z - 1 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    have hz1 : (1 : ℝ) < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      simp at hz1
    rw [zetaPoleFree_of_ne_one hzne, mul_assoc, riemannZeta_mul_moebiusAbel hM hz1, mul_one]
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq hH hUconn hmem2 hev
  have hval := heq (show s ∈ U from hs)
  simp only at hval
  rw [zetaPoleFree_of_ne_one hs1, hzero, mul_zero, zero_mul] at hval
  exact hs1 (by linear_combination -hval)

end RiemannHypothesis

end
