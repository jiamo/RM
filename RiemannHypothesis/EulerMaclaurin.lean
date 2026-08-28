/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries

/-!
# The Euler–Maclaurin representation of `ζ` and the logarithmic bound

This file proves the first-order Euler–Maclaurin (Abel summation) representation of the
Riemann zeta function and derives from it the classical bound
`|ζ(σ + it)| = O(log |t|)` for `1 ≤ σ ≤ 2`, which the eta representation used in
`RiemannHypothesis.Growth` cannot reach.
-/

noncomputable section

open Complex Filter Finset
open scoped Topology

namespace RiemannHypothesis

/-! ## A mean value bound for `x ↦ x ^ (-s)` -/

/-- Mean value bound: `‖u^(-s) - v^(-s)‖ ≤ ‖s‖ (log v - log u) u^(-re s)` for `0 < u ≤ v`
and `0 ≤ re s`. -/
theorem norm_cpow_neg_sub_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ‖(u : ℂ) ^ (-s) - (v : ℂ) ^ (-s)‖ ≤ ‖s‖ * (Real.log v - Real.log u) * u ^ (-s.re) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  set a : ℝ := Real.log u with ha
  set b : ℝ := Real.log v with hb
  have hab : a ≤ b := Real.log_le_log hu huv
  have hpa : (u : ℂ) ^ (-s) = Complex.exp (-s * (a : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hu.ne')]
    rw [Complex.ofReal_log hu.le]
    ring_nf
  have hpb : (v : ℂ) ^ (-s) = Complex.exp (-s * (b : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hv.ne')]
    rw [Complex.ofReal_log hv.le]
    ring_nf
  rw [hpa, hpb]
  set C : ℝ := Real.exp (-s.re * a) with hC
  have hf : ∀ x ∈ segment ℝ (-s * (a : ℂ)) (-s * (b : ℂ)), DifferentiableAt ℂ Complex.exp x :=
    fun x _ => Complex.differentiable_exp x
  have hbound : ∀ x ∈ segment ℝ (-s * (a : ℂ)) (-s * (b : ℂ)), ‖deriv Complex.exp x‖ ≤ C := by
    intro x hx
    obtain ⟨p, q, hp, hq, hpq, hxdef⟩ := hx
    have hp1 : p = 1 - q := by linarith
    have hmid : a ≤ p * a + q * b := by
      have hexp : p * a + q * b - a = q * (b - a) := by rw [hp1]; ring
      have := mul_nonneg hq (sub_nonneg.mpr hab)
      linarith
    have hxre : x.re ≤ -s.re * a := by
      rw [← hxdef]
      have hre : (p • (-s * (a : ℂ)) + q • (-s * (b : ℂ))).re = -s.re * (p * a + q * b) := by
        simp [Complex.add_re, Complex.mul_re]
        ring
      rw [hre]
      exact mul_le_mul_of_nonpos_left hmid (by linarith)
    calc ‖deriv Complex.exp x‖ = Real.exp x.re := by rw [Complex.deriv_exp, Complex.norm_exp]
      _ ≤ C := Real.exp_le_exp.mpr hxre
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hf hbound
    (convex_segment (𝕜 := ℝ) (-s * (a : ℂ)) (-s * (b : ℂ)))
    (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
  have hnorm : ‖(-s * (a : ℂ)) - (-s * (b : ℂ))‖ = ‖s‖ * (b - a) := by
    have hfac : (-s * (a : ℂ)) - (-s * (b : ℂ)) = s * ((b : ℂ) - (a : ℂ)) := by ring
    rw [hfac, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hCeq : C = u ^ (-s.re) := by
    rw [hC, ha, ← Real.log_rpow hu, Real.exp_log (by positivity)]
  calc ‖Complex.exp (-s * (a : ℂ)) - Complex.exp (-s * (b : ℂ))‖
      ≤ C * ‖(-s * (a : ℂ)) - (-s * (b : ℂ))‖ := hmvt
    _ = C * (‖s‖ * (b - a)) := by rw [hnorm]
    _ = ‖s‖ * (b - a) * u ^ (-s.re) := by rw [hCeq]; ring

/-- The elementary antiderivative `∫_u^v x^(-s) dx = (v^(1-s) - u^(1-s))/(1-s)`. -/
theorem integral_cpow_neg {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {s : ℂ} (hs : s ≠ 1) :
    ∫ x in u..v, (x : ℂ) ^ (-s) = ((v : ℂ) ^ (1 - s) - (u : ℂ) ^ (1 - s)) / (1 - s) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc u v := by
    rw [Set.uIcc_of_le huv]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hne : (-s : ℂ) ≠ -1 := fun h => hs (by linear_combination -h)
  rw [integral_cpow (a := u) (b := v) (r := -s) (Or.inr ⟨hne, h0⟩)]
  rw [show (-s + 1 : ℂ) = 1 - s by ring]

/-! ## The Euler–Maclaurin terms -/

/-- `eulerTerm n s = (n+1)^(-s) - ∫_{n+1}^{n+2} x^(-s) dx`, the error committed when the
integral of `x ↦ x^(-s)` over `[n+1, n+2]` is replaced by the value at the left endpoint. -/
def eulerTerm (n : ℕ) (s : ℂ) : ℂ :=
  ((n + 1 : ℝ) : ℂ) ^ (-s) - (((n + 1 : ℝ) : ℂ) ^ (1 - s) - ((n + 2 : ℝ) : ℂ) ^ (1 - s)) / (s - 1)

/-- The integral representation of `eulerTerm`. -/
lemma eulerTerm_eq_integral (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    eulerTerm n s = ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), (((n + 1 : ℝ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s))
    := by
  have hu : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have huv : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le huv]
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    linarith
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const hint,
    integral_cpow_neg hu huv hs]
  simp only [intervalIntegral.integral_const]
  unfold eulerTerm
  rw [show (((n : ℝ) + 2) - ((n : ℝ) + 1) : ℝ) = 1 by ring]
  rw [show (s - 1 : ℂ) = -(1 - s) by ring]
  have hne : (1 - s : ℂ) ≠ 0 := fun h => hs (by linear_combination -h)
  push_cast
  field_simp
  simp only [one_smul]
  ring

/-- The basic bound `‖eulerTerm n s‖ ≤ ‖s‖ (n+1)^(-(1 + re s))`. -/
lemma norm_eulerTerm_le (n : ℕ) {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s ≠ 1) :
    ‖eulerTerm n s‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-(1 + s.re)) := by
  have hu : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hC : ∀ x ∈ Set.uIoc ((n : ℝ) + 1) ((n : ℝ) + 2),
      ‖(((n + 1 : ℝ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s))‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-(1 + s.re)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxpos : (0 : ℝ) < x := by linarith
    refine (norm_cpow_neg_sub_le hu hx1.le hs0).trans ?_
    have hlog : Real.log x - Real.log ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      have h1 : Real.log x ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hxpos hx2
      have h2 : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)
          = Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) :=
        (Real.log_div (by positivity) (by positivity)).symm
      have h3 : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h4 : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by field_simp; ring
      linarith
    have hrp : (0 : ℝ) < ((n : ℝ) + 1) ^ (-s.re) := Real.rpow_pos_of_pos hu _
    have hsplit : ((n : ℝ) + 1) ^ (-(1 + s.re))
        = (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ (-s.re) := by
      rw [show -(1 + s.re) = -1 + -s.re by ring, Real.rpow_add hu, Real.rpow_neg_one, one_div]
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (norm_nonneg s)) hrp.le
  rw [eulerTerm_eq_integral n hs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rwa [show |((n : ℝ) + 2 - ((n : ℝ) + 1))| = 1 by
    rw [show ((n : ℝ) + 2 - ((n : ℝ) + 1)) = (1 : ℝ) by ring]; norm_num, mul_one] at h

/-- The Euler–Maclaurin approximation to `ζ` with `N` explicit terms. -/
def zetaApprox (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
    + ∑' n : ℕ, eulerTerm (n + N) s

/-- Summability of `n ↦ (n+1)^(-p)` for `1 < p`. -/
lemma summable_natAddOne_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := Real.summable_nat_rpow.mpr (by linarith)
  refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-- Summability of the Dirichlet series terms in the form used here. -/
lemma summable_natAddOne_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) : ℂ) ^ (-s)) := by
  apply Summable.of_norm
  have hnorm : ∀ n : ℕ, ‖((n + 1 : ℝ) : ℂ) ^ (-s)‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  exact (summable_natAddOne_rpow_neg hs).congr fun n => (hnorm n).symm

/-- Summability of the Euler–Maclaurin terms on the right half-plane. -/
lemma summable_eulerTerm {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun n : ℕ => eulerTerm n s) := by
  refine Summable.of_norm_bounded ((summable_natAddOne_rpow_neg
    (p := 1 + s.re) (by linarith)).mul_left ‖s‖) fun n => norm_eulerTerm_le n hs.le hs1

/-- **The Euler–Maclaurin representation of `ζ`** on the half-plane of absolute
convergence. -/
theorem riemannZeta_eq_zetaApprox (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = zetaApprox N s := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hsub : (s - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs1
  set f : ℕ → ℂ := fun n => ((n + 1 : ℝ) : ℂ) ^ (-s) with hf
  have hsum : Summable f := summable_natAddOne_cpow_neg hs
  have hz : riemannZeta s = ∑' n, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    rw [hf]
    simp only
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  set g : ℕ → ℂ := fun n => ((n + N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) with hg
  have hkey : ∀ n : ℕ, f (n + N) = eulerTerm (n + N) s + (g n - g (n + 1)) := by
    intro n
    rw [hf, hg]
    simp only
    unfold eulerTerm
    push_cast
    field_simp
    ring_nf
  have hgtend : Tendsto g atTop (𝓝 0) := by
    rw [hg, tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ n : ℕ, ‖((n + N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
        = ((n : ℝ) + ((N : ℝ) + 1)) ^ (-(s.re - 1)) / ‖s - 1‖ := by
      intro n
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      rw [Complex.sub_re, Complex.one_re, show ((n : ℝ) + N + 1) = ((n : ℝ) + ((N : ℝ) + 1)) by
        ring, show (1 - s.re) = -(s.re - 1) by ring]
    simp_rw [hnorm]
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + ((N : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop ((N : ℝ) + 1) tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp hbase
    simpa using h2.div_const ‖s - 1‖
  have hE : Summable (fun n : ℕ => eulerTerm (n + N) s) :=
    (summable_nat_add_iff N).2 (summable_eulerTerm (by linarith) hs1)
  have hfN : Summable (fun n : ℕ => f (n + N)) := (summable_nat_add_iff N).2 hsum
  have hsummg : Summable (fun n : ℕ => g n - g (n + 1)) :=
    (hfN.sub hE).congr fun n => by rw [hkey n]; ring
  have hgsum : ∑' n : ℕ, (g n - g (n + 1)) = g 0 := by
    have hts := hsummg.hasSum.tendsto_sum_nat
    have hlim : Tendsto (fun M => ∑ n ∈ range M, (g n - g (n + 1))) atTop (𝓝 (g 0)) := by
      simp_rw [Finset.sum_range_sub' g]
      simpa using (tendsto_const_nhds (x := g 0) (f := atTop (α := ℕ))).sub hgtend
    exact tendsto_nhds_unique hts hlim
  have hsplit : ∑' n, f n = ∑ n ∈ range N, f n + ∑' n, f (n + N) :=
    (hsum.sum_add_tsum_nat_add N).symm
  have htail : ∑' n : ℕ, f (n + N) = (∑' n : ℕ, eulerTerm (n + N) s) + g 0 := by
    rw [show (fun n : ℕ => f (n + N)) = fun n : ℕ => eulerTerm (n + N) s + (g n - g (n + 1)) from
      funext hkey, Summable.tsum_add hE hsummg, hgsum]
  rw [hz, hsplit, htail]
  unfold zetaApprox
  have hg0 : g 0 = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) := by rw [hg]; norm_num
  rw [hg0]
  simp only [hf]
  ring

/-! ## The logarithmic bound -/

/-- The harmonic bound for a truncated `p`-series with `1 ≤ p`. -/
lemma sum_range_natAddOne_rpow_neg_le_one_add_log {p : ℝ} (hp : 1 ≤ p) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-p) ≤ 1 + Real.log N := by
  have hterm : ∀ n ∈ range N, ((n : ℝ) + 1) ^ (-p) ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n _
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
    have h := Real.rpow_le_rpow_of_exponent_le hx (show -p ≤ (-1 : ℝ) by linarith)
    rwa [Real.rpow_neg_one] at h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hh : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, ((n : ℝ) + 1)⁻¹ := by simp [harmonic]
  rw [← hh]
  exact_mod_cast harmonic_le_one_add_log N

/-- The tail of a `p`-series with `2 ≤ p` beyond `N` is at most `2/(N+1)`. -/
lemma tsum_shift_rpow_neg_le {p : ℝ} (hp : 2 ≤ p) (N : ℕ) :
    ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-p) ≤ 2 / ((N : ℝ) + 1) := by
  have hterm : ∀ n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-p) ≤ (((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro n
    have hx : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) (n + N); linarith
    refine (Real.rpow_le_rpow_of_exponent_le hx (show -p ≤ (-2 : ℝ) by linarith)).trans
      (le_of_eq ?_)
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
    push_cast
    ring_nf
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  refine le_trans (Finset.sum_le_sum fun n _ => hterm n) ?_
  have h : ∑ n ∈ range M, (((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ i ∈ Finset.Ioo N (N + M + 1), ((i : ℝ) ^ 2)⁻¹ := by
    rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun i _ => ?_
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [h]
  exact sum_Ioo_inv_sq_le N (N + M + 1)

/-- **A logarithmic bound for `ζ` just to the right of the line `re s = 1`.** -/
theorem norm_riemannZeta_le_log_of_one_lt_re {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 6 + Real.log (1 + |s.im|) := by
  have hσ0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  set t : ℝ := |s.im| with hts
  set N : ℕ := ⌈t⌉₊ with hNdef
  have hN1 : t ≤ (N : ℝ) := Nat.le_ceil t
  have hN2 : (N : ℝ) < t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [riemannZeta_eq_zetaApprox N h1]
  unfold zetaApprox
  -- the truncated Dirichlet sum
  have hA : ‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ 1 + Real.log (1 + t) := by
    have hlogle : Real.log (N : ℝ) ≤ Real.log (1 + t) := Real.log_le_log hNpos (by linarith)
    calc ‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.range N, ‖((n + 1 : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
          simp
      _ ≤ 1 + Real.log (N : ℝ) := sum_range_natAddOne_rpow_neg_le_one_add_log (by linarith) N
      _ ≤ 1 + Real.log (1 + t) := by linarith
  -- the pole term
  have hden : (2 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hB : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hnum : ((N : ℝ) + 1) ^ (1 - s).re ≤ 1 := by
      rw [Complex.sub_re, Complex.one_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hpos : (0 : ℝ) < ‖s - 1‖ := by linarith
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- the Euler-Maclaurin tail
  have hC : ‖∑' n : ℕ, eulerTerm (n + N) s‖ ≤ 4 := by
    have hbd : ∀ n : ℕ, ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
      fun n => norm_eulerTerm_le (n + N) hσ0.le hs1
    have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by linarith))
    have hsummable := hsh.mul_left ‖s‖
    have hnorms : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
      hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
    have hnorm_s : ‖s‖ ≤ 2 + t := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hσ0] at h
      linarith
    have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) ≤ 2 / ((N : ℝ) + 1) :=
      tsum_shift_rpow_neg_le (by linarith) N
    have hfrac : 2 / ((N : ℝ) + 1) ≤ 2 / (t + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    calc ‖∑' n : ℕ, eulerTerm (n + N) s‖
        ≤ ∑' n : ℕ, ‖eulerTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
          hnorms.tsum_le_tsum hbd hsummable
      _ = ‖s‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) := tsum_mul_left
      _ ≤ (2 + t) * (2 / (t + 1)) := by
          have h1' : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
            tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
          have ht0 : (0 : ℝ) ≤ t := abs_nonneg _
          exact mul_le_mul hnorm_s (htail.trans hfrac) h1' (by linarith)
      _ ≤ 4 := by
          have ht0 : (0 : ℝ) ≤ t := abs_nonneg _
          rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < t + 1)]
          linarith
  calc ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        + ∑' n : ℕ, eulerTerm (n + N) s‖
      ≤ ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
          + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ + ‖∑' n : ℕ, eulerTerm (n + N) s‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
          + ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖) + ‖∑' n : ℕ, eulerTerm (n + N) s‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (1 + Real.log (1 + t) + 1 / 2) + 4 := by gcongr
    _ ≤ 6 + Real.log (1 + t) := by linarith

/-- **The logarithmic bound for `ζ` on the strip `1 ≤ re s ≤ 2`**, obtained from the
previous bound by continuity in `re s`. -/
theorem norm_riemannZeta_le_log {s : ℂ} (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 6 + Real.log (1 + |s.im|) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  swap
  · exact norm_riemannZeta_le_log_of_one_lt_re hlt h2 ht
  set t : ℝ := s.im with htdef
  have hs : s = ((1 : ℝ) : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [← heq, htdef]
  set F : ℝ → ℂ := fun x => riemannZeta ((x : ℂ) + (t : ℂ) * I) with hF
  have hre : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * I).re = x := by intro x; simp
  have him : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * I).im = t := by intro x; simp
  have hne : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro x h
    have h0 : ((x : ℂ) + (t : ℂ) * I).im = 0 := by rw [h]; simp
    rw [him] at h0
    rw [h0] at ht
    norm_num at ht
  have hinner : Continuous (fun x : ℝ => (x : ℂ) + (t : ℂ) * I) := by fun_prop
  have hcont : ContinuousAt F 1 :=
    ContinuousAt.comp (g := riemannZeta) (f := fun x : ℝ => (x : ℂ) + (t : ℂ) * I) (x := (1 : ℝ))
      ((differentiableAt_riemannZeta (hne 1)).continuousAt) hinner.continuousAt
  have htend : Tendsto (fun x : ℝ => ‖F x‖) (𝓝[>] (1 : ℝ)) (𝓝 ‖F 1‖) :=
    hcont.norm.continuousWithinAt.tendsto
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), ‖F x‖ ≤ 6 + Real.log (1 + |t|) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with x hx
    have h := norm_riemannZeta_le_log_of_one_lt_re (s := (x : ℂ) + (t : ℂ) * I)
      (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2.le) (by rw [him]; exact ht)
    rwa [him] at h
  have hfin := le_of_tendsto htend hev
  rw [hF] at hfin
  simp only [Complex.ofReal_one] at hfin
  rw [hs]
  exact hfin

end RiemannHypothesis

end
