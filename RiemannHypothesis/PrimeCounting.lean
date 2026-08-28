/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Reducing the prime number theorem to a Chebyshev asymptotic

The prime number theorem is not available in Mathlib, and the board row `M1-PNT` asks for

`π(x) / (x / log x) → 1`.

Mathlib *does* provide the Abel-summation link `π⌊x⌋ = θ(x)/log x + O(x/(log x)²)`
(`Chebyshev.primeCounting_sub_theta_div_log_isBigO`) and the elementary comparison
`|ψ(x) - θ(x)| ≤ 2 √x log x` (`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).  Together they
reduce the prime number theorem to the single analytic input `ψ(x) ~ x` — which is what the
explicit formula (`M1-EXPLICIT`) plus a zero-free region on `re s = 1` would supply, and
which is *not* proved here.

This file records that reduction as a proved implication, so that the remaining gap in
`M1-PNT` is exactly one statement.

## Main results

* `chebyshev_theta_tendsto_of_psi` : `ψ(x)/x → 1` implies `θ(x)/x → 1`.
* `primeCounting_tendsto_of_chebyshev_theta` : `θ(x)/x → 1` implies
  `π⌊x⌋ / (x / log x) → 1`.
* `primeCounting_tendsto_of_chebyshev_psi` : `ψ(x)/x → 1` implies the prime number theorem
  in the form `π⌊x⌋ / (x / log x) → 1`.
-/

noncomputable section

open Asymptotics Filter Real
open scoped Topology

namespace RiemannHypothesis

/-- `log x / √x → 0`. -/
lemma tendsto_log_div_sqrt_atTop : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
  rw [Real.sqrt_eq_rpow]

/-- The Chebyshev functions `ψ` and `θ` have the same asymptotic behaviour: their difference,
divided by `x`, tends to `0`. -/
lemma tendsto_psi_sub_theta_div_atTop :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) ?_
    (by simpa using tendsto_log_div_sqrt_atTop.const_mul 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hbd := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  calc |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x := hbd
    _ = 2 * (Real.log x / Real.sqrt x) * x := by
        field_simp
        rw [Real.sq_sqrt hx0.le]
        ring

/-- If `ψ(x) ~ x` then `θ(x) ~ x`. -/
theorem chebyshev_theta_tendsto_of_psi
    (h : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hsub := h.sub tendsto_psi_sub_theta_div_atTop
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

/-- **The prime number theorem follows from `θ(x) ~ x`.**  This is Mathlib's Abel-summation
link `π⌊x⌋ = θ(x)/log x + O(x/(log x)²)`, divided by `x / log x`. -/
theorem primeCounting_tendsto_of_chebyshev_theta
    (h : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  -- the error term, rescaled, tends to `0`
  have hg : Tendsto (fun x : ℝ => (x / Real.log x ^ 2) * (Real.log x / x)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_inv_atTop_zero.comp tendsto_log_atTop)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    simp only [Function.comp_apply]
    field_simp
  have herr : Tendsto
      (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
        (Real.log x / x)) atTop (𝓝 0) :=
    (Chebyshev.primeCounting_sub_theta_div_log_isBigO.mul
      (isBigO_refl (fun x : ℝ => Real.log x / x) atTop)).trans_tendsto hg
  have hsum := herr.add h
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp
  ring

/-- **The prime number theorem follows from `ψ(x) ~ x`.** -/
theorem primeCounting_tendsto_of_chebyshev_psi
    (h : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) :=
  primeCounting_tendsto_of_chebyshev_theta (chebyshev_theta_tendsto_of_psi h)

end RiemannHypothesis

end
