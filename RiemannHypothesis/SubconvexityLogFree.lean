/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SubconvexityClosedStrip

/-!
# Subconvexity on the closed critical strip, without the logarithm

`RiemannHypothesis.norm_riemannZeta_le_subconvexity_closed_strip` bounds `‖ζ(σ + i t)‖` by
`C (1 + log|t|) |t|^(e σ)` on the whole closed strip `0 ≤ σ ≤ 1`, `|t| ≥ 3`, with the
subconvex exponent

`e σ = max ((1 - σ)/3) (1/2 - 2σ/3)`,

and `RiemannHypothesis.norm_riemannZeta_le_convexity_logfree` removes the logarithm from the
*convexity* bound, at the convexity exponent `(1 - σ)/2`.  This file removes the logarithm
from the *subconvex* bound.  A fixed positive power of the height swallows `1 + log|t|`
(`exists_log_le_rpow`), so the logarithm costs an arbitrarily small `ε` in the exponent, and
the gap `(1 - σ)/2 - e σ`, which is `σ/6` on the left half of the strip and `(1 - σ)/6` on the
right half, is a fixed positive amount at every fixed `σ ∈ (0, 1)`.  Half of that gap pays for
the logarithm and half of it is kept, so the resulting exponent is still strictly below the
convexity exponent.

## Main results

* `norm_riemannZeta_le_subconvexity_logfree` : for every `ε > 0` there is a constant `C`,
  uniform in `σ`, with `‖ζ(s)‖ ≤ C |t|^(e σ + ε)` for `0 ≤ σ ≤ 1` and `|t| ≥ 3`.
* `norm_riemannZeta_le_subconvexity_logfree_fixed` : for every fixed `σ ∈ (0, 1)` there is a
  constant `C` with `‖ζ(σ + i t)‖ ≤ C |t|^((1 - σ)/2 - min σ (1 - σ)/12)` for all `|t| ≥ 3` —
  no logarithm, no `ε`, and an exponent strictly below the convexity exponent.
* `isBigO_riemannZeta_subconvexity_logfree` : the same statement in `O`-notation.

The constants necessarily depend on `ε` and on `σ`: the gap that pays for the logarithm
degenerates as `σ` approaches `0` or `1`.
-/

noncomputable section

open Complex Filter

namespace RiemannHypothesis

/-- **Log-free subconvexity on the closed strip, with an `ε` in the exponent.**  For every
`ε > 0` there is a `C` with `‖ζ(s)‖ ≤ C |t|^(max ((1-σ)/3) (1/2 - 2σ/3) + ε)` for every
`s = σ + i t` with `0 ≤ σ ≤ 1` and `|t| ≥ 3`.  The constant is uniform in `σ`. -/
theorem norm_riemannZeta_le_subconvexity_logfree {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖
        ≤ C * |s.im| ^ (max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) + ep) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_riemannZeta_le_subconvexity_closed_strip
  refine ⟨C₀ * (1 + 1 / ep), by positivity, ?_⟩
  intro s h0 h1 ht
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have h := hC₀ s h0 h1 ht
  have hlog := exists_log_le_rpow hep hT1
  have hsplit : |s.im| ^ (max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) + ep)
      = |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) * |s.im| ^ ep :=
    Real.rpow_add hT0 _ _
  have hpow : (0 : ℝ) < |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) :=
    Real.rpow_pos_of_pos hT0 _
  refine h.trans ?_
  rw [hsplit]
  have hstep : C₀ * (1 + Real.log |s.im|) ≤ C₀ * ((1 + 1 / ep) * |s.im| ^ ep) :=
    mul_le_mul_of_nonneg_left hlog hC₀pos.le
  calc C₀ * (1 + Real.log |s.im|) * |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3)
      ≤ C₀ * ((1 + 1 / ep) * |s.im| ^ ep)
          * |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) :=
        mul_le_mul_of_nonneg_right hstep hpow.le
    _ = C₀ * (1 + 1 / ep)
          * (|s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) * |s.im| ^ ep) := by ring

/-- The subconvex exponent is below the convexity exponent by at least `min σ (1-σ) / 6`. -/
lemma subconvexity_exponent_le (sg : ℝ) :
    max ((1 - sg) / 3) (1 / 2 - 2 * sg / 3) + min sg (1 - sg) / 12
      ≤ (1 - sg) / 2 - min sg (1 - sg) / 12 := by
  have hmin1 : min sg (1 - sg) ≤ sg := min_le_left _ _
  have hmin2 : min sg (1 - sg) ≤ 1 - sg := min_le_right _ _
  have hmax : max ((1 - sg) / 3) (1 / 2 - 2 * sg / 3) ≤ (1 - sg) / 2 - min sg (1 - sg) / 6 := by
    refine max_le ?_ ?_
    · linarith
    · linarith
  linarith

/-- **Log-free subconvexity at a fixed abscissa.**  For every fixed `σ ∈ (0, 1)` there is a
constant `C` with `‖ζ(σ + i t)‖ ≤ C |t|^((1-σ)/2 - min σ (1-σ)/12)` for every `|t| ≥ 3`: no
logarithm, no `ε`, and an exponent strictly below the convexity exponent `(1-σ)/2`. -/
theorem norm_riemannZeta_le_subconvexity_logfree_fixed {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ ((1 - sg) / 2 - min sg (1 - sg) / 12) := by
  have hminpos : 0 < min sg (1 - sg) := lt_min h0 (by linarith)
  obtain ⟨C, hCpos, hC⟩ :=
    norm_riemannZeta_le_subconvexity_logfree (ep := min sg (1 - sg) / 12) (by positivity)
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  have hre : ((sg : ℂ) + (t : ℂ) * I).re = sg := by simp
  have him : ((sg : ℂ) + (t : ℂ) * I).im = t := by simp
  have h := hC ((sg : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  rw [hre, him] at h
  refine h.trans ?_
  have hT1 : (1 : ℝ) ≤ |t| := by linarith
  have hmono : |t| ^ (max ((1 - sg) / 3) (1 / 2 - 2 * sg / 3) + min sg (1 - sg) / 12)
      ≤ |t| ^ ((1 - sg) / 2 - min sg (1 - sg) / 12) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (subconvexity_exponent_le sg)
  exact mul_le_mul_of_nonneg_left hmono hCpos.le

/-- The log-free subconvex bound in `O`-notation:
`ζ(σ + i t) = O(t^((1-σ)/2 - min σ (1-σ)/12))` as `t → ∞`, for every fixed `σ ∈ (0, 1)`. -/
theorem isBigO_riemannZeta_subconvexity_logfree {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    (fun t : ℝ => riemannZeta ((sg : ℂ) + (t : ℂ) * I))
      =O[atTop] fun t : ℝ => t ^ ((1 - sg) / 2 - min sg (1 - sg) / 12) := by
  obtain ⟨C, hCpos, hC⟩ := norm_riemannZeta_le_subconvexity_logfree_fixed h0 h1
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have h := hC t (by rwa [abs_of_nonneg ht0])
  rw [abs_of_nonneg ht0] at h
  rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)]

end RiemannHypothesis
