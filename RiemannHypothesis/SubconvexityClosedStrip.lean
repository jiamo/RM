/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ConvexityLogFree

/-!
# Subconvexity on the whole closed critical strip

The two subconvex bounds of this repository are stated in different ranges and with different
thresholds:

* `SubconvexityStrip.norm_riemannZeta_strip_le` — exponent `(1-σ)/3`, but only for
  `1/2 ≤ σ ≤ 1` and only for `t ≥ 10⁹`;
* `norm_riemannZeta_le_subconvexity_left` — exponent `1/2 - 2σ/3`, for `0 ≤ σ ≤ 1/2` and every
  `|t| ≥ 3`.

This file removes the threshold and the sign restriction from the first, and merges the two
into a single statement valid on the whole closed strip `0 ≤ σ ≤ 1` at every height `|t| ≥ 3`.
Below the threshold the convexity bound is already smaller than what is claimed, because
`|t|^((1-σ)/6) ≤ (10⁹)^(1/12) ≤ 6` there; for negative `t` the conjugation symmetry is used,
except on the line `σ = 1`, where the logarithmic bound of `EulerMaclaurin` covers both signs.

The merged exponent is `max ((1-σ)/3) (1/2 - 2σ/3)`, which is `(1-σ)/3` for `σ ≥ 1/2` and
`1/2 - 2σ/3` for `σ ≤ 1/2`; it equals `1/6` at `σ = 1/2`, `0` at `σ = 1`, and `1/2` at `σ = 0`,
and it is strictly smaller than the convexity exponent `(1-σ)/2` for every `σ ∈ (0, 1]`.

## Main results

* `norm_riemannZeta_le_subconvexity_right` : `‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^((1-σ)/3)` for
  `1/2 ≤ σ ≤ 1` and *every* `|t| ≥ 3`.
* `norm_riemannZeta_le_subconvexity_closed_strip` : `‖ζ(s)‖ ≤ C (1 + log|t|) |t|^(e(σ))`,
  `e(σ) = max ((1-σ)/3) (1/2 - 2σ/3)`, for `0 ≤ σ ≤ 1` and `|t| ≥ 3`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-- Below the threshold `10⁹` the convexity bound is already at least as strong as the
subconvex one: `|t|^((1-σ)/2) ≤ 6 |t|^((1-σ)/3)`. -/
lemma rpow_convexity_le_six_mul_rpow_third {sg t : ℝ} (h2 : 1 - sg ≤ 1 / 2)
    (ht1 : 1 ≤ t) (ht : t ≤ (10 : ℝ) ^ 9) :
    t ^ ((1 - sg) / 2) ≤ 6 * t ^ ((1 - sg) / 3) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsplit : t ^ ((1 - sg) / 2) = t ^ ((1 - sg) / 3) * t ^ ((1 - sg) / 6) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have hexp : t ^ ((1 - sg) / 6) ≤ t ^ ((1 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hbase : t ^ ((1 : ℝ) / 12) ≤ 6 := by
    have hb : t ≤ (6 : ℝ) ^ (12 : ℕ) := le_trans ht (by norm_num)
    have hle : t ^ ((1 : ℝ) / 12) ≤ ((6 : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow ht0.le hb (by norm_num)
    refine hle.trans_eq ?_
    rw [← Real.rpow_natCast (6 : ℝ) 12, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : (0 : ℝ) < t ^ ((1 - sg) / 3) := Real.rpow_pos_of_pos ht0 _
  rw [hsplit]
  calc t ^ ((1 - sg) / 3) * t ^ ((1 - sg) / 6)
      ≤ t ^ ((1 - sg) / 3) * 6 := by
        exact mul_le_mul_of_nonneg_left (hexp.trans hbase) hpos.le
    _ = 6 * t ^ ((1 - sg) / 3) := by ring

/-- **Subconvexity on `1/2 ≤ σ ≤ 1`, at every height.**  The bound
`‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^((1-σ)/3)` holds for `1/2 ≤ σ ≤ 1` and every `|t| ≥ 3`,
positive or negative — the threshold `t ≥ 10⁹` of `SubconvexityStrip` is removed. -/
theorem norm_riemannZeta_le_subconvexity_right :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_riemannZeta_le_convexity_log
  refine ⟨max (6 * C₀) 400, by positivity, ?_⟩
  intro s h1 h2 ht
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg hT1
  have hlog1 : (0 : ℝ) < 1 + Real.log |s.im| := by linarith
  have hpow : (0 : ℝ) < |s.im| ^ ((1 - s.re) / 3) := Real.rpow_pos_of_pos hT0 _
  have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rcases le_or_gt |s.im| ((10 : ℝ) ^ 9) with hsmall | hbig
  · -- below the threshold the convexity bound is enough
    have h := hC₀ s (by linarith) h2 ht
    refine h.trans ?_
    have hcv := rpow_convexity_le_six_mul_rpow_third (sg := s.re) (t := |s.im|)
      (by linarith) hT1 hsmall
    calc C₀ * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2)
        ≤ C₀ * (1 + Real.log |s.im|) * (6 * |s.im| ^ ((1 - s.re) / 3)) := by
          have : (0 : ℝ) ≤ C₀ * (1 + Real.log |s.im|) := by positivity
          exact mul_le_mul_of_nonneg_left hcv this
      _ = (6 * C₀) * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) := by ring
      _ ≤ max (6 * C₀) 400 * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) := by
          gcongr
          exact le_max_left _ _
  · rcases eq_or_lt_of_le h2 with hone | hlt
    · -- on the line `σ = 1` the logarithmic bound covers both signs of `t`
      have h := norm_riemannZeta_le_log (s := s) hone.ge (by rw [hone]; norm_num) (by linarith)
      refine h.trans ?_
      have hexp : |s.im| ^ ((1 - s.re) / 3) = 1 := by
        rw [hone]
        norm_num
      rw [hexp, mul_one]
      have hloglt : Real.log (1 + |s.im|) ≤ 1 + Real.log |s.im| := by
        have h2' : Real.log (1 + |s.im|) ≤ Real.log (2 * |s.im|) :=
          Real.log_le_log (by linarith) (by linarith)
        have h3 : Real.log (2 * |s.im|) = Real.log 2 + Real.log |s.im| := by
          rw [Real.log_mul (by norm_num) (by positivity)]
        have h4 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
          linarith
        linarith
      have hmax : (400 : ℝ) ≤ max (6 * C₀) 400 := le_max_right _ _
      nlinarith
    · -- inside the strip and above the threshold: the strip bound, after folding `t` to `|t|`
      have hz : ‖riemannZeta s‖ = ‖riemannZeta ((s.re : ℂ) + ((|s.im| : ℝ) : ℂ) * I)‖ := by
        conv_lhs => rw [hs]
        exact norm_riemannZeta_strip_abs (by linarith) hlt s.im
      rw [hz]
      have hstrip := SubconvexityStrip.norm_riemannZeta_strip_le (sg := s.re) (t := |s.im|)
        h1 h2 hbig.le
      refine hstrip.trans ?_
      have hmax : (400 : ℝ) ≤ max (6 * C₀) 400 := le_max_right _ _
      calc 400 * |s.im| ^ ((1 - s.re) / 3) * (Real.log |s.im| + 1)
          = 400 * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) := by ring
        _ ≤ max (6 * C₀) 400 * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) := by
            have hstep : (400 : ℝ) * (1 + Real.log |s.im|)
                ≤ max (6 * C₀) 400 * (1 + Real.log |s.im|) :=
              mul_le_mul_of_nonneg_right hmax (by linarith)
            exact mul_le_mul_of_nonneg_right hstep hpow.le

/-- **Subconvexity on the whole closed critical strip.**  There is a constant `C` with

`‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t| ^ max ((1-σ)/3) (1/2 - 2σ/3)`

for every `s = σ + i t` with `0 ≤ σ ≤ 1` and `|t| ≥ 3`.  The exponent is `(1-σ)/3` on the right
half of the strip and `1/2 - 2σ/3` on the left half; it is strictly below the convexity
exponent `(1-σ)/2` for every `σ ∈ (0, 1]`. -/
theorem norm_riemannZeta_le_subconvexity_closed_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|)
        * |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_riemannZeta_le_subconvexity_left
  obtain ⟨C₂, hC₂pos, hC₂⟩ := norm_riemannZeta_le_subconvexity_right
  refine ⟨max C₁ C₂, by positivity, ?_⟩
  intro s h0 h1 ht
  have hT0 : (0 : ℝ) < |s.im| := by linarith
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg hT1
  rcases le_or_gt s.re (1 / 2) with hleft | hright
  · have h := hC₁ s h0 hleft ht
    refine h.trans ?_
    have hmono : |s.im| ^ (1 / 2 - 2 * s.re / 3)
        ≤ |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (le_max_right _ _)
    have hCle : C₁ ≤ max C₁ C₂ := le_max_left _ _
    gcongr
  · have h := hC₂ s hright.le h1 ht
    refine h.trans ?_
    have hmono : |s.im| ^ ((1 - s.re) / 3)
        ≤ |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (le_max_left _ _)
    have hCle : C₂ ≤ max C₁ C₂ := le_max_right _ _
    gcongr

end RiemannHypothesis

end
