/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SubconvexityLeft
import RiemannHypothesis.SubconvexityStrip

/-!
# The convexity bound without a logarithm

The board row `M1-GROWTH` asks for the classical growth estimate

`|ζ(σ + i t)| = O(t ^ ((1 - σ)/2))`   for a fixed `σ` with `0 < σ < 1`,

with **no** logarithm and no `ε`.  `RiemannHypothesis.norm_riemannZeta_le_convexity_log`
proves it with a factor `1 + log|t|`, and that logarithm cannot be removed by convexity alone:
a genuine power saving is needed.  Both halves of the strip now have one:

* `RiemannHypothesis.SubconvexityStrip.norm_riemannZeta_strip_le` gives the exponent
  `(1 - σ)/3` for `1/2 ≤ σ ≤ 1`, which saves `|t|^((1-σ)/6)`;
* `RiemannHypothesis.norm_riemannZeta_le_subconvexity_left` gives the exponent `1/2 - 2σ/3`
  for `0 ≤ σ ≤ 1/2`, which saves `|t|^(σ/6)`.

For a *fixed* `σ` strictly inside the strip both savings are a fixed positive power of `|t|`,
and a fixed positive power of `|t|` swallows `1 + log|t|`.  That is the whole argument.

## Main results

* `exists_log_le_rpow` : `1 + log t ≤ (1 + 1/e) t^e` for `t ≥ 1` and `e > 0`.
* `norm_riemannZeta_le_convexity_logfree` : for every fixed `σ ∈ (0,1)` there is a constant
  `C` with `‖ζ(σ + i t)‖ ≤ C |t|^((1-σ)/2)` for all `|t| ≥ 3` — the logarithm-free convexity
  bound.
* `norm_riemannZeta_le_log_div_of_one_lt_re` : the companion bound used by the zero-free
  region, `‖ζ(σ + i t)‖ ≤ 2 log|t| / (σ - 1)` for `1 < σ ≤ 2` and `|t| ≥ 3`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-- A fixed positive power of `t` swallows the logarithm: `1 + log t ≤ (1 + 1/e) t^e`. -/
lemma exists_log_le_rpow {e : ℝ} (he : 0 < e) {t : ℝ} (ht : 1 ≤ t) :
    1 + Real.log t ≤ (1 + 1 / e) * t ^ e := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hpow : (1 : ℝ) ≤ t ^ e := Real.one_le_rpow ht he.le
  have hlog : Real.log t ≤ t ^ e / e := Real.log_le_rpow_div ht0.le he
  have hdiv : t ^ e / e = (1 / e) * t ^ e := by
    field_simp
  rw [hdiv] at hlog
  nlinarith

/-- On the critical line and to its right the modulus of `ζ` depends only on `|t|`. -/
lemma norm_riemannZeta_strip_abs {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) (t : ℝ) :
    ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖
      = ‖riemannZeta ((sg : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
  have hre : ((sg : ℂ) + (t : ℂ) * I).re = sg := by simp
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h]
    have hs : (sg : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) ((sg : ℂ) + (t : ℂ) * I) := by
      simp
    rw [hs, riemannZeta_conj_of_mem_strip (by rw [hre]; exact h0) (by rw [hre]; exact h1),
      norm_conj]

/-- **The logarithm-free convexity bound.**  For every fixed `σ` with `0 < σ < 1` there is a
constant `C` such that `‖ζ(σ + i t)‖ ≤ C |t|^((1 - σ)/2)` for all `|t| ≥ 3`.

This is the classical form of the convexity estimate: no `ε` in the exponent and no
logarithmic factor.  The constant necessarily depends on `σ` (it blows up as `σ → 1`, where
the exponent tends to `0` while `ζ` is still of size `log t`). -/
theorem norm_riemannZeta_le_convexity_logfree {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ ((1 - sg) / 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_riemannZeta_le_convexity_log
  have hre : ∀ t : ℝ, ((sg : ℂ) + (t : ℂ) * I).re = sg := by intro t; simp
  have him : ∀ t : ℝ, ((sg : ℂ) + (t : ℂ) * I).im = t := by intro t; simp
  rcases le_or_gt (1 / 2) sg with hhalf | hhalf
  · -- right half of the strip: the exponent `(1-σ)/3` saves `|t|^((1-σ)/6)`
    set e : ℝ := (1 - sg) / 6 with he
    have hepos : 0 < e := by rw [he]; linarith
    set D : ℝ := 1 + 1 / e with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    refine ⟨max (400 * D) (28 * C₀), by positivity, ?_⟩
    intro t ht
    have hT0 : (0 : ℝ) < |t| := by linarith
    have hT1 : (1 : ℝ) ≤ |t| := by linarith
    have hlog : 0 ≤ Real.log |t| := Real.log_nonneg hT1
    have hpow : (0 : ℝ) < |t| ^ ((1 - sg) / 2) := Real.rpow_pos_of_pos hT0 _
    rcases le_or_gt ((10 : ℝ) ^ 9) |t| with hbig | hsmall
    · rw [norm_riemannZeta_strip_abs h0 h1 t]
      have hstrip := SubconvexityStrip.norm_riemannZeta_strip_le (sg := sg) (t := |t|)
        hhalf h1.le hbig
      refine hstrip.trans ?_
      have hsplit : |t| ^ ((1 - sg) / 2) = |t| ^ ((1 - sg) / 3) * |t| ^ e := by
        rw [← Real.rpow_add hT0, he]
        congr 1
        ring
      have habs : Real.log |t| + 1 ≤ D * |t| ^ e := by
        have := exists_log_le_rpow hepos hT1
        rw [hD]
        linarith
      have hpow3 : (0 : ℝ) ≤ |t| ^ ((1 - sg) / 3) := (Real.rpow_pos_of_pos hT0 _).le
      calc 400 * |t| ^ ((1 - sg) / 3) * (Real.log |t| + 1)
          ≤ 400 * |t| ^ ((1 - sg) / 3) * (D * |t| ^ e) := by
            have : (0 : ℝ) ≤ 400 * |t| ^ ((1 - sg) / 3) := by positivity
            exact mul_le_mul_of_nonneg_left habs this
        _ = (400 * D) * (|t| ^ ((1 - sg) / 3) * |t| ^ e) := by ring
        _ = (400 * D) * |t| ^ ((1 - sg) / 2) := by rw [← hsplit]
        _ ≤ max (400 * D) (28 * C₀) * |t| ^ ((1 - sg) / 2) := by
            gcongr
            exact le_max_left _ _
    · have h := hC₀ ((sg : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
        (by rw [him]; exact ht)
      rw [hre, him] at h
      refine h.trans ?_
      have hlogle : 1 + Real.log |t| ≤ 28 := by
        have h9 : Real.log |t| ≤ Real.log ((10 : ℝ) ^ 9) := Real.log_le_log hT0 hsmall.le
        have h10 : Real.log ((10 : ℝ) ^ 9) = 9 * Real.log 10 := by
          rw [Real.log_pow]
          norm_num
        have hlog10 : Real.log 10 ≤ 3 := by
          have hexp : (10 : ℝ) ≤ Real.exp 3 := by
            have h1' : Real.exp 1 > 2.7182818283 := Real.exp_one_gt_d9
            have h3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
              rw [← Real.exp_add, ← Real.exp_add]
              norm_num
            nlinarith [Real.exp_pos 1]
          calc Real.log 10 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) hexp
            _ = 3 := Real.log_exp 3
        linarith
      calc C₀ * (1 + Real.log |t|) * |t| ^ ((1 - sg) / 2)
          ≤ C₀ * 28 * |t| ^ ((1 - sg) / 2) := by
            have : C₀ * (1 + Real.log |t|) ≤ C₀ * 28 :=
              mul_le_mul_of_nonneg_left hlogle hC₀pos.le
            exact mul_le_mul_of_nonneg_right this hpow.le
        _ = (28 * C₀) * |t| ^ ((1 - sg) / 2) := by ring
        _ ≤ max (400 * D) (28 * C₀) * |t| ^ ((1 - sg) / 2) := by
            gcongr
            exact le_max_right _ _
  · -- left half of the strip: the exponent `1/2 - 2σ/3` saves `|t|^(σ/6)`
    obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_riemannZeta_le_subconvexity_left
    set e : ℝ := sg / 6 with he
    have hepos : 0 < e := by rw [he]; linarith
    set D : ℝ := 1 + 1 / e with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    refine ⟨C₁ * D, by positivity, ?_⟩
    intro t ht
    have hT0 : (0 : ℝ) < |t| := by linarith
    have hT1 : (1 : ℝ) ≤ |t| := by linarith
    have hlog : 0 ≤ Real.log |t| := Real.log_nonneg hT1
    have h := hC₁ ((sg : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [him]; exact ht)
    rw [hre, him] at h
    refine h.trans ?_
    have hsplit : |t| ^ ((1 - sg) / 2) = |t| ^ (1 / 2 - 2 * sg / 3) * |t| ^ e := by
      rw [← Real.rpow_add hT0, he]
      congr 1
      ring
    have habs : 1 + Real.log |t| ≤ D * |t| ^ e := by
      have := exists_log_le_rpow hepos hT1
      rw [hD]
      linarith
    have hpowl : (0 : ℝ) ≤ |t| ^ (1 / 2 - 2 * sg / 3) := (Real.rpow_pos_of_pos hT0 _).le
    calc C₁ * (1 + Real.log |t|) * |t| ^ (1 / 2 - 2 * sg / 3)
        ≤ C₁ * (D * |t| ^ e) * |t| ^ (1 / 2 - 2 * sg / 3) := by
          have hstep : C₁ * (1 + Real.log |t|) ≤ C₁ * (D * |t| ^ e) :=
            mul_le_mul_of_nonneg_left habs hC₁pos.le
          exact mul_le_mul_of_nonneg_right hstep hpowl
      _ = (C₁ * D) * (|t| ^ (1 / 2 - 2 * sg / 3) * |t| ^ e) := by ring
      _ = (C₁ * D) * |t| ^ ((1 - sg) / 2) := by rw [← hsplit]

/-- The logarithm-free convexity bound in asymptotic form: for fixed `σ ∈ (0,1)`,
`ζ(σ + i t) = O(t^((1-σ)/2))` as `t → ∞`. -/
theorem isBigO_riemannZeta_convexity_logfree {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    (fun t : ℝ => riemannZeta ((sg : ℂ) + (t : ℂ) * I))
      =O[atTop] fun t : ℝ => t ^ ((1 - sg) / 2) := by
  obtain ⟨C, hCpos, hC⟩ := norm_riemannZeta_le_convexity_logfree h0 h1
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have h := hC t (by rwa [abs_of_nonneg ht0])
  rw [abs_of_nonneg ht0] at h
  rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)]

/-- The companion growth bound to the right of the strip, in the shape used by the zero-free
region argument: `‖ζ(σ + i t)‖ ≤ 2 log|t| / (σ - 1)` for `1 < σ ≤ 2` and `|t| ≥ 3`. -/
theorem norm_riemannZeta_le_log_div_of_one_lt_re {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2)
    (ht : 3 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 2 * Real.log |s.im| / (s.re - 1) := by
  have hd : 0 < s.re - 1 := by linarith
  have hbase := norm_riemannZeta_le_of_one_lt_re h1
  have hlog : (1 : ℝ) ≤ Real.log |s.im| := by
    have h3 : Real.log 3 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) ht
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have : (1 : ℝ) ≤ Real.log 3 := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
    linarith
  have hone : (1 : ℝ) ≤ 1 / (s.re - 1) := by
    rw [le_div_iff₀ hd]
    linarith
  have htwo : (2 : ℝ) / (s.re - 1) = 1 / (s.re - 1) + 1 / (s.re - 1) := by ring
  have hstep : 1 + 1 / (s.re - 1) ≤ 2 / (s.re - 1) := by
    rw [htwo]
    linarith
  refine hbase.trans (hstep.trans ?_)
  gcongr
  linarith

end RiemannHypothesis

end
