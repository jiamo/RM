/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EightyPercentSimple

/-!
# Sixty-seven per cent of the zeroes lie on the critical line, `ε`-free

The Montgomery–Taylor window gives `liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁*` with

`c₁* = √2·tan(1/√2)/(1 + tan(1/√2)/√2) = 0.7532960…`,

so `2 − 1/c₁* = 0.6725…` (`RiemannHypothesis.montgomery_taylor_on_critical_line`).  That is an
`ε`-statement: for every `ε > 0` and all large `T`.  To turn it into an `ε`-free inequality with
a decimal constant one needs a numerical lower bound for `c₁*` sharper than the `3/4` proved in
`RiemannHypothesis.EightyPercentSimple` — `3/4` only gives back `2 − 4/3 = 2/3`.

This file proves the sharper bound `c₁* > 88/117 = 0.75213…` and deduces the `ε`-free

`0.67·N(T,2T) ≤ N₀*(T,2T)` for all large `T`,

together with its simple-zero and cumulative forms.  The numerical input is
`tan(1/√2) > 44√2/73 = 0.85240…`, obtained from `x − x³/6 < sin x` (Mathlib) and the quartic
upper bound `cos x ≤ 1 − x²/2 + x⁴/24`, which is proved here from the same `sin` inequality by a
monotonicity argument.  The margin is genuine but thin: at `x = 1/√2` the two bounds give
`tan x > 44√2/73`, while `0.67` needs `tan x > 50√2/83`, and `44·83 = 3652 > 3650 = 50·73`.

Nothing here changes the *method*: the underlying analytic input is still Theorem D of the
vendored `Zeta23` library, and `0.6725…` remains the proportion that method yields.  What is new
is that the repository now states a proportion on the critical line without an `ε`, with a
decimal constant strictly above `2/3`.
-/

noncomputable section

open Real Set

namespace RiemannHypothesis

/-! ## A quartic upper bound for the cosine -/

/-- `cos x ≤ 1 − x²/2 + x⁴/24` for `x ≥ 0`.  Proved from `x − x³/6 < sin x`: the difference
`1 − x²/2 + x⁴/24 − cos x` vanishes at `0` and has derivative `−x + x³/6 + sin x ≥ 0`. -/
lemma cos_le_one_sub_sq_div_two_add_pow_four_div_24 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (-t + t ^ 3 / 6 + Real.sin t) t := by
    intro t
    have h3 := ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
    have he : (-((2 : ℕ) * t ^ (2 - 1) / 2) + (4 : ℕ) * t ^ (4 - 1) / 24 - -Real.sin t)
        = -t + t ^ 3 / 6 + Real.sin t := by push_cast; ring
    rw [he] at h3
    exact h3
  have hmono : MonotoneOn (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      linarith [sin_gt_sub_cube_div_six (Set.mem_Ioi.1 ht)]
  have h0 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simp only [Real.cos_zero] at h0
  norm_num at h0
  linarith

/-! ## A sharper lower bound for `tan (1/√2)` -/

/-- `tan (1/√2) > 44√2/73 = 0.85240…`.  From `sin x > x − x³/6 = (11/12)x` and
`cos x ≤ 1 − x²/2 + x⁴/24 = 73/96` at `x = 1/√2`.  Sharper than
`RiemannHypothesis.tan_one_div_sqrt_two_gt` (`3√2/5 = 0.84852…`). -/
lemma tan_one_div_sqrt_two_gt_quartic :
    44 * Real.sqrt 2 / 73 < Real.tan (1 / Real.sqrt 2) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set x : ℝ := 1 / Real.sqrt 2 with hx
  have hxpos : 0 < x := by positivity
  have hx2 : x ^ 2 = 1 / 2 := by rw [hx]; field_simp; nlinarith [hsq]
  have hx3 : x ^ 3 = x / 2 := by nlinarith [hx2]
  have hx4 : x ^ 4 = 1 / 4 := by nlinarith [hx2]
  have hxval : x = Real.sqrt 2 / 2 := by rw [hx]; field_simp; nlinarith [hsq]
  have hxlt1 : x < 1 := by
    rw [hx, div_lt_one h2]; nlinarith [hsq, h2]
  have hsin : x - x ^ 3 / 6 < Real.sin x := sin_gt_sub_cube_div_six hxpos
  have hcos : Real.cos x ≤ 73 / 96 := by
    have := cos_le_one_sub_sq_div_two_add_pow_four_div_24 hxpos.le
    rw [hx2, hx4] at this
    linarith
  have hcospos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcospos]
  -- `44√2/73 · cos x ≤ 44√2/73 · 73/96 = 11√2/24 = (11/12)·x < sin x`
  have hkey : 44 * Real.sqrt 2 / 73 * Real.cos x ≤ 11 * Real.sqrt 2 / 24 := by
    nlinarith [hcos, h2, hcospos]
  have hsin' : 11 * Real.sqrt 2 / 24 < Real.sin x := by
    have : x - x ^ 3 / 6 = 11 * Real.sqrt 2 / 24 := by
      rw [hx3, hxval]; ring
    linarith [this ▸ hsin]
  linarith

/-! ## The Montgomery–Taylor constant exceeds `88/117` -/

/-- The Montgomery–Taylor constant `c₁* = 0.7532960…` exceeds `88/117 = 0.75213…`.  This is what
makes `2 − 1/c₁*` exceed `59/88 = 0.67045…`, and hence `0.67`. -/
theorem mtConstant_gt_eightyEight_div_117 : 88 / 117 < mtConstant := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htan := tan_one_div_sqrt_two_gt_quartic
  have htanpos : 0 < Real.tan (1 / Real.sqrt 2) := lt_of_le_of_lt (by positivity) htan
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by field_simp; nlinarith [hsq]
  set u : ℝ := Real.tan (1 / Real.sqrt 2) with hu
  have hden : 0 < 1 + 1 / Real.sqrt 2 * u := by positivity
  rw [mtConstant, ← hu, lt_div_iff₀ hden]
  have h1 : 1 / Real.sqrt 2 * u = Real.sqrt 2 / 2 * u := by rw [hinv]
  -- `√2·u > 88/73`, so `88(1 + u/√2) = 88 + 44√2·u < 117√2·u`
  have hkey : 88 / 73 < Real.sqrt 2 * u := by nlinarith [htan, hsq, h2]
  rw [h1]
  nlinarith [hkey, hsq, h2, htanpos]

/-- `2 − 1/c₁* > 0.67`: the Montgomery–Taylor proportion exceeds `67 %`. -/
theorem sixty_seven_lt_two_sub_inv_mtConstant : (0.67 : ℝ) < 2 - mtConstant⁻¹ := by
  have hc : 88 / 117 < mtConstant := mtConstant_gt_eightyEight_div_117
  have hc0 : (0 : ℝ) < mtConstant := by linarith
  have : mtConstant⁻¹ < 117 / 88 := by
    rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
  linarith

/-! ## Sixty-seven per cent on the critical line, `ε`-free -/

/-- **At least 67 % of the nontrivial zeroes of `ζ` lie on the critical line** (dyadic windows),
in `ε`-free form: for all large `T`, `0.67·N(T,2T) ≤ N₀*(T,2T)`.  The zeroes are counted with
multiplicity on the left and as distinct points of the critical line on the right. -/
theorem sixty_seven_percent_on_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.67 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T) := by
  have hgap := sixty_seven_lt_two_sub_inv_mtConstant
  set ε : ℝ := 2 - mtConstant⁻¹ - 0.67 with hεdef
  obtain ⟨T₀, hT₀⟩ := montgomery_taylor_on_critical_line ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 2 - 1 / mtConstant - ε = 0.67 := by rw [hεdef, one_div]; ring
  rwa [hred] at h

/-- **At least 67 % of the nontrivial zeroes of `ζ` are simple and on the critical line**
(dyadic windows), `ε`-free. -/
theorem sixty_seven_percent_simple_on_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.67 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ windowCountSimpleOnLine T (2 * T) := by
  have hgap := sixty_seven_lt_two_sub_inv_mtConstant
  set ε : ℝ := 2 - mtConstant⁻¹ - 0.67 with hεdef
  obtain ⟨T₀, hT₀⟩ := montgomery_taylor_simple_on_critical_line ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 2 - 1 / mtConstant - ε = 0.67 := by rw [hεdef, one_div]; ring
  rwa [hred] at h

/-- **At least 67 % of the nontrivial zeroes of `ζ` are simple and on the critical line**,
cumulative form over `(0, T]`, `ε`-free. -/
theorem sixty_seven_percent_simple_on_critical_line_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.67 : ℝ) * (windowCount 0 T : ℝ) ≤ windowCountSimpleOnLine 0 T := by
  have hgap := sixty_seven_lt_two_sub_inv_mtConstant
  set ε : ℝ := 2 - mtConstant⁻¹ - 0.67 with hεdef
  obtain ⟨T₀, hT₀⟩ :=
    montgomery_taylor_simple_on_critical_line_cumulative ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 2 - 1 / mtConstant - ε = 0.67 := by rw [hεdef, one_div]; ring
  rwa [hred] at h

/-- **At most 33 % of the nontrivial zeroes of `ζ` lie off the critical line** (dyadic windows),
`ε`-free: for all large `T`, `N_off(T,2T) ≤ 0.33·N(T,2T)`.  The `ε`-form with `1/3` is
`RiemannHypothesis.one_third_off_critical_line`. -/
theorem thirty_three_percent_off_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (windowCountOffLine T (2 * T) : ℝ) ≤ (0.33 : ℝ) * windowCount T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := sixty_seven_percent_on_critical_line
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hsplit : (windowCountOffLine T (2 * T) : ℝ) + windowCountOnLine T (2 * T)
      = (windowCountDistinct T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine T (2 * T))
  have hle : (windowCountDistinct T (2 * T) : ℝ) ≤ (windowCount T (2 * T) : ℝ) := by
    exact_mod_cast windowCountDistinct_le_windowCount T (2 * T)
  linarith

end RiemannHypothesis

end
