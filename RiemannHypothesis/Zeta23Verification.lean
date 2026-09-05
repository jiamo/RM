/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CriticalLine

/-!
# The two-thirds theorem, checked against the classical normalization

The strongest results of this repository are imported from the vendored `Zeta23` library
through `RiemannHypothesis.Zeta23Bridge`, and every one of them is a *ratio*: Theorem A says
`(2/3 − ε)·N(T, 2T) ≤ N₀*(T, 2T)`.  A ratio statement is only as strong as its denominator: if
`windowCount` were not the classical zero-counting function `N`, or if it were eventually zero,
the bound would say nothing at all, and no axiom check could detect that — the statement would
be true, fully proved, and empty.

This file removes that possibility by turning the ratio into an absolute count, using nothing
but the Riemann–von Mangoldt formula, which the vendored library also proves unconditionally:

* `windowCount_sub_mainTerm_le` — the classical asymptotic, in this repository's own
  vocabulary: `|N(T, 2T) − (T/2π)·(log(T/2π) + 2log 2 − 1)| ≤ C log T` for all large `T`.
  The main term is the classical `N(2T) − N(T)`, so `windowCount` *is* the literature's `N`;
* `eventually_windowCount_ge` — in particular `N(T, 2T) ≥ (T/4π) log T`, so the denominator of
  Theorem A grows like `T log T` and the theorem is not vacuous;
* `eventually_windowCountOnLine_ge` — the two-thirds theorem in absolute form: for all large
  `T` there are at least `(T/8π)·log T` **distinct** zeroes of `ζ` on the critical line with
  ordinate in `(T, 2T]`;
* `eventually_windowCountSimpleOnLine_ge` — the same count of *simple* zeroes on the line,
  from Theorem B.

Nothing here is assumed: the two inputs are `RiemannHypothesis.two_thirds_on_critical_line`
(Theorem A) and `Zeta23.riemannVonMangoldt_zeta`, both unconditional theorems, and the
constants are explicit.  The counting functions are this repository's own
(`RiemannHypothesis.windowCount` and friends), defined directly against Mathlib's
`riemannZeta` and `analyticOrderAt`.
-/

noncomputable section

open Filter Real
open scoped Topology

namespace RiemannHypothesis

/-- The classical main term of `N(T, 2T)`: `(T/2π)·(log(T/2π) + 2log 2 − 1)`, which is
`N(2T) − N(T)` in the Riemann–von Mangoldt formula `N(T) = (T/2π)log(T/2π) − T/2π + O(log T)`. -/
def windowMainTerm (T : ℝ) : ℝ := T / (2 * π) * (Real.log (T / (2 * π)) + 2 * Real.log 2 - 1)

/-- **Riemann–von Mangoldt**, in this repository's vocabulary: the number of nontrivial zeroes
of `ζ` with ordinate in `(T, 2T]`, counted with multiplicity, differs from the classical main
term by at most `C log T`.  This is what identifies `windowCount` with the `N` of the
literature. -/
theorem windowCount_sub_mainTerm_le :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀, |(windowCount T (2 * T) : ℝ) - windowMainTerm T| ≤ C * Real.log T := by
  obtain ⟨C, T₀, h⟩ := Zeta23.riemannVonMangoldt_zeta.main
  refine ⟨C, T₀, fun T hT => ?_⟩
  have := h T hT
  simpa only [Zeta23.zetaZeroConfig_N, windowCount_eq, windowMainTerm, Zeta23.ell1, Zeta23.l]
    using this

/-- `log(T/2π) + 2 log 2 − 1 = log T − c₀` with `c₀ = log(2π) + 1 − 2 log 2 > 0`. -/
private lemma windowMainTerm_eq (T : ℝ) (hT : 0 < T) :
    windowMainTerm T = T / (2 * π) * (Real.log T - (Real.log (2 * π) + 1 - 2 * Real.log 2)) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [windowMainTerm, Real.log_div hT.ne' hpi.ne']
  ring

/-- The denominator of the two-thirds theorem is genuinely of size `T log T`: for all large
`T`, at least `(T/4π)·log T` nontrivial zeroes (with multiplicity) have ordinate in `(T, 2T]`.
(The true size is `(T/2π)(log T − c₀)`; half of the main term is kept, so that the explicit
threshold stays simple.) -/
theorem eventually_windowCount_ge :
    ∀ᶠ T in atTop, T / (4 * π) * Real.log T ≤ (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hC⟩ := windowCount_sub_mainTerm_le
  set c₀ : ℝ := Real.log (2 * π) + 1 - 2 * Real.log 2 with hc₀
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpi : (0 : ℝ) < 2 * π := by positivity
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.exp (4 * |c₀| + 1)), eventually_ge_atTop (8 * π * C' + 1)]
    with T hT hT1 hTexp hTC
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hlog : Real.log T ≥ 4 * |c₀| + 1 := by
    have h1 : Real.log (Real.exp (4 * |c₀| + 1)) ≤ Real.log T :=
      Real.log_le_log (Real.exp_pos _) hTexp
    simpa using h1
  have hlogpos : 0 < Real.log T := by
    have : (0 : ℝ) ≤ |c₀| := abs_nonneg _
    linarith
  have hA : 0 < T / (2 * π) := div_pos hT0 hpi
  have hbound := hC T hT
  have habs : (windowCount T (2 * T) : ℝ) ≥ windowMainTerm T - C * Real.log T := by
    have := abs_le.mp hbound
    linarith [this.1]
  rw [windowMainTerm_eq T hT0, ← hc₀] at habs
  have hCC : C * Real.log T ≤ C' * Real.log T :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos.le
  have hTC' : 4 * C' ≤ T / (2 * π) := by
    rw [le_div_iff₀ hpi]
    nlinarith [Real.pi_pos, hC'0]
  have hc₀le : c₀ ≤ |c₀| := le_abs_self c₀
  have hhalf : T / (4 * π) * Real.log T = (T / (2 * π) * Real.log T) / 2 := by
    have : (4 : ℝ) * π = 2 * (2 * π) := by ring
    rw [this]
    field_simp
  rw [hhalf]
  -- `A(log T − c₀) − C' log T ≥ A log T / 2`, from `log T ≥ 4|c₀|` and `A ≥ 4C'`
  nlinarith [hA, hlogpos, habs, hCC, hTC', hc₀le, abs_nonneg c₀]

/-- **Theorem A in absolute form.**  For all large `T` there are at least `(T/8π)·log T`
*distinct* zeroes of `ζ` on the critical line with ordinate in `(T, 2T]`.  Nothing is assumed:
this is the two-thirds theorem against the Riemann–von Mangoldt count. -/
theorem eventually_windowCountOnLine_ge :
    ∀ᶠ T in atTop, T / (8 * π) * Real.log T ≤ (windowCountOnLine T (2 * T) : ℝ) := by
  obtain ⟨T₁, hT₁⟩ := two_thirds_on_critical_line (1 / 6) (by norm_num)
  filter_upwards [eventually_windowCount_ge, eventually_ge_atTop T₁] with T hN hT
  have h := hT₁ T hT
  have hhalf : (2 : ℝ) / 3 - 1 / 6 = 1 / 2 := by norm_num
  rw [hhalf] at h
  have hrw : T / (8 * π) * Real.log T = (1 / 2) * (T / (4 * π) * Real.log T) := by
    have : (8 : ℝ) * π = 2 * (4 * π) := by ring
    rw [this]
    field_simp
  rw [hrw]
  refine le_trans ?_ h
  nlinarith [hN]

/-- **Theorem B in absolute form**: for all large `T` there are at least `(T/8π)·log T`
*simple* zeroes of `ζ` on the critical line with ordinate in `(T, 2T]`. -/
theorem eventually_windowCountSimpleOnLine_ge :
    ∀ᶠ T in atTop, T / (8 * π) * Real.log T ≤ (windowCountSimpleOnLine T (2 * T) : ℝ) := by
  obtain ⟨T₁, hT₁⟩ := two_thirds_simple_on_critical_line (1 / 6) (by norm_num)
  filter_upwards [eventually_windowCount_ge, eventually_ge_atTop T₁] with T hN hT
  have h := hT₁ T hT
  have hhalf : (2 : ℝ) / 3 - 1 / 6 = 1 / 2 := by norm_num
  rw [hhalf] at h
  have hrw : T / (8 * π) * Real.log T = (1 / 2) * (T / (4 * π) * Real.log T) := by
    have : (8 : ℝ) * π = 2 * (4 * π) := by ring
    rw [this]
    field_simp
  rw [hrw]
  refine le_trans ?_ h
  nlinarith [hN]

end RiemannHypothesis

end
