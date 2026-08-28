/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeta23Bridge
import Zeta23.Main
import Zeta23.RvM.Statement

/-!
# Consequences of the two-thirds theorem: Hardy, Selberg, Levinson, Conrey

`RiemannHypothesis.Zeta23Bridge` states, in this repository's vocabulary, that at least two
thirds of the nontrivial zeroes of `ζ` are simple and on the critical line.  This file draws
the classical consequences, all of them unconditional:

* `tendsto_windowCount_atTop` — `N(0,T) → ∞` (Riemann–von Mangoldt);
* `tendsto_windowCountOnLine_atTop`, `tendsto_windowCountSimpleOnLine_atTop` — the number of
  zeroes on the critical line of ordinate in `(0,T]`, and the number of *simple* ones,
  tend to infinity;
* `infinite_criticalLineZeroSet` — **Hardy's theorem**: `ζ` has infinitely many zeroes on the
  critical line;
* `infinite_simpleCriticalLineZeroSet` — infinitely many of them are simple;
* `selberg_positive_proportion` — a positive proportion of the nontrivial zeroes lies on the
  critical line;
* `levinson_one_third`, `conrey_two_fifths` — the Levinson (`1/3`) and Conrey (`2/5`)
  proportions, here obtained as corollaries of the stronger `2/3` bound rather than by the
  mollifier method of those authors.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-- The zeroes of `ζ` on the critical line. -/
def criticalLineZeroSet : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}

/-- The *simple* zeroes of `ζ` on the critical line. -/
def simpleCriticalLineZeroSet : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ zeroMultiplicity ρ = 1}

lemma criticalLineZeroSet_subset_nontrivialZeroSet :
    criticalLineZeroSet ⊆ nontrivialZeroSet := by
  rintro ρ ⟨hzero, hre⟩
  exact ⟨hzero, by rw [hre]; norm_num, by rw [hre]; norm_num⟩

/-! ## The counts along the critical line diverge -/

/-- **Riemann–von Mangoldt**: the number of nontrivial zeroes of ordinate in `(0, T]`, counted
with multiplicity, tends to infinity. -/
theorem tendsto_windowCount_atTop :
    Tendsto (fun T : ℝ => (windowCount 0 T : ℝ)) atTop atTop := by
  simpa only [windowCount_eq] using
    Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam
      (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts)

/-- The number of *distinct zeroes on the critical line* of ordinate in `(0, T]` tends to
infinity: at least a third of all zeroes, of which there are eventually arbitrarily many. -/
theorem tendsto_windowCountOnLine_atTop :
    Tendsto (fun T : ℝ => (windowCountOnLine 0 T : ℝ)) atTop atTop := by
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line_cumulative (1 / 3) (by norm_num)
  refine tendsto_atTop_mono' _ ?_
    (tendsto_windowCount_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have h := hT₀ T hT
  have : (2 : ℝ) / 3 - 1 / 3 = 1 / 3 := by norm_num
  rwa [this] at h

/-- The number of *simple* zeroes on the critical line of ordinate in `(0, T]` tends to
infinity. -/
theorem tendsto_windowCountSimpleOnLine_atTop :
    Tendsto (fun T : ℝ => (windowCountSimpleOnLine 0 T : ℝ)) atTop atTop := by
  obtain ⟨T₀, hT₀⟩ := two_thirds_simple_on_critical_line_cumulative (1 / 3) (by norm_num)
  refine tendsto_atTop_mono' _ ?_
    (tendsto_windowCount_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have h := hT₀ T hT
  have : (2 : ℝ) / 3 - 1 / 3 = 1 / 3 := by norm_num
  rwa [this] at h

/-! ## Hardy's theorem and its strengthening to simple zeroes -/

/-- **Hardy's theorem**: `ζ` has infinitely many zeroes on the critical line.  (Here it comes
out of the two-thirds theorem: a positive proportion of a divergent count.) -/
theorem infinite_criticalLineZeroSet : criticalLineZeroSet.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨T, hT⟩ :=
    (tendsto_windowCountOnLine_atTop.eventually_ge_atTop
      ((criticalLineZeroSet.ncard : ℝ) + 1)).exists
  have hsub : windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ⊆ criticalLineZeroSet := by
    rintro ρ ⟨⟨⟨hzero, _, _⟩, _, _⟩, hre⟩
    exact ⟨hzero, hre⟩
  have hle : windowCountOnLine 0 T ≤ criticalLineZeroSet.ncard :=
    Set.ncard_le_ncard hsub hfin
  have : ((windowCountOnLine 0 T : ℕ) : ℝ) ≤ (criticalLineZeroSet.ncard : ℝ) := by
    exact_mod_cast hle
  linarith

/-- Infinitely many zeroes of `ζ` on the critical line are **simple**. -/
theorem infinite_simpleCriticalLineZeroSet : simpleCriticalLineZeroSet.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨T, hT⟩ :=
    (tendsto_windowCountSimpleOnLine_atTop.eventually_ge_atTop
      ((simpleCriticalLineZeroSet.ncard : ℝ) + 1)).exists
  have hsub : windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩ {ρ : ℂ | zeroMultiplicity ρ = 1} ⊆
      simpleCriticalLineZeroSet := by
    rintro ρ ⟨⟨⟨⟨hzero, _, _⟩, _, _⟩, hre⟩, hmult⟩
    exact ⟨hzero, hre, hmult⟩
  have hle : windowCountSimpleOnLine 0 T ≤ simpleCriticalLineZeroSet.ncard :=
    Set.ncard_le_ncard hsub hfin
  have : ((windowCountSimpleOnLine 0 T : ℕ) : ℝ) ≤ (simpleCriticalLineZeroSet.ncard : ℝ) := by
    exact_mod_cast hle
  linarith

/-! ## Positive proportion: Selberg, Levinson, Conrey -/

/-- **Selberg's theorem** (in the strong form proved here): a positive proportion — indeed at
least one third — of the nontrivial zeroes of `ζ` lies on the critical line. -/
theorem selberg_positive_proportion :
    ∃ c > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, c * (windowCount 0 T : ℝ) ≤ windowCountOnLine 0 T := by
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line_cumulative (1 / 3) (by norm_num)
  refine ⟨1 / 3, by norm_num, T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have : (2 : ℝ) / 3 - 1 / 3 = 1 / 3 := by norm_num
  rwa [this] at h

/-- **Levinson's constant**: at least one third of the nontrivial zeroes lie on the critical
line (dyadic windows).  A corollary of the two-thirds theorem, not a formalization of
Levinson's mollifier argument. -/
theorem levinson_one_third :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 / 3 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (hT₀ T hT)⟩
  have hN : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Conrey's constant**: at least two fifths of the nontrivial zeroes lie on the critical
line (dyadic windows).  A corollary of the two-thirds theorem, not a formalization of
Conrey's argument. -/
theorem conrey_two_fifths :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 5 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (hT₀ T hT)⟩
  have hN : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

end RiemannHypothesis

end
