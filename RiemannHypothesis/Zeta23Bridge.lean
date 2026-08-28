/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroSum
import Zeta23.Unconditional
import Zeta23.FinalMult
import Zeta23.ThmD.Final
import Zeta23.ThmD.Mult
import Zeta23.ThmE.Final
import Zeta23.ThmE.Mult
import Zeta23.ThmDE.Final
import Zeta23.ThmDE.Mult

/-!
# Two thirds of the zeroes are simple and on the critical line

This file restates, in this repository's own vocabulary, the headline results of the
`Zeta23` library (vendored under `vendor/zeta23`, Apache 2.0; see `vendor/zeta23/NOTICE`),
which formalizes the paper *"More than two thirds of the zeros of the Riemann zeta function
are simple and on the critical line"*.  Nothing here is assumed: every statement below is a
theorem with no hypotheses beyond, in the Dirichlet case, primitivity of the character.

## The counting functions

All counting is done over the nontrivial zeroes of `ζ` — the elements of this repository's
`nontrivialZeroSet`, i.e. the zeroes in the open critical strip — whose ordinate lies in a
window `(T₁, T₂]`:

* `zeroMultiplicity ρ`: the order of vanishing of `ζ` at `ρ`, through Mathlib's
  `analyticOrderAt`;
* `windowZeros T₁ T₂`: the nontrivial zeroes with `T₁ < im ρ ≤ T₂`;
* `windowCount T₁ T₂` (`N`): their number *with multiplicity*;
* `windowCountDistinct T₁ T₂` (`N_d`): the number of *distinct* such zeroes;
* `windowCountOnLine T₁ T₂` (`N₀*`): the distinct ones *on the critical line*;
* `windowCountSimpleOnLine T₁ T₂` (`N₀ˢ`): those on the line that are *simple*.

The same six definitions are made for a Dirichlet `L`-function (Mathlib's
`DirichletCharacter.LFunction`), with an `L` suffix.

## The results

Writing "`liminf_{T→∞} X(T)/N(T) ≥ c`" in the `ε`-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`, on dyadic windows `(T, 2T]` and on
cumulative windows `(0, T]`:

* `two_thirds_on_critical_line`  (Theorem A): `N₀*/N ≥ 2/3`;
* `two_thirds_simple_on_critical_line` (Theorem B): `N₀ˢ/N ≥ 2/3`;
* `five_sixths_distinct` (Theorem C): `N_d/N ≥ 5/6`;
* `montgomery_taylor_*` (Theorem D): the same three counts against the optimal
  Montgomery–Taylor window, with the constants `2 − 1/c₁*` and `(3 − 1/c₁*)/2`, where
  `c₁* = mtConstant`;
* `dirichlet_*` (Theorem E): the analogues for `L(s, χ)`, `χ` primitive modulo `q > 1`.

Consequences of these bounds in this repository's language — Hardy's theorem, positive
proportion, the Levinson and Conrey constants — are in `RiemannHypothesis.CriticalLine`.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## Counting functions for `ζ` -/

/-- `m_ρ`, the multiplicity of a zero `ρ` of `ζ`: the order of vanishing of `ζ` at `ρ`,
through Mathlib's `analyticOrderAt` (`toNat` sends `⊤` to `0`). -/
def zeroMultiplicity (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeroes of `ζ` with ordinate in the window `(T₁, T₂]`. -/
def windowZeros (T₁ T₂ : ℝ) : Set ℂ := {ρ ∈ nontrivialZeroSet | T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N(T₁, T₂)`: the number of nontrivial zeroes with `T₁ < im ρ ≤ T₂`, **with
multiplicity**. -/
def windowCount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ windowZeros T₁ T₂, zeroMultiplicity ρ

/-- `N_d(T₁, T₂)`: the number of *distinct* nontrivial zeroes with `T₁ < im ρ ≤ T₂`. -/
def windowCountDistinct (T₁ T₂ : ℝ) : ℕ := (windowZeros T₁ T₂).ncard

/-- `N₀*(T₁, T₂)`: the number of distinct nontrivial zeroes with `T₁ < im ρ ≤ T₂` lying on
the critical line. -/
def windowCountOnLine (T₁ T₂ : ℝ) : ℕ := (windowZeros T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- `N₀ˢ(T₁, T₂)`: the number of *simple* zeroes on the critical line with
`T₁ < im ρ ≤ T₂`. -/
def windowCountSimpleOnLine (T₁ T₂ : ℝ) : ℕ :=
  (windowZeros T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultiplicity ρ = 1}).ncard

/-! ### Identification with the `Zeta23` counting functions -/

lemma zeroMultiplicity_eq (ρ : ℂ) : zeroMultiplicity ρ = Zeta23.zeroMult ρ := rfl

lemma windowZeros_eq (T₁ T₂ : ℝ) : windowZeros T₁ T₂ = Zeta23.zerosIn T₁ T₂ := by
  ext ρ
  simp only [windowZeros, nontrivialZeroSet, Zeta23.zerosIn, Zeta23.IsNontrivialZero,
    Set.mem_setOf_eq]

lemma windowCount_eq (T₁ T₂ : ℝ) : windowCount T₁ T₂ = Zeta23.Ncount T₁ T₂ := by
  simp only [windowCount, Zeta23.Ncount, windowZeros_eq, zeroMultiplicity]
  rfl

lemma windowCountDistinct_eq (T₁ T₂ : ℝ) : windowCountDistinct T₁ T₂ = Zeta23.Ndist T₁ T₂ := by
  simp [windowCountDistinct, Zeta23.Ndist, windowZeros_eq]

lemma windowCountOnLine_eq (T₁ T₂ : ℝ) : windowCountOnLine T₁ T₂ = Zeta23.N0star T₁ T₂ := by
  simp [windowCountOnLine, Zeta23.N0star, windowZeros_eq]

lemma windowCountSimpleOnLine_eq (T₁ T₂ : ℝ) :
    windowCountSimpleOnLine T₁ T₂ = Zeta23.N0simple T₁ T₂ := by
  simp only [windowCountSimpleOnLine, Zeta23.N0simple, windowZeros_eq]
  rfl

/-! ## Counting functions for a Dirichlet `L`-function -/

section Dirichlet

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The multiplicity of a zero of `L(·, χ)`. -/
def zeroMultiplicityL (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- The nontrivial zeroes of `L(·, χ)` — those in the open critical strip — with ordinate in
the window `(T₁, T₂]`. -/
def windowZerosL (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N_χ(T₁, T₂)`: the nontrivial zeroes of `L(·, χ)` in the window, with multiplicity. -/
def windowCountL (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ windowZerosL χ T₁ T₂, zeroMultiplicityL χ ρ

/-- `N_{d,χ}`: the distinct nontrivial zeroes of `L(·, χ)` in the window. -/
def windowCountDistinctL (T₁ T₂ : ℝ) : ℕ := (windowZerosL χ T₁ T₂).ncard

/-- `N₀*_χ`: the distinct zeroes of `L(·, χ)` in the window lying on the critical line. -/
def windowCountOnLineL (T₁ T₂ : ℝ) : ℕ :=
  (windowZerosL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- `N₀ˢ_χ`: the simple zeroes of `L(·, χ)` in the window lying on the critical line. -/
def windowCountSimpleOnLineL (T₁ T₂ : ℝ) : ℕ :=
  (windowZerosL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultiplicityL χ ρ = 1}).ncard

lemma windowZerosL_eq (T₁ T₂ : ℝ) : windowZerosL χ T₁ T₂ = Zeta23.ThmE.zerosInL χ T₁ T₂ := by
  ext ρ
  simp only [windowZerosL, Zeta23.ThmE.zerosInL, Zeta23.ThmE.IsNontrivialZeroL,
    Set.mem_setOf_eq]
  tauto

lemma windowCountL_eq (T₁ T₂ : ℝ) : windowCountL χ T₁ T₂ = Zeta23.ThmE.NcountL χ T₁ T₂ := by
  simp only [windowCountL, Zeta23.ThmE.NcountL, windowZerosL_eq, zeroMultiplicityL]
  rfl

lemma windowCountDistinctL_eq (T₁ T₂ : ℝ) :
    windowCountDistinctL χ T₁ T₂ = Zeta23.ThmE.NdistL χ T₁ T₂ := by
  simp [windowCountDistinctL, Zeta23.ThmE.NdistL, windowZerosL_eq]

lemma windowCountOnLineL_eq (T₁ T₂ : ℝ) :
    windowCountOnLineL χ T₁ T₂ = Zeta23.ThmE.N0starL χ T₁ T₂ := by
  simp [windowCountOnLineL, Zeta23.ThmE.N0starL, windowZerosL_eq]

lemma windowCountSimpleOnLineL_eq (T₁ T₂ : ℝ) :
    windowCountSimpleOnLineL χ T₁ T₂ = Zeta23.ThmE.N0simpleL χ T₁ T₂ := by
  simp only [windowCountSimpleOnLineL, Zeta23.ThmE.N0simpleL, windowZerosL_eq]
  rfl

end Dirichlet

/-! ## The Montgomery–Taylor constant -/

/-- `c₁* = √2·tan ϑ / (1 + ϑ·tan ϑ)` at `ϑ = 1/√2` (numerically `0.7532960…`), the constant
of the optimal window of Theorem D. -/
def mtConstant : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

lemma mtConstant_eq_cStar_one : Zeta23.ThmD.cStar 1 = mtConstant := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold mtConstant Zeta23.ThmD.theta
  rfl

/-! ## Theorem A: at least two thirds of the zeroes are on the critical line -/

/-- **Theorem A** (dyadic windows): for every `ε > 0` and all large `T`,
`(2/3 − ε)·N(T, 2T) ≤ N₀*(T, 2T)`; that is, `liminf N₀*(T,2T)/N(T,2T) ≥ 2/3`.  The zeroes are
counted with multiplicity on the left and as distinct points of the critical line on the
right. -/
theorem two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T) := by
  simpa only [windowCount_eq, windowCountOnLine_eq] using Zeta23.thmA₀

/-- **Theorem A**, cumulative form: `liminf N₀*(T)/N(T) ≥ 2/3` over the windows `(0, T]`. -/
theorem two_thirds_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCount 0 T : ℝ) ≤ windowCountOnLine 0 T := by
  simpa only [windowCount_eq, windowCountOnLine_eq] using Zeta23.thmA₀_cumulative

/-! ## Theorem B: at least two thirds of the zeroes are simple and on the critical line -/

/-- **Theorem B** (dyadic windows): `liminf N₀ˢ(T,2T)/N(T,2T) ≥ 2/3` — at least two thirds of
the nontrivial zeroes of `ζ` are simple *and* on the critical line. -/
theorem two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountSimpleOnLine T (2 * T) := by
  simpa only [windowCount_eq, windowCountSimpleOnLine_eq] using Zeta23.thmB₀_mult

/-- **Theorem B**, cumulative form: `liminf N₀ˢ(T)/N(T) ≥ 2/3`. -/
theorem two_thirds_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCount 0 T : ℝ) ≤ windowCountSimpleOnLine 0 T := by
  simpa only [windowCount_eq, windowCountSimpleOnLine_eq] using Zeta23.thmB₀_mult_cumulative

/-! ## Theorem C: at least five sixths of the zeroes are distinct -/

/-- **Theorem C** (dyadic windows): `liminf N_d(T,2T)/N(T,2T) ≥ 5/6`. -/
theorem five_sixths_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountDistinct T (2 * T) := by
  simpa only [windowCount_eq, windowCountDistinct_eq] using Zeta23.thmC₀_mult

/-- **Theorem C**, cumulative form: `liminf N_d(T)/N(T) ≥ 5/6`. -/
theorem five_sixths_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (windowCount 0 T : ℝ) ≤ windowCountDistinct 0 T := by
  simpa only [windowCount_eq, windowCountDistinct_eq] using Zeta23.thmC₀_mult_cumulative

/-! ## Theorem D: the optimal (Montgomery–Taylor) window -/

/-- **Theorem D**: with the optimal window, `liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁*`
(numerically `0.67250…`). -/
theorem montgomery_taylor_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / mtConstant - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀
  simp only [Zeta23.ThmD.HD, mtConstant_eq_cStar_one] at h
  simpa only [windowCount_eq, windowCountOnLine_eq] using h

/-- **Theorem D** for simple zeroes on the line: `liminf N₀ˢ(T,2T)/N(T,2T) ≥ 2 − 1/c₁*`. -/
theorem montgomery_taylor_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / mtConstant - ε) * (windowCount T (2 * T) : ℝ) ≤
        windowCountSimpleOnLine T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult
  simp only [Zeta23.ThmD.HD, mtConstant_eq_cStar_one] at h
  simpa only [windowCount_eq, windowCountSimpleOnLine_eq] using h

/-- **Theorem D** for simple zeroes on the line, cumulative form. -/
theorem montgomery_taylor_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / mtConstant - ε) * (windowCount 0 T : ℝ) ≤ windowCountSimpleOnLine 0 T := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult_cumulative
  simp only [Zeta23.ThmD.HD, mtConstant_eq_cStar_one] at h
  simpa only [windowCount_eq, windowCountSimpleOnLine_eq] using h

/-- **Theorem D** for distinct zeroes: `liminf N_d(T,2T)/N(T,2T) ≥ (3 − 1/c₁*)/2`
(numerically `0.83625…`). -/
theorem montgomery_taylor_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - mtConstant⁻¹ / 2 - ε) * (windowCount T (2 * T) : ℝ) ≤
        windowCountDistinct T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult
  simp only [Zeta23.ThmD.GD, mtConstant_eq_cStar_one] at h
  simpa only [windowCount_eq, windowCountDistinct_eq] using h

/-- **Theorem D** for distinct zeroes, cumulative form. -/
theorem montgomery_taylor_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - mtConstant⁻¹ / 2 - ε) * (windowCount 0 T : ℝ) ≤ windowCountDistinct 0 T := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult_cumulative
  simp only [Zeta23.ThmD.GD, mtConstant_eq_cStar_one] at h
  simpa only [windowCount_eq, windowCountDistinct_eq] using h

/-! ## Theorem E: Dirichlet `L`-functions -/

section DirichletTheorems

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive)

include hq hχ

/-- **Theorem E** (A for `L(s,χ)`): for `χ` primitive modulo `q > 1`,
`liminf N₀*_χ(T,2T)/N_χ(T,2T) ≥ 2/3`. -/
theorem dirichlet_two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCountL χ T (2 * T) : ℝ) ≤ windowCountOnLineL χ T (2 * T) := by
  simpa only [windowCountL_eq, windowCountOnLineL_eq] using Zeta23.ThmE.thmE_A₀ hq hχ

/-- **Theorem E** (B for `L(s,χ)`): at least two thirds of the nontrivial zeroes of `L(s,χ)`
are simple and on the critical line. -/
theorem dirichlet_two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCountL χ T (2 * T) : ℝ) ≤ windowCountSimpleOnLineL χ T (2 * T) := by
  simpa only [windowCountL_eq, windowCountSimpleOnLineL_eq] using Zeta23.ThmE.thmE_B₀_mult hq hχ

/-- **Theorem E** (C for `L(s,χ)`): at least five sixths of the nontrivial zeroes of `L(s,χ)`
are distinct. -/
theorem dirichlet_five_sixths_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (windowCountL χ T (2 * T) : ℝ) ≤ windowCountDistinctL χ T (2 * T) := by
  simpa only [windowCountL_eq, windowCountDistinctL_eq] using Zeta23.ThmE.thmE_C₀_mult hq hχ

/-- **Theorem E** (D for `L(s,χ)`): with the optimal window,
`liminf N₀*_χ(T,2T)/N_χ(T,2T) ≥ 2 − 1/c₁*`. -/
theorem dirichlet_montgomery_taylor_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / mtConstant - ε) * (windowCountL χ T (2 * T) : ℝ) ≤
        windowCountOnLineL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀ (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, mtConstant_eq_cStar_one] at h
  simpa only [windowCountL_eq, windowCountOnLineL_eq] using h

/-- **Theorem E** (D for `L(s,χ)`, simple zeroes on the line). -/
theorem dirichlet_montgomery_taylor_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / mtConstant - ε) * (windowCountL χ T (2 * T) : ℝ) ≤
        windowCountSimpleOnLineL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_simple_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, mtConstant_eq_cStar_one] at h
  simpa only [windowCountL_eq, windowCountSimpleOnLineL_eq] using h

/-- **Theorem E** (D for `L(s,χ)`, distinct zeroes). -/
theorem dirichlet_montgomery_taylor_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - mtConstant⁻¹ / 2 - ε) * (windowCountL χ T (2 * T) : ℝ) ≤
        windowCountDistinctL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_dist_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.GD, mtConstant_eq_cStar_one] at h
  simpa only [windowCountL_eq, windowCountDistinctL_eq] using h

end DirichletTheorems

end RiemannHypothesis

end
