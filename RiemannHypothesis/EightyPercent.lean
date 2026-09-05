/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeta23Bridge
import RiemannHypothesis.XiGrowth
import Zeta23.XiPrime.Final

/-!
# Where eighty per cent is reached

The two-thirds theorem of `RiemannHypothesis.Zeta23Bridge` puts `2/3 ≈ 66.7 %` of the
nontrivial zeroes of `ζ` on the critical line.  Raising *that* proportion to `80 %` is an
open research problem, and nothing in this repository proves it.  Two neighbouring
statistics, however, do pass `80 %` unconditionally, and this file records both in the
repository's own vocabulary.

* **At least 80 % of the nontrivial zeroes of `ζ` are distinct**
  (`eighty_percent_distinct`, `eighty_percent_distinct_cumulative`).  This is Theorem C
  (`5/6 ≈ 83.3 %`) with `ε = 1/30`.

* **At least 80 % of the zeroes of `ξ′` are simple and on the critical line**
  (`eighty_percent_simple_on_line_xiDeriv` and its cumulative form), and at least `90 %` of
  them are distinct (`ninety_percent_distinct_xiDeriv`).  Here `ξ′` is the derivative of the
  completed zeta function `ξ` of `RiemannHypothesis.XiGrowth`; the underlying constants,
  proved in the vendored `Zeta23` library, are `0.86864` and `0.93432`.  Every zero of `ξ′`
  lies in the open critical strip (`xiDerivFn_zero_mem_strip`), so these are statements about
  a set of zeroes directly comparable with the nontrivial zeroes of `ζ`.

The counting functions for `ξ′` are the analogues of those for `ζ`, over *all* zeroes of `ξ′`
in the ordinate window `(T₁, T₂]`.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## Eighty per cent of the zeroes of `ζ` are distinct -/

/-- **At least 80 % of the nontrivial zeroes of `ζ` are distinct** (dyadic windows): for all
large `T`, `0.8·N(T,2T) ≤ N_d(T,2T)`.  A consequence of Theorem C (`5/6`). -/
theorem eighty_percent_distinct :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ windowCountDistinct T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := five_sixths_distinct (1 / 30) (by norm_num)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have he : (5 : ℝ) / 6 - 1 / 30 = 0.8 := by norm_num
  rwa [he] at h

/-- **At least 80 % of the nontrivial zeroes of `ζ` are distinct**, cumulative form. -/
theorem eighty_percent_distinct_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, (0.8 : ℝ) * (windowCount 0 T : ℝ) ≤ windowCountDistinct 0 T := by
  obtain ⟨T₀, hT₀⟩ := five_sixths_distinct_cumulative (1 / 30) (by norm_num)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have he : (5 : ℝ) / 6 - 1 / 30 = 0.8 := by norm_num
  rwa [he] at h

/-! ## The zeroes of `ξ′` -/

/-- `ξ′`, the derivative of the completed zeta function `ξ` (an entire function). -/
def xiDerivFn : ℂ → ℂ := deriv xiFn

/-- The multiplicity of a zero of `ξ′`. -/
def xiDerivMultiplicity (ρ : ℂ) : ℕ := (analyticOrderAt xiDerivFn ρ).toNat

/-- The zeroes of `ξ′` with ordinate in the window `(T₁, T₂]` (all of them: no condition on
the real part is imposed, and none is needed — every zero of `ξ′` lies in the open critical
strip, `xiDerivFn_zero_mem_strip`). -/
def xiDerivWindowZeros (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | xiDerivFn ρ = 0 ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N_{ξ′}(T₁,T₂)`: the zeroes of `ξ′` in the window, with multiplicity. -/
def xiDerivWindowCount (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ xiDerivWindowZeros T₁ T₂, xiDerivMultiplicity ρ

/-- `N_{d,ξ′}(T₁,T₂)`: the distinct zeroes of `ξ′` in the window. -/
def xiDerivWindowCountDistinct (T₁ T₂ : ℝ) : ℕ := (xiDerivWindowZeros T₁ T₂).ncard

/-- `N₀ˢ_{ξ′}(T₁,T₂)`: the simple zeroes of `ξ′` in the window lying on the critical line. -/
def xiDerivWindowCountSimpleOnLine (T₁ T₂ : ℝ) : ℕ :=
  (xiDerivWindowZeros T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | xiDerivMultiplicity ρ = 1}).ncard

/-! ### Identification with the `Zeta23` objects -/

lemma xiFn_eq_zeta23_xi : xiFn = Zeta23.XiPrime.xi := by
  funext s
  simp only [xiFn, Zeta23.XiPrime.xi]
  ring

lemma xiDerivFn_eq : xiDerivFn = Zeta23.XiPrime.xiDeriv := by
  rw [xiDerivFn, Zeta23.XiPrime.xiDeriv, xiFn_eq_zeta23_xi]

lemma xiDerivMultiplicity_eq (ρ : ℂ) :
    xiDerivMultiplicity ρ = Zeta23.XiPrime.xiDerivMult ρ := by
  rw [xiDerivMultiplicity, Zeta23.XiPrime.xiDerivMult, xiDerivFn_eq]

lemma xiDerivWindowZeros_eq (T₁ T₂ : ℝ) :
    xiDerivWindowZeros T₁ T₂ = Zeta23.XiPrime.zerosIn T₁ T₂ := by
  ext ρ
  simp only [xiDerivWindowZeros, Zeta23.XiPrime.zerosIn, Zeta23.XiPrime.IsXiDerivZero,
    xiDerivFn_eq, Set.mem_ofPred_eq]

lemma xiDerivWindowCount_eq (T₁ T₂ : ℝ) :
    xiDerivWindowCount T₁ T₂ = Zeta23.XiPrime.Ncount T₁ T₂ := by
  simp only [xiDerivWindowCount, Zeta23.XiPrime.Ncount, xiDerivWindowZeros_eq,
    xiDerivMultiplicity_eq]

lemma xiDerivWindowCountDistinct_eq (T₁ T₂ : ℝ) :
    xiDerivWindowCountDistinct T₁ T₂ = Zeta23.XiPrime.Ndist T₁ T₂ := by
  rw [xiDerivWindowCountDistinct, Zeta23.XiPrime.Ndist, xiDerivWindowZeros_eq]

lemma xiDerivWindowCountSimpleOnLine_eq (T₁ T₂ : ℝ) :
    xiDerivWindowCountSimpleOnLine T₁ T₂ = Zeta23.XiPrime.N0simple T₁ T₂ := by
  simp only [xiDerivWindowCountSimpleOnLine, Zeta23.XiPrime.N0simple, xiDerivWindowZeros_eq,
    xiDerivMultiplicity_eq]

/-- Every zero of `ξ′` lies in the open critical strip. -/
theorem xiDerivFn_zero_mem_strip {ρ : ℂ} (h : xiDerivFn ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  Zeta23.XiPrime.xiDerivZerosInStrip_holds ρ (by rwa [← xiDerivFn_eq])

/-! ## Eighty per cent of the zeroes of `ξ′` are simple and on the critical line -/

/-- **At least 80 % of the zeroes of `ξ′` are simple and on the critical line** (dyadic
windows).  The proved constant is `0.86864`. -/
theorem eighty_percent_simple_on_line_xiDeriv :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (xiDerivWindowCount T (2 * T) : ℝ) ≤
        xiDerivWindowCountSimpleOnLine T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).1
  rw [xiDerivWindowCount_eq, xiDerivWindowCountSimpleOnLine_eq]
  have hN : (0 : ℝ) ≤ (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **At least 80 % of the zeroes of `ξ′` are simple and on the critical line**, cumulative
form. -/
theorem eighty_percent_simple_on_line_xiDeriv_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (xiDerivWindowCount 0 T : ℝ) ≤ xiDerivWindowCountSimpleOnLine 0 T := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_cumulative_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).1
  rw [xiDerivWindowCount_eq, xiDerivWindowCountSimpleOnLine_eq]
  have hN : (0 : ℝ) ≤ (Zeta23.XiPrime.Ncount 0 T : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **At least 90 % of the zeroes of `ξ′` are distinct** (dyadic windows).  The proved
constant is `0.93432`. -/
theorem ninety_percent_distinct_xiDeriv :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.9 : ℝ) * (xiDerivWindowCount T (2 * T) : ℝ) ≤
        xiDerivWindowCountDistinct T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).2
  rw [xiDerivWindowCount_eq, xiDerivWindowCountDistinct_eq]
  have hN : (0 : ℝ) ≤ (Zeta23.XiPrime.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **At least 90 % of the zeroes of `ξ′` are distinct**, cumulative form. -/
theorem ninety_percent_distinct_xiDeriv_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.9 : ℝ) * (xiDerivWindowCount 0 T : ℝ) ≤ xiDerivWindowCountDistinct 0 T := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_cumulative_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).2
  rw [xiDerivWindowCount_eq, xiDerivWindowCountDistinct_eq]
  have hN : (0 : ℝ) ≤ (Zeta23.XiPrime.Ncount 0 T : ℝ) := Nat.cast_nonneg _
  nlinarith

end RiemannHypothesis

end
