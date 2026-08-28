/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Known partial results toward the Riemann hypothesis, stated precisely

The Riemann hypothesis itself is open; the propositions in this file are the *best results
known toward it*, stated in Lean so that the gap between them and the conjecture is pinned
down exactly.  Like `RiemannHypothesis.ZetaForm`, all of them are unproved here: proving any
of them in Lean would require the full apparatus of analytic number theory (Perron's formula,
approximate functional equations, mollifiers, …), which Mathlib does not yet contain.  What
this file provides is the *statement* — the `Prop` whose proof the literature claims.

## The propositions

* `ZeroFreeRegion` — de la Vallée Poussin (1899): there is an absolute constant `c > 0` such
  that `ζ(s) ≠ 0` for `Re(s) > 1 − c / log|Im(s)|`, uniformly for `|Im(s)| ≥ 3`.

* `HardyTheorem` — Hardy (1914): there are infinitely many zeroes of `ζ` on the critical
  line `Re(s) = 1/2`.

* `zeroCount T` / `criticalZeroCount T` — the number of zeroes of `ζ` with imaginary part in
  `(0, T)`, and the number of those that lie on the critical line.  (The trivial zeroes are
  excluded by `0 < Im(s)`; for large `T` these sets are finite, a fact not needed to state
  the propositions.)

* `PositiveProportionOnCriticalLine` — Selberg (1942): a positive proportion of the zeroes
  lie on the critical line, i.e. `liminf_T N₀(T)/N(T) > 0`.

* `TwoFifthsOnCriticalLine` — Conrey (1989): at least `2/5` of the zeroes lie on the critical
  line, i.e. `liminf_T N₀(T)/N(T) ≥ 2/5`.  (Improved to about 41% in the 2010s — Bui–Conrey–
  Young, Feng, Platt–Trudgian.)

* `AlmostAllZerosNearCriticalLine` — Bohr–Landau / Selberg density theorem: for every
  `δ > 0`, the number of zeroes with imaginary part in `(0, T)` and distance at least `δ`
  from the critical line is `o(T)` as `T → ∞`.

* `VerifiedUpToHeight` — the numerical verification (Gourdon 2004; Platt–Trudgian 2021,
  rigorous interval arithmetic): every zero with imaginary part below `H` lies on the
  critical line, for `H` around `10^12`–`10^13`.

For contrast, everything that *is* proved in this repository is in `RiemannHypothesis.Main`:
the equivalence of the zeta form, the strip form and the eta form of the conjecture, together
with the location of the trivial zeroes (`RiemannHypothesis.Zeros`).  None of the propositions
below is implied by those equivalences, and none implies the Riemann hypothesis itself (except
`VerifiedUpToHeight`, which is a finite check).
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology MeasureTheory ENNReal

namespace RiemannHypothesis

open Complex

/-- **The de la Vallée Poussin zero-free region**: there is an absolute constant `c > 0` such
that `ζ(s) ≠ 0` whenever `Re(s) > 1 − c / log|Im(s)|` and `|Im(s)| ≥ 3`. -/
def ZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0

/-- **Hardy's theorem**: there are infinitely many zeroes of `ζ` on the critical line
`Re(s) = 1/2`. -/
def HardyTheorem : Prop :=
  Infinite {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2}

/-- The number of zeroes of `ζ` with imaginary part in `(0, T)`.  (All non-trivial zeroes lie
in the critical strip, so this counts the non-trivial zeroes below height `T`.) -/
def zeroCount (T : ℝ) : ℕ :=
  ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T}

/-- The number of zeroes of `ζ` with imaginary part in `(0, T)` that lie on the critical
line `Re(s) = 1/2`. -/
def criticalZeroCount (T : ℝ) : ℕ :=
  ncard {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ 0 < s.im ∧ s.im < T}

/-- **Selberg's theorem**: a positive proportion of the zeroes of `ζ` lie on the critical
line, i.e. `liminf_T N₀(T)/N(T) > 0`. -/
def PositiveProportionOnCriticalLine : Prop :=
  0 < liminf (fun T : ℝ => (criticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop

/-- **Conrey's theorem**: at least `2/5` of the zeroes of `ζ` lie on the critical line,
i.e. `liminf_T N₀(T)/N(T) ≥ 2/5`. -/
def TwoFifthsOnCriticalLine : Prop :=
  (2 / 5 : ℝ) ≤ liminf (fun T : ℝ => (criticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop

/-- **Bohr–Landau / Selberg density theorem**: for every `δ > 0`, the number of zeroes of `ζ`
with imaginary part in `(0, T)` and distance at least `δ` from the critical line is `o(T)`
as `T → ∞`. -/
def AlmostAllZerosNearCriticalLine : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun T : ℝ => (ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
        δ ≤ |s.re - 1 / 2|} : ℝ) / T) atTop (𝓝 0)

/-- The Riemann hypothesis holds for every zero of `ζ` with imaginary part below `H`.  This is
the form of the numerical verification (Gourdon 2004 verified up to about `10^13`; Platt–
Trudgian 2021 up to `3 × 10^12` with rigorous interval arithmetic). -/
def VerifiedUpToHeight (H : ℝ) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → s.im < H → s.re = 1 / 2

/-- The GUE pair-correlation density `R2(u) = 1 - (sin(pi u)/(pi u))^2` (Dyson), conjectured
by Montgomery to describe the pair correlation of the non-trivial zeroes. -/
noncomputable def guePairCorrelationDensity (u : ℝ) : ℝ :=
  1 - (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2

/-- **Montgomery's pair correlation conjecture**, in the smoothed counting form tested
numerically by Odlyzko: for fixed `0 < a < b`, the proportion of ordered pairs of non-trivial
zeroes (counted with multiplicity) with imaginary parts below `T` and unfolded distance in
`(a, b)` tends to `∫ₐᵇ R2(u) du` as `T → ∞`.  The unfolding uses the local density
`log(T/2π)/(2π)`; equivalently the normalized distance of a pair is
`(γ - γ') · log(T/2π) / (2π)`. -/
def PairCorrelationConjecture : Prop :=
  ∀ a b : ℝ, 0 < a → a < b →
    Tendsto (fun T : ℝ =>
      (ncard {p : ℂ × ℂ |
        riemannZeta p.1 = 0 ∧ riemannZeta p.2 = 0 ∧ 0 < p.1.im ∧ p.1.im < T ∧
        0 < p.2.im ∧ p.2.im < T ∧ p.1 ≠ p.2 ∧
        a * (2 * Real.pi / Real.log (T / (2 * Real.pi))) ≤ |p.1.im - p.2.im| ∧
        |p.1.im - p.2.im| ≤ b * (2 * Real.pi / Real.log (T / (2 * Real.pi)))} : ℝ) /
          (zeroCount T : ℝ))
      atTop (𝓝 (∫ u in Set.Ioc a b, guePairCorrelationDensity u))

/-- **Selberg's central limit theorem**: as `t` ranges over `[T, 2T]`, the normalized
`log |ζ(1/2 + i t)| / sqrt(1/2 log log T)` is asymptotically standard normal.  Stated in
the proportion form (Radziwill-Soundararajan 2017 gave a short proof): for every real `x`,
the proportion of `t ∈ [T, 2T]` with the normalized value at most `x` tends to `Phi(x)`,
the standard normal CDF.  The zeroes of `ζ` on the critical line form a set of measure zero,
so `log` is well-defined up to a null set and the statement is unaffected by its values
there. -/
def SelbergCentralLimit : Prop :=
  ∀ x : ℝ,
    Tendsto (fun T : ℝ =>
      (volume {t : ℝ | T ≤ t ∧ t ≤ 2 * T ∧
        Real.log ‖riemannZeta (1 / 2 + t * I)‖ ≤
          x * Real.sqrt (1 / 2 * Real.log (Real.log T))} : ℝ≥0∞).toReal / T)
      atTop (𝓝 ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ t in Set.Iic x, Real.exp (-(t ^ 2) / 2)))


end RiemannHypothesis

end
