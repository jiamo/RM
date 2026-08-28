/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Riemann Hypothesis, precisely stated

This file fixes the *statements* around which the development is built.  Everything here is
definitional: no mathematical claim is made beyond "these are the propositions that various
authors call the Riemann hypothesis, or one of its reformulations".

## The main definitions

* `dirichletEta s`: the Dirichlet eta function `η(s)`, defined by the absolutely convergent
  series obtained by grouping the terms of the classical alternating series
  `∑' n, (-1)^n / (n+1)^s` in pairs:
  `η(s) = ∑' j, ((2j+1)^(-s) - (2j+2)^(-s))`.
  For `0 < re s` this paired series converges absolutely (proved in
  `RiemannHypothesis.Eta`), so the value is meaningful on the right half-plane.  The classical
  alternating-series representation is recovered for `1 < re s` in
  `RiemannHypothesis.Eta.dirichletEta_eq_tsum_alternating_of_one_lt_re`; we cannot use the
  alternating series as the definition because Mathlib's `tsum` is *unconditional*, and the
  alternating series is only conditionally convergent in the strip.

* `ZetaForm`: the classical statement, in terms of the analytically continued Riemann zeta
  function of Mathlib (`RiemannHypothesis`, defined in
  `Mathlib.NumberTheory.LSeries.RiemannZeta`): every zero of `ζ` other than the trivial zeroes
  at the negative even integers and the pole at `s = 1` lies on the critical line
  `re s = 1/2`.

* `ZetaStripForm`: the same claim restricted to the critical strip `0 < re s < 1`: every zero
  of `ζ` inside the strip lies on the critical line.  This is the formulation most often seen
  in textbooks.

* `EtaForm`: the same claim in terms of the Dirichlet eta function: every zero of `η` inside
  the critical strip lies on the critical line.  Because the factor `1 - 2^(1-s)` relating
  `η` to `ζ` has no zeroes inside the strip, this is equivalent to the zeta form; the
  equivalence is proved in `RiemannHypothesis.Main`.

All three forms are definitions of a `Prop`; none is proved in this repository.  This is the
honest state of affairs: the Riemann hypothesis is open, and what is formalized here is its
precise statement, together with the *equivalence* of its standard formulations.
-/

noncomputable section

namespace RiemannHypothesis

open Complex

/-- The `j`-th pair of terms of the eta series: `(2j+1)^(-s) - (2j+2)^(-s)`.  The series
over `j` of these terms converges absolutely for `0 < re s` (see
`RiemannHypothesis.Eta.summable_pairedTerm`). -/
def pairedTerm (j : ℕ) (s : ℂ) : ℂ :=
  ((2 * j + 1 : ℕ) : ℂ) ^ (-s) - ((2 * j + 2 : ℕ) : ℂ) ^ (-s)

/-- **The Dirichlet eta function**, defined by its paired series
`η(s) = ∑' j, ((2j+1)^(-s) - (2j+2)^(-s))`.  This is the sum of the classical alternating
series `∑' n, (-1)^n / (n+1)^s` with the terms grouped in pairs; the grouping is what makes
the series converge absolutely (and hence what makes the definition work in Lean, whose
`tsum` is the unconditional sum).  For `0 < re s` the series converges absolutely
(`RiemannHypothesis.Eta.summable_pairedTerm`), and `η` is analytic there
(`RiemannHypothesis.Eta.differentiableOn_dirichletEta`).  The classical alternating series
representation holds for `1 < re s`
(`RiemannHypothesis.Eta.dirichletEta_eq_tsum_alternating_of_one_lt_re`). -/
def dirichletEta (s : ℂ) : ℂ :=
  ∑' j : ℕ, pairedTerm j s

/-- **The Riemann hypothesis** (zeta form, as in Mathlib): every zero of `ζ` that is neither a
trivial zero (`s = -2(n+1)`, `n ∈ ℕ`) nor the pole `s = 1` has real part `1/2`. -/
abbrev ZetaForm : Prop :=
  RiemannHypothesis

/-- The Riemann hypothesis restricted to the critical strip: every zero of `ζ` with
`0 < re s < 1` lies on the critical line `re s = 1/2`. -/
def ZetaStripForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- The Riemann hypothesis in terms of the Dirichlet eta function: every zero of `η` with
`0 < re s < 1` lies on the critical line `re s = 1/2`. -/
def EtaForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → dirichletEta s = 0 → s.re = 1 / 2

end RiemannHypothesis

end
