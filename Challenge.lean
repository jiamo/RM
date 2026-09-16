/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Riemann Hypothesis: statement of record

This is the statement of record for this repository.  It states three theorems and, apart
from the definitions it imports from `RiemannHypothesis.Defs` (the Dirichlet eta function and
the three formulations of the Riemann hypothesis), it introduces no definitions of its own.

## The statements

The Riemann hypothesis is open.  What is formalized here is its *precise statement* together
with the equivalence of its standard formulations.  Three formulations appear, all as `Prop`:

* `ZetaForm` — the classical form, in terms of the analytically continued Riemann zeta
  function of Mathlib (`RiemannHypothesis`, in
  `Mathlib.NumberTheory.LSeries.RiemannZeta`): every zero of `ζ` that is neither a trivial
  zero (`s = -2(n+1)`, `n ∈ ℕ`) nor the pole at `s = 1` lies on the critical line
  `re s = 1/2`.
* `ZetaStripForm` — the same claim restricted to the critical strip `0 < re s < 1`.
* `EtaForm` — the same claim in terms of the Dirichlet eta function `η`, defined by its
  paired series; for `1 < re s` it is the classical alternating series
  `∑' n, (-1)^n / (n+1)^s` (see
  `RiemannHypothesis.Eta.dirichletEta_eq_tsum_alternating_of_one_lt_re`).

None of the three formulations is proved here, or anywhere in this repository — that is the honest state
of the Riemann hypothesis.  What is proved (in `RiemannHypothesis.Main`) is that the three
formulations are *equivalent*:

* `zeta_strip_iff_eta` : `ZetaStripForm ↔ EtaForm`,
* `zeta_iff_zeta_strip` : `ZetaForm ↔ ZetaStripForm`,
* `zeta_iff_eta` : `ZetaForm ↔ EtaForm`.

Accordingly, the three theorems below are recorded **without `sorry`**: each one is a direct
reference to the matching equivalence theorem already proved in `RiemannHypothesis.Main`
(and restated once more in `Solution.lean`).  This file therefore introduces no mathematics
of its own; it simply records the propositions together with their machine-checked proofs.

The equivalence is genuinely informative, not a formality: `EtaForm` is an *elementary*
statement (it can be written down without analytic continuation), while `ZetaForm` requires
the analytic continuation of `ζ`.  The bridge between them is the classical identity
`η(s) = (1 - 2^(1-s)) ζ(s)` on the punctured right half-plane, proved in
`RiemannHypothesis.Eta` by the identity theorem for analytic functions; the factor
`1 - 2^(1-s)` has no zeroes in the strip
(`RiemannHypothesis.Zeros.one_sub_two_cpow_ne_zero`), so the zeroes of `η` inside the strip
are exactly the zeroes of `ζ` inside the strip.
-/

namespace RiemannHypothesisConjecture

open Complex

/-- **The Riemann hypothesis** (zeta form): every zero of `ζ` other than the trivial zeroes
`-2(n+1)` and the pole at `s = 1` lies on the critical line `re s = 1/2`. -/
theorem zeta_strip_iff_eta : RiemannHypothesis.ZetaStripForm ↔ RiemannHypothesis.EtaForm :=
  RiemannHypothesis.zeta_strip_iff_eta

/-- The zeta form of the Riemann hypothesis is equivalent to its restriction to the critical
strip. -/
theorem zeta_iff_zeta_strip : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.ZetaStripForm :=
  RiemannHypothesis.zeta_iff_zeta_strip

/-- The Riemann hypothesis in its zeta form is equivalent to its Dirichlet eta form. -/
theorem zeta_iff_eta : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.EtaForm :=
  RiemannHypothesis.zeta_iff_eta

end RiemannHypothesisConjecture
