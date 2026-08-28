/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Main

/-!
# Solutions to the Challenge

The three declarations of `Challenge.lean`, proved.  Each is the corresponding theorem in
`RiemannHypothesis.Main`, stated in the namespace `RiemannHypothesisConjecture` of the
Challenge; the only difference is the namespace.

As the Challenge explains, none of these theorems asserts the Riemann hypothesis itself:
the hypothesis appears inside them only as the proposition `RiemannHypothesis.ZetaForm`
(and its two equivalent forms), which is open.  What is proved is the *equivalence* of the
three standard formulations — in particular, the equivalence between the classical
analytic-continuation form and the elementary Dirichlet-eta form.
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
