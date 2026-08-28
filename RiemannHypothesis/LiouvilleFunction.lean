/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# The Liouville function as an arithmetic function

`λ(n) = (-1)^Ω(n)`, where `Ω(n) = ArithmeticFunction.cardFactors n` counts the prime factors of
`n` with multiplicity.

The Mathlib version this repository is built against provides `ArithmeticFunction.liouville`
together with the two properties used downstream, so this file simply re-exports them (a
self-contained copy used to live here, back when Mathlib did not have the definition).

## Main results

* `ArithmeticFunction.liouville` : the Liouville function `λ`, as an `ArithmeticFunction ℤ`.
* `ArithmeticFunction.liouville_apply` : `λ(n) = (-1)^Ω(n)` for `n ≠ 0`.
* `ArithmeticFunction.isMultiplicative_liouville` : `λ` is multiplicative.
-/

namespace ArithmeticFunction

example : IsMultiplicative liouville := isMultiplicative_liouville

example {n : ℕ} (hn : n ≠ 0) : liouville n = (-1) ^ cardFactors n := liouville_apply hn

end ArithmeticFunction
