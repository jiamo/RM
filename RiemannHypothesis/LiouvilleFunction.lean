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

This file used to define the Liouville function, because the Mathlib revision the repository was
built against did not provide it. Mathlib now supplies
`Mathlib.NumberTheory.ArithmeticFunction.Liouville`, with the very same definition and the two
properties used downstream, so this module simply re-exports it; the downstream names are
unchanged.

## Main results (from Mathlib)

* `ArithmeticFunction.liouville` : the Liouville function `λ`, as an `ArithmeticFunction ℤ`.
* `ArithmeticFunction.liouville_apply` : `λ(n) = (-1)^Ω(n)` for `n ≠ 0`.
* `ArithmeticFunction.isMultiplicative_liouville` : `λ` is multiplicative.
-/
