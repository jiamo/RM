# Koksma's inequality with the total variation

Date: 2026-09-07
Module: `RiemannHypothesis/KoksmaVariation.lean`

## Why

`M1-KOKSMA` proves Koksma's inequality for a nondecreasing integrand and, as a corollary, for an
integrand *presented* as a difference `f = g − h` of two nondecreasing functions, the constant
being the sum of the two rises of the chosen presentation.  Its recorded open boundary was
exactly that no total-variation functional was introduced: the statement was not available for a
general function of bounded variation, and the constant depended on the decomposition rather than
on `f`.  This row closes that part of the boundary, using mathlib's `eVariationOn`.

## What is proved

Write `V(f) = (eVariationOn f (Set.Icc 0 1)).toReal` (`unitVariation`).

* `unitVariation`, `unitVariation_nonneg`, `variationOnFromTo_zero_one` — the total variation of
  `f` on `[0,1]` as a real number, and its identification with the signed variation from `0`
  to `1`.
* `unitVariation_of_monotoneOn` — for a nondecreasing `f`, `V(f) = f 1 − f 0`.
* `abs_sub_le_unitVariation` — `|f 1 − f 0| ≤ V(f)`, so the constants below are nonnegative.
* `koksma_variation_sub` — for `f` of bounded variation on `[0,1]`, every sequence `x` and every
  `N ≥ 1`,

      |(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ (2 V(f) − (f 1 − f 0)) · D_N(x) .

* `koksma_variation_add` — the same with `(2 V(f) + (f 1 − f 0))`.
* `koksma_variation` — their conjunction, with the constant `2 V(f) − |f 1 − f 0|`.
* `koksma_variation_le` — the readable form, with the constant `2 V(f)`.
* `unitVariation_le_of_lipschitz` — the total variation of an `L`-Lipschitz function on `[0,1]`
  is at most `L`.
* `koksma_lipschitz_two` — hence for an `L`-Lipschitz integrand the error is at most
  `2 L · D_N(x)`, improving the constant `3 L` of `koksma_lipschitz`.
* `tendsto_average_of_tendsto_discrepancy_variation`,
  `tendsto_average_quadratic_variation` — a sequence whose discrepancy tends to `0` integrates
  *every* function of bounded variation correctly in the limit; the second is the concrete
  instance `xₙ = α n²` with `α` irrational.

## Proof

Let `V_f x = variationOnFromTo f [0,1] 0 x` be the variation function.  Mathlib provides that
`V_f` is nondecreasing on `[0,1]` (`variationOnFromTo.monotoneOn`) and that both `V_f − f` and
`V_f + f` are nondecreasing there (`variationOnFromTo.sub_self_monotoneOn`,
`variationOnFromTo.add_self_monotoneOn`).  This gives two Jordan decompositions,

    f = V_f − (V_f − f)   and   f = (V_f + f) − V_f ,

with `V_f 0 = 0` and `V_f 1 = V(f)`.  Feeding each into `koksma_sub_monotone` of `M1-KOKSMA`
produces the constants `(V(f)) + (V(f) − (f 1 − f 0))` and `(V(f) + (f 1 − f 0)) + V(f)`, that is
`2 V(f) ∓ (f 1 − f 0)`; taking whichever of the two is smaller gives `2 V(f) − |f 1 − f 0|`.

For the Lipschitz form, `eVariationOn f [0,1] = eVariationOn (f ∘ id) [0,1] ≤ L · eVariationOn id
[0,1] = L` by `LipschitzOnWith.comp_eVariationOn_le` and `eVariationOn_id_Icc`; in particular `f`
has bounded variation, and the constant `2 V(f) ≤ 2 L`.

## Scope

The classical sharp constant of Koksma's inequality is `V(f)`, not `2 V(f)`.  The sharp form is
proved by Riemann–Stieltjes integration by parts against `d f`, machinery mathlib does not have;
the factor `2` here is exactly the price of routing through the Jordan decomposition, whose two
monotone pieces have rises summing to `2 V(f) − (f 1 − f 0)`.  For a nondecreasing `f` the
constant is `f 1 − f 0 = V(f)` and nothing is lost, so the new statement subsumes
`koksma_monotone` without weakening it.  Likewise the Lipschitz constant `2 L` is still not the
sharp `L`.  Nothing here concerns `ζ`.

## Adversarial revalidation: M1-KOKSMA-VARIATION

* **Is the constant right, checked by hand?**  Take `f` nondecreasing.  Then
  `V_f x = f x − f 0`, so the first decomposition is `f = (f − f 0) − 0`, with rises
  `(f 1 − f 0)` and `0`, and the theorem's constant is
  `2 V(f) − |f 1 − f 0| = 2(f 1 − f 0) − (f 1 − f 0) = f 1 − f 0`, exactly the constant of
  `koksma_monotone`.  Take `f = −g` with `g` nondecreasing: `V(f) = g 1 − g 0`,
  `f 1 − f 0 = −(g 1 − g 0)`, and the constant is again `g 1 − g 0`.  Both agree with the
  hand computation; the two one-sided forms are genuinely needed, since only one of them gives
  the right answer in each case.
* **Is the hypothesis vacuous or unnecessarily strong?**  `BoundedVariationOn f (Set.Icc 0 1)`
  holds for every monotone and every Lipschitz function, and the module derives both cases;
  it fails only for genuinely wild integrands, for which the statement would be `≤ ∞` and
  meaningless.  It is load-bearing: without it `V(f)` is `(⊤).toReal = 0` and the inequality
  would assert that the average is exactly the integral.
* **Is anything circular?**  No.  The two decompositions come from mathlib
  (`variationOnFromTo.sub_self_monotoneOn`, `variationOnFromTo.add_self_monotoneOn`), and the
  inequality itself comes from `koksma_sub_monotone`, which was proved in `M1-KOKSMA` from the
  monotone case.  No result of this row is used in its own proof.
* **Is the claimed improvement over `koksma_lipschitz` real?**  Yes: `3 L D_N` is replaced by
  `2 L D_N` under the same hypotheses (`0 ≤ L` and the same two-point Lipschitz condition on
  `[0,1]`), and both statements are pinned in `scripts/revalidation.lean`, so neither can be
  weakened silently.  It is still not the sharp `L`, which the row records as open.
* **Claim mode.**  Every item is a theorem proved in this repository, not a `Prop` and not a
  literature citation; `eVariationOn`, `variationOnFromTo` and their two monotonicity lemmas are
  provided by mathlib and are used as such.
* **Anything claimed about `ζ`?**  Nothing.

## Gates

* `lake build RiemannHypothesis.KoksmaVariation`
* `lake build`
* `./scripts/audit.sh`
* Axioms of `unitVariation_of_monotoneOn`, `koksma_variation_sub`, `koksma_variation_add`,
  `koksma_variation`, `koksma_variation_le`, `koksma_lipschitz_two`,
  `tendsto_average_of_tendsto_discrepancy_variation`, `tendsto_average_quadratic_variation`:
  exactly `propext`, `Classical.choice`, `Quot.sound`.
