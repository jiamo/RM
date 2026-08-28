# Evidence: the Riemann–von Mangoldt upper bound `N(T) = O(T log T)` (2026-08-20)

Row: `M2-ZERO-COUNT` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroCount.lean`:

* `nontrivialZeros T = {s | ζ s = 0 ∧ 0 < re s ∧ re s < 1 ∧ |im s| ≤ T}` (a definition);
* `nontrivialZeros_subset` : every such zero is a zero of `ξ` lying in the disc of radius
  `T + 2` about `s = 2`;
* `finite_nontrivialZeros` : **for every `T`, `nontrivialZeros T` is finite**;
* `ncard_nontrivialZeros_le` : **there is an absolute constant `C > 0` with
  `#(nontrivialZeros T) ≤ C · T · log T` for every `T ≥ 2`**, the zeroes being counted without
  multiplicity.

## The argument

A zero `s` with `0 < re s < 1` and `|im s| ≤ T` satisfies `‖s − 2‖ ≤ 2 + T`, and is a zero of
the entire function `ξ` (`xiFn_eq_zero_of_zeta`). Apply the counting lemma
`ncard_setOf_zeros_le` of `RiemannHypothesis.ZeroCountingLemma` with centre `c = 2` and radius
`R = 4(T + 2)`, so that the small disc of radius `R/4 = T + 2` contains all of them:

* the maximum of `‖ξ‖` on the circle `‖z − 2‖ = R` is at most
  `M = exp (C₀ (1 + (R+2)) log (2 + (R+2)))` by `norm_xiFn_le`;
* `ξ(2) = Λ(2) ≠ 0`.

Hence the number of zeroes is at most `log (M / ‖ξ(2)‖)/log 3`, and
`log M = C₀ (4T + 11) log (4T + 12) ≤ 112 C₀ · T log T` for `T ≥ 2`, using
`4T + 11 ≤ 16T`, `log(4T+12) ≤ log(12T) = log 12 + log T ≤ 7 log T` and `log 3 ≥ 1`.

## Commands run

```
lake build RiemannHypothesis.ZeroCount
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `finite_nontrivialZeros` and `ncard_nontrivialZeros_le` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* Only the **upper** bound is proved. The matching lower bound `N(T) ≫ T log T`, and the
  Riemann–von Mangoldt asymptotic `N(T) = (T/2π) log (T/2πe) + O(log T)`, are not proved: they
  need the argument principle and Stirling's formula for the Gamma factor on vertical lines,
  neither of which is available here.
* The constant `C` is not explicit (it inherits the non-explicit constant of `norm_xiFn_le`).
* Zeroes are counted **without multiplicity**.
* Nothing here says that any zero exists; the row is an upper bound only.

## Adversarial revalidation: M2-ZERO-COUNT

Second, independent pass.

* **Claim mode.** `nontrivialZeros` is a `def`, pinned by `rfl` in `scripts/revalidation.lean`;
  the two results are `theorem`s proved here. No hypothesis of either theorem refers to the
  Riemann hypothesis, and neither statement implies it: both are compatible with zeroes off the
  critical line.
* **Non-vacuity.** `nontrivialZeros T` is defined by a condition that can be satisfied
  (`ζ` does have zeroes in the strip, though this repository does not prove it); the theorems do
  not become trivial through an unsatisfiable hypothesis — the only hypothesis is `2 ≤ T`. If the
  set were empty the statements would still be true but harmless; the mathematical content is the
  *bound*, which is proved for the set as defined, whatever it contains.
* **Direction check.** The bound is an upper bound on a cardinality, so it cannot be strengthened
  accidentally by an error in the direction of an inequality: a wrong direction would have made
  the final `calc` fail. The `log 3` in the denominator is a *divisor*, and `log 3 ≥ 1` is used
  to discard it — which weakens the bound, in the safe direction.
* **Sanity check of the order of magnitude.** The truth is
  `N(T) ~ (T/2π) log (T/2π)`, so `N(100) ≈ 29`. The proved bound is of the same shape,
  `C T log T`, with a much larger constant; nothing here claims sharpness.
* **Where the largeness of the disc is used.** The counting lemma needs the zeroes in the
  concentric disc of a *quarter* of the radius; that is why `R = 4(T+2)` and why `log M` is
  evaluated at `‖s‖ ≈ 4T`. The extra factor `4` is absorbed into the constant, and is the reason
  the growth bound for `ξ` has to hold on the whole plane (including `re s < 0`, where it comes
  from the functional equation) rather than only in the critical strip.
* **Statement pinning.** `scripts/revalidation.lean` writes out `nontrivialZeros`,
  `finite_nontrivialZeros` and `ncard_nontrivialZeros_le` in full and supplies the repository's
  declarations as the proof terms; `scripts/audit.sh` prints their axioms.
