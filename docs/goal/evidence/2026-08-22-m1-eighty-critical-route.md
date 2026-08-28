# M1-EIGHTY-CRITICAL-ROUTE — a conditional route past eighty per cent on the critical line

Date: 2026-08-22
Module: `RiemannHypothesis/EightyPercentRoute.lean` (imported by `RiemannHypothesis.lean`)

## What is proved, unconditionally, in this module

* `windowCount_rvm` and `xiDerivWindowCount_rvm` — the Riemann–von Mangoldt formula for the
  zeroes of `ζ` and for the zeroes of `ξ′` in the dyadic window `(T, 2T]`, restated in this
  repository's counting functions, with the *same* main term `(T/2π)·ℓ₁(T)`.  Both come from
  the vendored `Zeta23` library (`Zeta23.riemannVonMangoldt_zeta`,
  `Zeta23.XiPrime.xiDerivZeros₀_rvm`).
* `abs_xiDerivWindowCount_sub_windowCount_le` — hence `|N_{ξ′}(T,2T) − N(T,2T)| = O(log T)`.
* `exists_le_windowCount_mul_log` — `N(T,2T)/log T → ∞`; for every `K` one has
  `K·log T ≤ N(T,2T)` for all large `T`.
* `xiDerivWindowCount_le_one_add_mul` — consequently `N_{ξ′} ≤ (1 + ε)·N` for all large `T`,
  for every `ε > 0`.

## The single unproved input

`SpeiserTransfer` is a `def … : Prop`, in the style of `RiemannHypothesis/Partial.lean`: the
counting form of Speiser's theorem (Levinson–Montgomery),

```
∃ C S, ∀ T ≥ S, N_off(T,2T) ≤ (N_{ξ′}(T,2T) − N₀ˢ_{ξ′}(T,2T)) + C·log T .
```

It is **not** proved here.  Proving it needs the argument principle for `ξ′/ξ` on the left half
of the critical strip, which this repository does not have.

## What the route gives, under that hypothesis

* `offLine_le_of_speiserTransfer` — `N_off ≤ (0.13136 + ε)·N` for all large `T`
  (from the unconditional `ξ′` quartic bound `0.86864`, restated as
  `Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std`).
* `eighty_four_percent_distinct_on_critical_line_of_speiserTransfer` —
  `0.84·N_d ≤ N₀`: at least 84 % of the **distinct** zeroes on the critical line, using
  `five_sixths_distinct` (`N_d ≥ (5/6 − ε)·N`).
* `eightyPercentOnCriticalLineDistinct_of_speiserTransfer` — the 80 % target for the distinct
  zeroes, recorded as the `Prop` `EightyPercentOnCriticalLineDistinct`.
* `seventy_percent_on_critical_line_of_speiserTransfer` — `0.7·N ≤ N₀`, i.e. 70 % of the zeroes
  counted **with multiplicity**, improving on the unconditional `2/3` only under the hypothesis.

## Scope and honesty

* Unconditionally the proportion of zeroes of `ζ` proved to lie on the critical line is
  unchanged: `2/3` (`two_thirds_on_critical_line`), `2 − 1/c₁* = 0.67250…` with the optimal
  window.  Nothing in this module raises it.
* `EightyPercentOnCriticalLine` (80 % **with multiplicity**) is not reached even on this route:
  the multiplicity budget `N_d ≥ (5/6)·N` caps it at 70 %.
* The vendored library's own bandwidth-one ceiling (≈ 0.6818) shows the mollifier method as
  formalized here cannot reach 80 % on the critical line unconditionally.
* No `sorry`.  Every theorem in the module depends on exactly `propext`, `Classical.choice`,
  `Quot.sound`.

## Gates

* `lake build` (whole project, including `vendor/zeta23`) — succeeds.
* `./scripts/audit.sh` — `OK`.
