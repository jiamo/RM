# M1-LIOUVILLE-ELEMENTARY — elementary Liouville sums

Date: 2026-08-22
Module: `RiemannHypothesis/LiouvilleSums.lean` (imported by `RiemannHypothesis.lean`)

(Evidence file reconstructed from the task-board entry and the module itself; the row was
already `DONE_STRONG` and its pins are in `scripts/revalidation.lean`.)

## What is proved

* `sum_divisors_liouville` — for `k ≠ 0`, `∑_{d ∣ k} λ(d) = 1` if `k` is a square and `0`
  otherwise; the divisor-sum form of the Dirichlet identity `ζ · λ = 1_squares` proved in
  `RiemannHypothesis/LiouvilleCriterion.lean`.
* `sum_liouville_mul_div` — the classical identity
  `∑_{n ≤ N} λ(n) ⌊N/n⌋ = ⌊√N⌋`, obtained from the divisor sum by the hyperbola reindexing
  `sum_pairs_outer` of `RiemannHypothesis/MertensSums.lean` together with the count of the
  squares in `[1, m]`.
* `abs_littleLiouville_sub_le_one` — replacing `⌊N/n⌋` by `N/n` costs at most the fractional
  parts, so the weighted sum `littleLiouville N = ∑_{n ≤ N} λ(n)/n` satisfies
  `|littleLiouville N − ⌊√N⌋/N| ≤ 1`.

## What is *not* proved

Both statements are unconditional and elementary. They are very far from the square-root
cancellation `LiouvilleBoundForm` that is equivalent to the Riemann hypothesis: no bound of
the shape `L(N) = O(N^{1/2+ε})` for the summatory Liouville function is claimed anywhere.

## Gates

* `lake build RiemannHypothesis.LiouvilleSums` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-LIOUVILLE-ELEMENTARY

Re-checked by pinning: `scripts/revalidation.lean` states the divisor sum, the identity
`∑_{n ≤ N} λ(n) ⌊N/n⌋ = ⌊√N⌋`, the definitional unfolding of `littleLiouville`, and the
bound `|littleLiouville N − ⌊√N⌋/N| ≤ 1` in full, each discharged by the repository's
declaration.

Hidden-assumption check: the only hypothesis is `k ≠ 0` in the divisor sum, which is needed
(`0` has no finite divisor set in the relevant sense); the other two statements hold for
every `N`, including `N = 0`. Vacuity check: none of the statements is conditional on an
unsatisfiable hypothesis, and each has computational content (both sides are integers or
explicit rationals for each `N`).

Scope check: no square-root cancellation for the summatory Liouville function is claimed,
so nothing here approaches the Riemann hypothesis.
