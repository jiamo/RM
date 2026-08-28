# M1-WEYL-EQUIDISTRIBUTION — cancellation in quadratic Weyl sums for an irrational coefficient

Date: 2026-08-26
File: `RiemannHypothesis/WeylEquidistribution.lean`

## Claim

With `e(θ) = exp(2πiθ)`, `‖θ‖ = intDist θ` the distance to the nearest integer and

    quadSum α N = ∑_{0 ≤ n < N} e(α n²),

the module proves, for `α` irrational:

* `exists_pos_le_intDist_of_irrational` — for every `H` there is a `δ > 0` with `δ ≤ ‖2αk‖` for
  all `0 < k < H`;
* `exists_normSq_quadSum_le` — hence for every `H ≥ 1` there is a `C ≥ 0` with
  `‖quadSum α N‖² ≤ (N + H)(N + C)/H` for every `N`;
* `tendsto_norm_quadSum_div_atTop` — **`‖quadSum α N‖ / N → 0`**;
* `tendsto_norm_quadSum_div_atTop_intCast` — the same for the phase `(hα) n²` for every nonzero
  integer `h`, which is the family of estimates Weyl's criterion asks for.

## Proof

`M1-WEYL-QUADRATIC` proves Weyl's inequality for the quadratic phase but leaves its diophantine
hypothesis (`‖2αk‖ ≥ δ > 0` for `0 < k < H`) to the caller.  For `α` irrational, `2αk` is
irrational for every `k ≠ 0` (`Irrational.mul_intCast`), so `‖2αk‖ > 0`
(`intDist_pos_of_irrational`, via `intDist_eq_zero_iff`), and the minimum of the finitely many
values over `0 < k < H` is a legitimate `δ`.  Weyl's inequality then gives

    ‖quadSum α N‖² ≤ (N + H − 1)(N + (H − 1)/δ)/H ≤ (N + H)(N + C)/H ,

and for `N` larger than both `H` and `C` the right-hand side is at most `4N²/H`.  Given `ε > 0`,
choosing `H > 4/ε²` therefore makes `‖quadSum α N‖ < εN` for all large `N`.

## Why this row exists

`M1-WEYL-QUADRATIC` closes with an inequality that is conditional on an unverified diophantine
hypothesis; the open boundary of that row records exactly this.  This row discharges the
hypothesis in the classical case and extracts the classical conclusion — the quadratic Weyl sum
has *some* cancellation for every irrational `α`, with no rate.

## Scope, and what is *not* claimed

* **No rate.**  `δ` is produced by a compactness-free but entirely ineffective minimum over
  `0 < k < H`; it depends on `H` and on the diophantine nature of `α`.  Nothing of the shape
  `∑_{n<N} e(α n²) ≪ N^{1−c}` is proved, and no such bound is possible uniformly in `α`
  irrational.
* **Equidistribution itself is not proved.**  The estimates for all nonzero integer multiples
  are the *input* to Weyl's criterion; the criterion (which needs the density of trigonometric
  polynomials in the continuous functions on the circle, and then an approximation of indicators)
  is not formalized here, so no statement about the distribution of the fractional parts of
  `α n²` is made.
* Nothing about `ζ` is claimed.  Quadratic phases are not zeta phases; the module is
  infrastructure.

## Adversarial revalidation: M1-WEYL-EQUIDISTRIBUTION

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.WeylEquidistribution` succeeds, the file contains no `sorry`, and it triggers
  no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements (checked in `scripts/audit.sh`).
* The statements are pinned in `scripts/revalidation.lean`; the pinned form of the limit writes
  the sum out in full rather than through `quadSum`, so the definition cannot silently change.
* The hypothesis is satisfiable and the conclusion is not vacuous: `Irrational (√2)` is available
  in mathlib, and the conclusion `‖∑_{n<N} e(αn²)‖/N → 0` is a genuine improvement on the trivial
  bound `‖∑_{n<N} e(αn²)‖ ≤ N`, which gives only that the quotient is `≤ 1`.
* The irrationality hypothesis is load-bearing: for `α = 0` the sum is exactly `N` and the
  quotient is constantly `1`, so the theorem is false without it.
* The statements are unconditional (no unproved `Prop` of this repository occurs as a hypothesis),
  so `docs/goal/conditional-theorems.txt` gains no entry.
