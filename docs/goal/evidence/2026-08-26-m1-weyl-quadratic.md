# M1-WEYL-QUADRATIC — Weyl's bound for a quadratic exponential sum

Date: 2026-08-26
File: `RiemannHypothesis/WeylQuadratic.lean`

## Claim

Write `e(θ) = exp(2πiθ)` and `‖θ‖ = intDist θ = |θ − round θ|` for the distance from `θ` to the
nearest integer.  The module proves, for a real `α`:

* **the geometric series bound** (`norm_geomSum_e2pi_le`) — if `‖θ‖ ≠ 0` then for every `M` and
  every shift `c`,

      ‖∑_{j < M} e(θ j + c)‖ ≤ 1 / (2‖θ‖) ;

* **Weyl's inequality for a quadratic phase** (`norm_sq_sum_e2pi_quadratic_le`) — for every
  `H ≥ 1`, provided `‖2αk‖ ≠ 0` for `0 < k < H`,

      H ‖∑_{0 ≤ n < N} e(α n²)‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} 1/(2‖2αk‖)) ;

* **the usable form** (`normSq_sum_e2pi_quadratic_le_of_le`) — if `‖2αk‖ ≥ δ > 0` for
  `0 < k < H`, then

      ‖∑_{0 ≤ n < N} e(α n²)‖² ≤ (N + H − 1)(N + (H − 1)/δ) / H .

## Proof

One differencing step and an exact summation.

1. `RiemannHypothesis.WeylDifferencing.norm_sq_sum_e2pi_le` (the A process) bounds
   `H ‖∑_{n<N} e(f n)‖²` by `(N + H − 1)(N + 2 ∑_{0<k<H} ‖∑_{n<N−k} e(f(n+k) − f(n))‖)` for an
   arbitrary phase `f`.
2. For `f n = α n²` the differenced phase is *linear*: `α(n+k)² − α n² = (2αk) n + α k²`
   (`quadratic_diff`).  So each differenced sum is a geometric series.
3. A geometric series of unimodular terms with ratio `e(θ)` is summed exactly, and the bound
   `‖∑_{j<M} e(θ j + c)‖ ≤ 2/‖e(θ) − 1‖ ≤ 1/(2‖θ‖)` follows from Jordan's inequality in the form
   `4‖θ‖ ≤ ‖e(θ) − 1‖` (`four_mul_intDist_le_norm_e2pi_sub_one`), which is the repository's
   `two_mul_le_sin_pi_mul` from `KusminLandau.lean` applied to `θ − round θ`.
4. The third statement is the second with each `1/(2‖2αk‖)` replaced by `1/(2δ)` and the `H − 1`
   terms counted.

## Why this row exists

`M1-WEYL-DIFFERENCING` proves the A process but applies it to nothing: its open boundary records
that no choice of `H` is made and no bound for a specific phase is derived.  This row is the
first arithmetic application: the quadratic phase is the case where one differencing step already
suffices, and it is the base case of the induction (Weyl's inequality for a degree-`d` polynomial)
out of which the exponent pairs of the theory of `ζ` are built.

## Scope, and what is *not* claimed

* Only a **quadratic** phase is treated.  The general degree-`d` Weyl inequality requires
  iterating the A process `d − 1` times and is not proved here.
* The diophantine hypothesis is left as a hypothesis: no continued-fraction or
  Dirichlet-approximation argument converts `α` irrational (or `|α − a/q| ≤ 1/q²`) into a lower
  bound `δ` for `‖2αk‖`, and no choice of `H` is made, so no bound of the shape
  `∑ e(α n²) ≪ N^{1−1/2+ε}` is deduced.
* Nothing about `ζ` is claimed.  Quadratic exponential sums are not zeta sums; the module is
  infrastructure, and no subconvexity bound, approximate functional equation or density estimate
  follows from it.

## Adversarial revalidation: M1-WEYL-QUADRATIC

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylQuadratic`
  succeeds, the file contains no `sorry`, and it triggers no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements (checked in `scripts/audit.sh`).
* The statements are pinned verbatim in `scripts/revalidation.lean`, so a change of statement
  breaks the audit.
* The hypotheses are satisfiable, so the statements are not vacuous: for `α` irrational,
  `‖2αk‖ ≠ 0` for every `k ≠ 0`, and for `α = 1/(4H)` say, `‖2αk‖ = k/(2H) ≥ 1/(2H)` for
  `0 < k < H`, so the `δ`-form applies with `δ = 1/(2H)`.
* The bound is nontrivial: the trivial estimate is `‖∑_{n<N} e(α n²)‖² ≤ N²`, whereas with
  `H ≈ N` and `δ` bounded below the third statement gives `O(N + N/δ)`, i.e. square-root
  cancellation up to the diophantine factor.  It is of course lossy when `δ` is tiny — as it must
  be, since for `α` an integer the sum is exactly `N`.
* The statements are unconditional (no unproved `Prop` of this repository occurs as a hypothesis),
  so `docs/goal/conditional-theorems.txt` gains no entry.
