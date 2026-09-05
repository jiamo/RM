# M1-WEYL-POLYNOMIAL — Weyl's theorem for an arbitrary polynomial

Date: 2026-08-28
File: `RiemannHypothesis/WeylPolynomial.lean`

## Claim

For a real polynomial `p` of degree `d ≥ 1` whose leading coefficient `a_d` is irrational, the
fractional parts of `p(n)` are equidistributed modulo one:

* `equidistributedMod1_polyEval` — `n ↦ p(n)` is equidistributed modulo one;
* `tendsto_countIn_div_polyEval` — the counting form: for `0 ≤ a < b ≤ 1`,

      #{ n < N : {p(n)} ∈ [a, b) } / N → b − a ;

* `equidistributedMod1_monomial`, `tendsto_countIn_div_monomial` — the special case `α n^d`,
  `α` irrational, `d ≥ 1`.

The supporting statements about the forward difference `diffPoly p k = p(X + k) − p(X)` are

* `coeff_diffPoly_of_le` — every coefficient of `diffPoly p k` from the degree of `p` upwards
  vanishes;
* `coeff_diffPoly_pred` — its coefficient of `X^{d−1}` is `d · a_d · k`;
* `natDegree_diffPoly` — hence `deg (diffPoly p k) = d − 1` for `k ≥ 1` and `a_d ≠ 0`.

## Proof

`diffPoly p k` is `taylor k p − p`, so its coefficients are computed from mathlib's Hasse
derivatives: `(taylor r p).coeff i = eval r (hasseDeriv i p)` and
`(hasseDeriv i p).coeff m = C(m+i, i) · p.coeff (m+i)`.  For `i ≥ d` the Hasse derivative is
constant (or zero) and cancels the corresponding coefficient of `p`; for `i = d − 1` it is the
linear polynomial `a_{d−1} + d·a_d·X`, whose value at `k` exceeds `a_{d−1}` by exactly `d·a_d·k`.

Weyl's theorem is then an induction on the degree.  In degree one, `p(n) = a₁ n + a₀` is a linear
sequence with irrational slope, equidistributed by `M1-WEYL-LINEAR` and invariant under the
translation by `a₀` (`equidistributedMod1_add_const`).  In degree `d + 1 ≥ 2`, every difference
sequence `n ↦ p(n + k) − p(n)`, `k ≥ 1`, is the value sequence of `diffPoly p k`, a polynomial of
degree `d` whose leading coefficient `(d+1)·a_{d+1}·k` is again irrational (an irrational number
times a nonzero natural number); the induction hypothesis applies to it, and van der Corput's
difference theorem (`M1-WEYL-DIFFERENCE-THEOREM`) lifts equidistribution back to `p`.

The counting form is `M1-WEYL-COUNT-GENERAL` applied to the resulting equidistribution.

## Why this row exists

`M1-WEYL-CRITERION` and `M1-WEYL-EQUIDISTRIBUTION` proved equidistribution only for `α n` and
`α n²`, and both recorded in their open boundary that the general polynomial case — which needs
the A process iterated — was not proved.  This row proves it.

## Scope, and what is *not* claimed

* No rate of convergence, and no quantitative Weyl inequality: the input estimates are
  ineffective in the diophantine nature of `a_d`, so nothing of the shape
  `∑_{n<N} e(p(n)) = O(N^{1−c})` is proved here.
* Only the leading coefficient is assumed irrational, which is the classical hypothesis; nothing
  is claimed when every coefficient is rational (where the sequence is periodic modulo one).
* Nothing about `ζ` follows: polynomial phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-POLYNOMIAL

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylPolynomial`
  succeeds, the file contains no `sorry`, and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all six main
  statements; the checks are in `scripts/audit.sh`.
* All of them are pinned in `scripts/revalidation.lean`, the counting statements with `countIn`
  written out as the cardinality of an explicit `Finset.filter`, so the definitions cannot be
  weakened.
* The statements are not vacuous: `Irrational (√2)` is available in mathlib, so
  `p = C √2 * X^3 + X` satisfies the hypotheses, and the conclusion `b − a` is a nonzero
  proportion for, say, `a = 1/4`, `b = 1/2`.
* The conclusion is a genuine restriction: the trivial bounds are `0 ≤ countIn/N ≤ 1`, whereas
  the theorem pins the limit at `b − a`, and it fails for a rational leading coefficient — for
  `p = X` the fractional parts are all `0`.
* The degree hypothesis is load-bearing: a constant polynomial has constant, hence
  non-equidistributed, values, which is why `1 ≤ deg p` is assumed.
* No unproved `Prop` of this repository occurs among the hypotheses.
