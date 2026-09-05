# M1-WEYL-QUADRATIC-QUANTITATIVE — the diophantine input to Weyl's inequality, and an effective `N^(3/4)` bound

Date: 2026-08-28
File: `RiemannHypothesis/WeylQuadraticQuantitative.lean`

## Claim

Let `intDist θ = |θ − round θ|` be the distance to the nearest integer, and let
`quadSum α N = ∑_{0 ≤ n < N} e(α n²)`.

* `inv_le_intDist_intCast_div` — if `q ≥ 1` and `q ∤ m` then `1/q ≤ intDist (m/q)`.
* `intDist_le_intDist_add_abs_sub` — `intDist y ≤ intDist x + |x − y|`: the distance to the
  nearest integer is `1`-Lipschitz.
* `inv_two_mul_le_intDist_of_approx` — **the diophantine input**: if `gcd(a, q) = 1` and
  `|β − a/q| ≤ 1/q²`, then `1/(2q) ≤ intDist (β k)` for every integer `k` with `0 < 2k ≤ q`.
* `normSq_quadSum_le_of_approx` — **the quantitative Weyl inequality**: for `q ≥ 4`,
  `gcd(a, q) = 1` and `|2α − a/q| ≤ 1/q²`,

      ‖quadSum α N‖² ≤ 4 (N + q)(N + q²)/q   for every N.

* `normSq_quadSum_le_of_approx_sqrt`, `norm_quadSum_pow_four_le_of_approx_sqrt`,
  `norm_quadSum_le_of_approx_sqrt` — with `N ≥ 16` and a denominator of the size of `√N`
  (`N ≤ q² ≤ 4N`), this reads `‖quadSum α N‖² ≤ 40 N √N`, `‖quadSum α N‖⁴ ≤ 1600 N³`, and

      ‖quadSum α N‖ ≤ 7 N^(3/4).

## Proof

`inv_le_intDist_intCast_div`: with `j = round (m/q)`, the integer `m − jq` is nonzero because
`q ∤ m`, so `|m − jq| ≥ 1` and `intDist (m/q) = |m − jq|/q ≥ 1/q`.

`intDist_le_intDist_add_abs_sub` follows from `intDist_le_abs_sub_int`, itself the observation
that if `j ≠ round θ` then `|j − round θ| ≥ 1` while `|θ − round θ| ≤ 1/2`, so no integer other
than `round θ` can be closer.

`inv_two_mul_le_intDist_of_approx`: since `gcd(a, q) = 1` and `0 < k ≤ q/2 < q`, `q` does not
divide `a k`, so `intDist (a k / q) ≥ 1/q` by the first lemma.  The perturbation is
`|β k − a k / q| = k |β − a/q| ≤ (q/2)(1/q²) = 1/(2q)`, and the Lipschitz property gives
`intDist (β k) ≥ 1/q − 1/(2q) = 1/(2q)`.

`normSq_quadSum_le_of_approx`: with `H = q/2 ≥ 1`, every `0 < k < H` satisfies `2k ≤ q`, so
`M1-WEYL-QUADRATIC`'s `normSq_sum_e2pi_quadratic_le_of_le` applies with `δ = 1/(2q)` and yields
`‖quadSum α N‖² ≤ (N + H − 1)(N + 2q(H − 1))/H`.  From `2H ≤ q ≤ 4H` the numerator is at most
`(N + q)(N + q²)` and `1/H ≤ 4/q`.

For the `√N` form put `s = √N`, so `s ≥ 4`, `s ≤ q ≤ 2s` and `N = s²`; then
`4(N + q)(N + q²) ≤ 4(s² + 2s)(5s²) = 20 s⁴ + 40 s³ ≤ 40 s⁴ ≤ 40 s³ q`, that is
`‖quadSum α N‖² ≤ 40 N √N`.  Squaring gives `‖quadSum α N‖⁴ ≤ 1600 N³`, and since
`1600 ≤ 2401 = 7⁴` and `(N^{3/4})⁴ = N³`, taking fourth roots gives `‖quadSum α N‖ ≤ 7 N^{3/4}`.

## Why this row exists

`M1-WEYL-QUADRATIC` recorded in its open boundary that "the diophantine input is left as a
hypothesis: no continued-fraction or Dirichlet-approximation argument turns `|α − a/q| ≤ 1/q²`
into the lower bound `δ` for `intDist (2 α k)`, and no choice of `H` is made, so no bound of the
shape `∑ e(α n²) = O(N^(1/2+ε))` is deduced".  `M1-WEYL-EQUIDISTRIBUTION` discharged the
hypothesis only ineffectively, through a minimum over finitely many `k`, giving `o(N)` and no
rate.  This row supplies the classical effective form of the input and makes the choice of `H`,
so a power saving is proved for the first time.

## Scope, and what is *not* claimed

* The exponent is `3/4`, not the `1/2 + ε` of Weyl's inequality.  Reaching that requires the
  counting lemma `∑_{k<H} min(N, 1/intDist(αk)) ≪ (H/q + 1)(N + q log q)`, which lets one take
  `H` as large as `N` rather than `q/2`; it is not formalized here.
* The bound is conditional on the *existence* of an approximation with a large denominator, as it
  must be: for `α` a rational with small denominator there is no cancellation at all, and
  `‖quadSum α N‖` can be of order `N`.  Dirichlet's approximation theorem produces some `q ≤ Q`
  with `|2α − a/q| ≤ 1/(qQ)`, but not a `q` in a prescribed range, so no unconditional statement
  about a fixed irrational `α` is drawn here.
* The constants `4`, `40`, `1600`, `7` are not optimized.
* Nothing about `ζ` follows.  Quadratic phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-QUADRATIC-QUANTITATIVE

* The module is imported by `RiemannHypothesis.lean`,
  `lake build RiemannHypothesis.WeylQuadraticQuantitative` succeeds, the file contains no `sorry`,
  and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all seven
  statements; the checks are in `scripts/audit.sh`.
* Six of them are pinned in `scripts/revalidation.lean` with `intDist` and `quadSum` named by
  their fully qualified constants and the hypotheses written out in full, so the coprimality, the
  approximation quality and the ranges of `k`, `q`, `N` cannot be weakened silently.
* None of the statements is vacuous.  For `α = √2/2`, so `2α = √2`, the continued fraction of
  `√2` supplies infinitely many coprime `a/q` with `|√2 − a/q| ≤ 1/q²`, and the convergent
  denominators `1, 2, 5, 12, 29, 70, …` grow by a bounded factor, so the hypothesis
  `N ≤ q² ≤ 4N` is satisfiable for arbitrarily large `N`.
* The hypotheses are load-bearing.  Coprimality is used exactly once, to know `q ∤ a k`, and it
  cannot be dropped: for `a = q` the fraction `a k / q` is an integer and the conclusion fails.
  The range `2k ≤ q` is used to bound the perturbation by half of `1/q`, and `q ≥ 4` is what makes
  `H = q/2` at least `1`.  Taking `q = 1` in `normSq_quadSum_le_of_approx` would assert
  `‖quadSum α N‖² ≤ 4(N+1)²`, which is true but says nothing; the content is in the `q ≍ √N`
  corollaries.
* The `N^(3/4)` conclusion is weaker than the trivial bound `N` only for `N` large, and the
  hypothesis `16 ≤ N` is what makes `√N ≥ 4` and hence `q ≥ 4` available; it is not a way of
  making the statement vacuous, since it excludes only finitely many `N`.
* No unproved `Prop` of this repository occurs among the hypotheses.
