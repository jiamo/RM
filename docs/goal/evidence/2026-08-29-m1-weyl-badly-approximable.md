# M1-WEYL-BADLY-APPROXIMABLE — an unconditional rate for a quadratic Weyl sum

Date: 2026-08-29
File: `RiemannHypothesis/WeylBadlyApproximable.lean`

## Claim

Write `quadSum α N = ∑_{0 ≤ n < N} e(α n²)`.

* `normSq_quadSum_le_of_den_le` — the bound of `M1-WEYL-MIN-SUM` in the shape used below: for
  `0 < q ≤ N`, `gcd(a, q) = 1` and `|2α − a/q| ≤ 1/q²`,

      ‖quadSum α N‖² ≤ 16 N²/q + 26 N (1 + log N).

* `exists_coprime_approx` — Dirichlet's approximation theorem in numerator/denominator form: for
  every `n ≥ 1` there are `a : ℤ` and `q : ℕ` with `0 < q ≤ n`, `gcd(a, q) = 1` and
  `|x − a/q| ≤ 1/(q(n+1))`.

* `BadlyApproximable x` — there is a `c > 0` with `|x − a/q| ≥ c/q²` for every fraction `a/q`
  with `q ≥ 1`.

* `le_den_of_badlyApproximable` — for such an `x`, the Dirichlet denominator is large:
  `c/q² ≤ |x − a/q| ≤ 1/(q(n+1))` forces `q ≥ c(n+1)`.

* `normSq_quadSum_le_of_badlyApproximable`, `norm_quadSum_le_of_badlyApproximable` — **the
  unconditional bound**: if `2α` is badly approximable with constant `c > 0`, then for every
  `N ≥ 1`

      ‖quadSum α N‖² ≤ (16/c + 26) N (1 + log N),
      ‖quadSum α N‖  ≤ √((16/c + 26) N (1 + log N)).

  No hypothesis on the size of a denominator is left to the caller.

* `sq_ne_two_mul_sq`, `badlyApproximable_sqrt_two`, `badlyApproximable_sqrt_two'` — `√2` is badly
  approximable, with `c = 1/4`.

* `inv_le_abs_sub_div_of_quadratic`, `badlyApproximable_of_quadratic` — **every quadratic
  irrational is badly approximable**: if `A x² + B x + C = 0` with `A ≠ 0` and `x` irrational then

      |x − a/q| ≥ (1/(|A|(2|x| + 1) + |B|)) / q²    for every fraction a/q with q ≥ 1.

* `exists_norm_quadSum_le_of_badlyApproximable`, `exists_norm_quadSum_le_of_quadratic` — the rate
  with the constant hidden: there is a `K > 0` with `‖quadSum α N‖ ≤ √(K N (1 + log N))` for every
  `N ≥ 1`, whenever `2α` is badly approximable, in particular whenever `2α` is a quadratic
  irrational.

* `norm_quadSum_sqrt_two_le` — hence, for the explicit coefficient `α = √2/2`, for every `N ≥ 1`

      ‖∑_{0 ≤ n < N} e((√2/2) n²)‖ ≤ √(90 N (1 + log N)).

## Proof

`normSq_quadSum_le_of_den_le` is arithmetic on `M1-WEYL-MIN-SUM`'s
`normSq_quadSum_le_of_approx_count`: expanding
`4(N/q + 1)(4N + q(1 + log q)) = 16N²/q + 4N(1 + log q) + 16N + 4q(1 + log q)` and using
`q ≤ N`, so that `log q ≤ log N` and `q(1 + log q) ≤ N(1 + log N)`, the last three terms and the
leading `2N` are together at most `26 N(1 + log N)`.

`exists_coprime_approx` is mathlib's `Real.exists_rat_abs_sub_le_and_den_le` read through
`Rat.num`, `Rat.den` and `Rat.reduced`.

`le_den_of_badlyApproximable` is one cross-multiplication: `c/q² ≤ 1/(q(n+1))` gives
`c q (n+1) ≤ q²`, hence `c(n+1) ≤ q`.

For the main theorem, apply Dirichlet with `n = N`.  The denominator satisfies `q ≤ N`, so
`1/(q(N+1)) ≤ 1/q²` and the approximation is of Weyl quality; and `q ≥ c(N+1) ≥ cN`, so
`16N²/q ≤ 16N/c ≤ (16/c) N (1 + log N)`.  Adding `26 N(1 + log N)` gives the bound, and taking
square roots the second form.

`inv_le_abs_sub_div_of_quadratic` is Liouville's argument for a quadratic.  Put
`f(t) = A t² + B t + C` and `r = a/q`.  The integer `m = A a² + B a q + C q²` is nonzero: if it
vanished then `f(r) = 0`, and subtracting `f(x) = 0` gives `(x − r)(A(x + r) + B) = 0`, so either
`x = r` or `x = −B/A − r`, and both make `x` rational.  Hence `|f(r)| = |m|/q² ≥ 1/q²`.  On the
other hand `f(r) = f(r) − f(x) = (r − x)(A(r + x) + B)`.  If `|x − r| ≥ 1` the conclusion is
immediate since the constant is at most `1`; otherwise `|r| ≤ |x| + 1`, so
`|A(r + x) + B| ≤ |A|(2|x| + 1) + |B| = M`, and `1/q² ≤ |x − r| M`.

`sq_ne_two_mul_sq`: if `a² = 2q²` with `q ≥ 1` then `(|a|/q)² = 2` and `√2 = |a|/q` is rational,
contradicting `irrational_sqrt_two`.  For `badlyApproximable_sqrt_two`, note first that
`(1/4)/q² ≤ 1/4` for `q ≥ 1` and that `1 < √2 < 3/2`.  If `a/q ≤ 0` or `a/q > 2`, then
`|√2 − a/q| > 1/4` outright.  Otherwise `0 < a/q ≤ 2`, and

    |√2 − a/q| (√2 + a/q) = |2 − a²/q²| = |2q² − a²|/q² ≥ 1/q²

because `2q² − a²` is a nonzero integer, while `√2 + a/q ≤ 3/2 + 2 ≤ 4`; hence
`|√2 − a/q| ≥ 1/(4q²)`.  Finally `2·(√2/2) = √2`, and `16/(1/4) + 26 = 90`.

## Why this row exists

`M1-WEYL-EQUIDISTRIBUTION` records as its open boundary: "No rate: delta is an ineffective
minimum depending on H and on the diophantine nature of alpha, so nothing of the shape
`sum e(alpha n^2) = O(N^(1-c))` is proved."  `M1-WEYL-QUADRATIC-QUANTITATIVE` and
`M1-WEYL-MIN-SUM` do prove rates, but each leaves to the caller the hypothesis that a rational
approximation with a denominator in a prescribed range exists, so neither says anything about a
*fixed* `α`.  This row removes that hypothesis for the badly approximable `α` and exhibits an
explicit one: for `α = √2/2` the quadratic Weyl sum is `O(√(N log N))`, effectively and with an
explicit constant.

## Scope, and what is *not* claimed

* The class covered is the badly approximable coefficients — equivalently, those with bounded
  partial quotients — not all irrationals.  For an irrational of infinite type no power saving is
  true, and none is claimed; for such `α` the repository still gives only the `o(N)` of
  `M1-WEYL-EQUIDISTRIBUTION`.
* The logarithm is not removed: the bound is `√(N log N)`, not `N^{1/2+ε}` in the uniform sense.
  The constants `16`, `26`, `90` are not optimized.
* The converse characterization of the class, by bounded partial quotients of the continued
  fraction, is not formalized; what is proved is that the quadratic irrationals belong to it.
* Nothing about `ζ` follows.  Quadratic phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-BADLY-APPROXIMABLE

* The module is imported by `RiemannHypothesis.lean`, `lake build` succeeds, the file contains no
  `sorry`, and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all twelve
  statements; the checks are in `scripts/audit.sh`.
* Seven of them are pinned in `scripts/revalidation.lean` with `quadSum` and `BadlyApproximable`
  named by their fully qualified constants and every hypothesis written out.
* Nothing is vacuous.  `badlyApproximable_sqrt_two` exhibits a member of the Diophantine class, so
  the hypothesis of the main theorem is satisfiable, and `norm_quadSum_sqrt_two_le` is the
  resulting unconditional statement about a concrete real number.  The conclusion is a genuine
  saving: `90 N (1 + log N) < N²` as soon as `N ≥ 600`, so the bound beats the trivial `N` for all
  large `N`.
* The hypotheses are load-bearing.  `0 < c` is used to divide by `c`; `0 < N` is what makes
  Dirichlet's theorem applicable and `log N ≥ 0`.  The Diophantine hypothesis cannot be dropped:
  for `α = 0` the sum equals `N` exactly, and indeed `0` is not badly approximable.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.
