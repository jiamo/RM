# M1-WEYL-MIN-SUM — the counting lemma of Weyl's method, and the exponent `1/2`

Date: 2026-08-29
File: `RiemannHypothesis/WeylMinSum.lean`

## Claim

Write `intDist θ = |θ − round θ|` for the distance to the nearest integer and
`quadSum α N = ∑_{0 ≤ n < N} e(α n²)`.

* `sum_block_le` — **the block bound**.  Let `q ≥ 1`, `gcd(a, q) = 1` and `|β − a/q| ≤ 1/q²`,
  and let `g : ℤ → ℝ` satisfy `0 ≤ g k ≤ N` and `g k · 2·intDist (β k) ≤ 1` for all `k` — the two
  properties of `min(N, 1/(2‖βk‖))`, written so that no convention for `1/0` is needed.  Then for
  every `x : ℤ`

      ∑_{x < k ≤ x + q} g k ≤ 4N + q (1 + log q).

* `sum_Ioc_le` — **the counting lemma**, the block bound iterated over `⌊H/q⌋ + 1` blocks:

      ∑_{0 < k ≤ H} g k ≤ (H/q + 1) (4N + q (1 + log q)).

* `normSq_quadSum_le_of_approx_count` — **Weyl's inequality with the counting lemma**: for
  `q ≥ 1`, `N ≥ 1`, `gcd(a, q) = 1` and `|2α − a/q| ≤ 1/q²`,

      ‖quadSum α N‖² ≤ 2N + 4 (N/q + 1) (4N + q (1 + log q)),

  the classical shape `N² (1/q + 1/N + q/N²)`, up to logarithms.

* `normSq_quadSum_le_of_approx_large`, `norm_quadSum_le_of_approx_large` — for a denominator in
  the range `N ≤ q ≤ 2N`,

      ‖quadSum α N‖² ≤ 66 N (1 + log 2N),      ‖quadSum α N‖ ≤ 9 √(N (1 + log 2N)).

## Proof

The block bound is the classical argument.  Write `β = a/q + θ` with `|θ| ≤ 1/q²`.  On a block
`k = x + r` with `1 ≤ r ≤ q`, the perturbation `θ r` has absolute value at most `1/q`, so
`intDist (β k) ≥ intDist (β x + a r / q) − 1/q` by the Lipschitz property
`intDist_le_intDist_add_abs_sub` of `M1-WEYL-QUADRATIC-QUANTITATIVE`.  Since `a` is invertible
modulo `q`, the numbers `β x + a r / q`, as `r` runs over the block, are the `q` points
`(i + f)/q`, `0 ≤ i < q`, of an arithmetic progression of step `1/q` covering the circle exactly
once: `gridIndex` names the index `i`, `grid_sub_le_intDist` gives
`intDist (β k) ≥ (i-th grid distance) − 1/q`, and `gridIndex_injOn` — a consequence of
`IsCoprime (q, a)` through `Int.eq_zero_of_abs_lt_dvd` — is the injectivity.

The majorant `weylMajorant N q i` is `N` for the four indices `i ∈ {0, 1, q−1, q}` closest to the
integers and `q/(i − 1)` respectively `q/(q − i − 1)` otherwise; `le_weylMajorant` is the
pointwise bound and `sum_weylMajorant_le` its total mass, the four exceptional points
contributing `4N` and the rest two harmonic sums, at most `q(1 + log q)` in total by
`sum_range_inv_succ_le` (from mathlib's `harmonic_le_one_add_log`).  Summing over
`n = ⌊H/q⌋ + 1` consecutive blocks (`sum_Ioc_mul_le`, by induction, splitting the interval with
`Finset.Ioc_union_Ioc_eq_Ioc`) gives the counting lemma.

For the Weyl bound, `M1-WEYL-DIFFERENCING`'s `norm_sq_sum_e2pi_le` with `H = N` gives

    ‖quadSum α N‖² ≤ 2N + 4 ∑_{0 < k < N} ‖∑_n e((2αk) n + α k²)‖,

and each inner sum is bounded both by `N` and by `1/(2 intDist (2αk))`
(`quadInner_le`, `quadInner_mul_intDist_le`, from `norm_geomSum_e2pi_le`), so `quadInner α N` is
an admissible `g` for `β = 2α`, and the counting lemma applies.  For `N ≤ q ≤ 2N` one has
`N/q + 1 ≤ 2` and `q (1 + log q) ≤ 2N (1 + log 2N)`, whence the constant `66`; taking square
roots and using `66 ≤ 81` gives the `9 √(N(1 + log 2N))` form.

## Why this row exists

`M1-WEYL-QUADRATIC-QUANTITATIVE` recorded in its scope section that "the exponent is `3/4`, not
the `1/2 + ε` of Weyl's inequality.  Reaching that requires the counting lemma
`∑_{k<H} min(N, 1/intDist(αk)) ≪ (H/q + 1)(N + q log q)`, which lets one take `H` as large as `N`
rather than `q/2`; it is not formalized here."  `M1-WEYL-QUADRATIC` carried the same sentence in
its open boundary.  This row formalizes exactly that lemma and draws exactly that consequence:
the differencing length is now `N`, and the exponent is `1/2` up to a logarithm.

## Scope, and what is *not* claimed

* The logarithm is not removed: the bound is `√(N log N)`, not `N^(1/2+ε)` for every `ε` in the
  usual uniform sense, and no attempt is made to optimize the constants `4`, `66`, `9`.
* As it must be, the bound is conditional on the *existence* of a rational approximation with a
  large denominator (`N ≤ q ≤ 2N`).  For `α` close to a rational with small denominator the sum
  has no cancellation at all.  Dirichlet's theorem gives some `q ≤ Q` with `|2α − a/q| ≤ 1/(qQ)`
  but not a `q` in a prescribed range, so no unconditional statement about a fixed irrational `α`
  is drawn.
* Only the quadratic phase.  The general degree-`d` Weyl inequality, which iterates the
  differencing `d − 1` times and feeds the same counting lemma, is still not formalized.
* Nothing about `ζ` follows.  Quadratic phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-MIN-SUM

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylMinSum`
  and the full `lake build` succeed, the file contains no `sorry`, and the build emits no warning
  for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for `sum_block_le`,
  `sum_Ioc_le`, `normSq_quadSum_le_of_approx_count`, `normSq_quadSum_le_of_approx_large` and
  `norm_quadSum_le_of_approx_large`; the checks are in `scripts/audit.sh`.
* All five are pinned in `scripts/revalidation.lean` with `intDist` and `quadSum` named by their
  fully qualified constants and every hypothesis written out, so the coprimality, the quality of
  the approximation and the ranges of `q` and `N` cannot be weakened silently.
* No statement is vacuous.  The hypotheses on `g` are satisfied by `quadInner α N`, which is what
  the application does; and the diophantine hypothesis is satisfiable for arbitrarily large `N`,
  for instance for `α = √2/2`, where the continued fraction of `2α = √2` supplies infinitely many
  coprime `a/q` with `|√2 − a/q| ≤ 1/q²`, and taking `N = q` meets `N ≤ q ≤ 2N`.
* The hypotheses are load-bearing.  Coprimality is used exactly once, in `gridIndex_injOn`, and
  is necessary: for `a = 0` all the grid points coincide and the block sum is `qN`, not
  `4N + q(1 + log q)`.  The approximation quality `1/q²` is what keeps the perturbation `θ r`
  below `1/q`, one grid step; with `1/q` in its place the grid argument collapses.  The bound
  `g k ≤ N` is what handles the four grid points nearest the integers, where the reciprocal of
  the distance is unbounded.
* The improvement over `M1-WEYL-QUADRATIC-QUANTITATIVE` is real and not a restatement: there the
  differencing stopped at `H = q/2 ≍ √N`, giving `‖quadSum α N‖ ≤ 7 N^{3/4}`; here it runs to
  `H = N`, giving `‖quadSum α N‖ ≤ 9 √(N(1 + log 2N))`, which is smaller for all large `N`.
* No unproved `Prop` of this repository occurs among the hypotheses.
