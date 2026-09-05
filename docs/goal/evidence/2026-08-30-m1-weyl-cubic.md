# M1-WEYL-CUBIC — Weyl's bound for a cubic exponential sum

Date: 2026-08-30
File: `RiemannHypothesis/WeylCubic.lean`

## Claim

Write `e(x) = exp(2πix)`, `cubeSum α N = ∑_{0 ≤ n < N} e(α n³)`, and let
`dioMaj β N m = min(N, 1/(2‖β m‖))`, where `‖·‖` is the distance to the nearest integer
(`intDist`) and the value is taken to be `N` when `β m` is an integer, so that no convention for
`1/0` is needed.

* `norm_linSum_le_dioMaj` — a linear exponential sum of length at most `N` and frequency `β m` is
  bounded by `dioMaj β N m`.

* `mul_normSq_cubeSum_le` — **the first differencing**: for `H ≥ 1`,

      H ‖cubeSum α N‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} cubeInner α N k),

  where `cubeInner α N k = ‖∑_{0 ≤ n < N − k} e(α(n+k)³ − α n³)‖` is the once-differenced sum,
  whose phase is quadratic.

* `cubic_second_diff` — the twice-differenced phase is linear in `n`:

      α(n+l+k)³ − α(n+l)³ − α(n+k)³ + α n³ = (6α k l) n + α(3kl² + 3k²l).

* `mul_sq_cubeInner_le` — **the second differencing**: for `0 < k ≤ N` and `H ≥ 1`,

      H (cubeInner α N k)² ≤ (N + H − 1) (N + 2 ∑_{0 < l < H} dioMaj (6α) N (k l)).

* `sum_double_le` — the double sum, through the counting lemma of `M1-WEYL-MIN-SUM`: if `a`, `q`
  are coprime and `|β − a/q| ≤ 1/q²`, then

      ∑_{0<k<H} ∑_{0<l<H} dioMaj β N (k l) ≤ H (H²/q + 1)(4N + q(1 + log q)).

* `norm_cubeSum_pow_four_le_of_approx` — the assembled inequality, with `H` free.

* `norm_cubeSum_pow_eight_le_of_approx` — **the main bound**, with `H = ⌊√N⌋ + 1`: if `a`, `q` are
  coprime, `0 < q ≤ 4N` and `|6α − a/q| ≤ 1/q²`, then for every `N ≥ 1`

      ‖cubeSum α N‖⁸ ≤ 2²² (4N/q + 1)² N⁷ (1 + log 4N)².

  For `q` of order `N` this reads `‖cubeSum α N‖ ≪ N^{7/8} (log N)^{1/4}`, a power saving against
  the trivial `N`.

* `norm_cubeSum_pow_eight_le_of_badlyApproximable` — **the unconditional form**: if `6α` is badly
  approximable with constant `c > 0`, i.e. `|6α − a/q| ≥ c/q²` for every fraction, then for every
  `N ≥ 1`

      ‖cubeSum α N‖⁸ ≤ 2²² (4/c + 1)² N⁷ (1 + log 4N)².

* `norm_cubeSum_sqrt_two_le` — the explicit instance `α = √2/6`, for which `6α = √2` is badly
  approximable with `c = 1/4`: for every `N ≥ 1`

      ‖∑_{0 ≤ n < N} e((√2/6) n³)‖⁸ ≤ 2³¹ N⁷ (1 + log 4N)².

## Proof

`M1-WEYL-QUADRATIC` applies van der Corput's A process once, to a phase whose difference is
already linear.  A cubic phase needs the process twice.

The first step is `norm_sq_sum_e2pi_le` of `M1-WEYL-DIFFERENCING` applied to `f n = α n³`; the
inner sums are the `cubeInner α N k`.  Each of these is an exponential sum of length `N − k` with
a *quadratic* phase, so the A process applies to it as well, and by `cubic_second_diff` its
differenced phase is linear in `n` with leading coefficient `6α k l`; the geometric-series bound
`norm_geomSum_e2pi_le`, in the form `norm_linSum_le_dioMaj`, bounds the resulting inner sums by
`dioMaj (6α) N (k l)`.  That is `mul_sq_cubeInner_le`.

Cauchy–Schwarz over the at most `H − 1` shifts `k` (mathlib's
`Finset.sum_mul_sq_le_sq_mul_sq`, against the constant function `1`) converts `(∑_k cubeInner α N k)²` into
`H ∑_k (cubeInner α N k)²`, so the two differencings combine into a bound for `‖cubeSum α N‖⁴` in
terms of the double sum `∑_{k,l} dioMaj (6α) N (k l)`.

`sum_double_le` folds that double sum onto the single variable `m = k l`.  For a fixed `k` the map
`l ↦ k l` is injective and sends `(0, H)` into `(0, H²]`, so reindexing through
`Finset.sum_image` and `Finset.sum_le_sum_of_subset_of_nonneg` bounds each row by `∑_{0 < m ≤ H²} dioMaj (6α) N m`, which is exactly the shape the
counting lemma `sum_Ioc_le` of `M1-WEYL-MIN-SUM` bounds — `dioMaj` satisfies its two hypotheses,
`0 ≤ g ≤ N` (`dioMaj_nonneg`, `dioMaj_le`) and `g m · 2‖β m‖ ≤ 1` (`dioMaj_mul_intDist_le`).
There are at most `H` rows.  No divisor-function estimate is needed: the crude count
`#{l : k l = m} ≤ 1` for fixed `k` suffices, at the cost of a worse exponent.

`norm_cubeSum_pow_four_le_of_approx` is the assembly, with `H` free.  Choosing `H = ⌊√N⌋ + 1`, so
that `√N ≤ H ≤ 2√N` and `H² ≤ 4N`, and squaring, gives the eighth-power bound; the real
arithmetic is isolated in the standalone lemma `cubic_bound_numeric`, which works with abstract
variables `n, h, P, B, L, R, S` so that no large `nlinarith` call is needed inside the main proof.
The hypothesis `q ≤ 4N` is what lets `log q ≤ log 4N` absorb the logarithms into a single factor
`(1 + log 4N)`.

The unconditional form repeats the argument of `M1-WEYL-BADLY-APPROXIMABLE`: `exists_coprime_approx`
(Dirichlet, with `n = N`) produces a coprime `a/q` with `q ≤ N` and `|6α − a/q| ≤ 1/(q(N+1))`,
hence `≤ 1/q²`, and `le_den_of_badlyApproximable` forces `q ≥ c(N + 1)`, so `4N/q ≤ 4/c`.  Finally
`badlyApproximable_sqrt_two` gives `c = 1/4` for `6·(√2/6) = √2`, and `2²²(4/(1/4) + 1)² = 2²²·289
≤ 2³¹`.

## Why this row exists

The open boundary of `M1-WEYL-QUADRATIC` reads "Only a quadratic phase.  The general degree-`d`
Weyl inequality requires the A process iterated `d − 1` times and is not proved", and
`M1-WEYL-MIN-SUM` repeats it.  This row does the first iterated case, `d = 3`, and shows that the
counting lemma proved there is exactly the right input: nothing beyond it, and the folding of the
pairs `(k, l)`, is needed for a power saving.  It also produces the repository's first effective
power saving for a *cubic* phase at a concrete irrational coefficient.

## Scope, and what is *not* claimed

* The exponent is `7/8`, **weaker than the classical Weyl exponent `3/4`** for a cubic phase.  The
  losses are the Cauchy–Schwarz over the shifts and the crude folding of the pairs `(k, l)`, which
  the classical argument avoids with an average divisor bound.  The constants `2²²`, `2³¹` are not
  optimized and the logarithm is not removed.
* Only degree `3`.  The general degree-`d` Weyl inequality, by induction on `d`, is not
  formalized, and neither is Vinogradov's mean value theorem, which is what large `d` needs.
* The conditional form assumes a rational approximation to `6α` with a large denominator, and the
  unconditional form assumes `6α` badly approximable.  Both are necessary: for `α` close to a
  rational with a small denominator there is no cancellation at all.
* Nothing about `ζ` follows.  Cubic phases are not the phase of `ζ`, and no subconvexity bound,
  approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-CUBIC

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylCubic`
  succeeds, the file contains no `sorry`, and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_cubeSum_pow_four_le_of_approx`, `norm_cubeSum_pow_eight_le_of_approx`,
  `norm_cubeSum_pow_eight_le_of_badlyApproximable` and `norm_cubeSum_sqrt_two_le`; the checks are
  in `scripts/audit.sh`.
* The main statements are pinned in `scripts/revalidation.lean` with `cubeSum` named by its fully
  qualified constant and every hypothesis written out.
* Nothing is vacuous.  `badlyApproximable_sqrt_two` exhibits a coefficient satisfying the
  Diophantine hypothesis, and `norm_cubeSum_sqrt_two_le` is the resulting unconditional statement
  about a concrete real number.  The conclusion is a genuine saving: `2³¹ N⁷ (1 + log 4N)² < N⁸`
  for all sufficiently large `N`, so the bound beats the trivial `‖cubeSum α N‖ ≤ N`.
* The hypotheses are load-bearing.  `0 < N` gives `log 4N ≥ 0` and makes Dirichlet's theorem
  applicable; `0 < c` is used to divide by `c`; coprimality of `a` and `q` is what makes the grid
  argument behind the counting lemma work; `q ≤ 4N` is what merges the logarithms.  The
  Diophantine hypothesis cannot be dropped: for `α = 0` the sum equals `N` exactly, and `0` is not
  badly approximable.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.
