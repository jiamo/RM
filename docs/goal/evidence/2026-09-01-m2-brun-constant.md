# M2-BRUN-CONSTANT — Brun's theorem: the reciprocals of the twin primes converge

## Task

Draw the convergence consequence of the twin-prime counting bound `card_twinPrimes_le` of
`M2-BRUN-TWIN`, which that row left open: the counting bound is of order `N/(log N)²`, which is
summable against `dN/N`, so the reciprocals of the twin primes have a finite sum. This is
Brun's theorem, the first result that distinguished the twin primes from the primes.

## Lean declarations

New file `RiemannHypothesis/BrunConstant.lean` (namespace `RiemannHypothesis.BrunConstant`),
imported by `RiemannHypothesis.lean`:

* `twinInv n` — `1/n` when `n` and `n + 2` are both prime, and `0` otherwise;
  `twinInv_nonneg`, `sum_twinInv_range`;
* `blockSum k` — the dyadic block `∑_{2ᵏ ≤ n < 2ᵏ⁺¹} twinInv n`; `blockSum_nonneg`,
  `sum_twinInv_two_pow` (the dyadic decomposition of the partial sums), `card_Ico_two_pow`;
* `pow_four_le_two_pow` — `k⁴ ≤ 2ᵏ` for `k ≥ 47`;
* `blockSum_le_one`, `sieve_numeric`, `blockSum_le_of_le`, `blockSum_le` — every dyadic block is
  at most `3753/(k+1)²`;
* `sum_inv_sq_range_le` — `∑_{k < K} 1/(k+1)² ≤ 7/4`, from `sum_inv_sq_Icc_one_le` of
  `M2-LARGE-SIEVE-SQUAREFREE`;
* `sum_twinInv_two_pow_le`, `sum_inv_twinPrimes_le`, `sum_range_twinInv_le` — the partial sums
  are at most `6600`, uniformly;
* `summable_twinInv` — **Brun's theorem**;
* `tsum_twinInv_le` — the sum is at most `6600`;
* `nonTwinInv`, `indicator_prime_eq_twinInv_add_nonTwinInv`, `not_summable_nonTwinInv`,
  `infinite_setOf_prime_not_prime_add_two` — infinitely many primes `p` have `p + 2` composite.

The five main statements are pinned as `example … := <declaration>` in
`scripts/revalidation.lean` under the heading `M2-BRUN-CONSTANT`, and their axiom checks are in
`scripts/audit.sh`.

## The statement

```
Summable (fun n => if n.Prime ∧ (n + 2).Prime then 1/n else 0),
∑' n, (if n.Prime ∧ (n + 2).Prime then 1/n else 0) ≤ 6600,
∑_{n < N, n and n + 2 prime} 1/n ≤ 6600  for every N.
```

## The proof

**Dyadic decomposition.** `∑_{n < 2^K} twinInv n = ∑_{k < K} blockSum k`, by induction on `K`
and `Finset.sum_Ico_consecutive`; the term `n = 0` vanishes because `0` is not prime.

**One block.** On `[2ᵏ, 2ᵏ⁺¹)` every term is at most `2^{-k}`, so
`blockSum k ≤ card (twinPrimes 2ᵏ⁺¹) / 2ᵏ`, the twin primes of the block being a subset of the
twin primes below `2ᵏ⁺¹`. For `k ≥ 46` the endpoint `M = 2ᵏ⁺¹` satisfies
`log M = (k+1) log 2 ≥ 47 × 0.6931 > 32`, so `card_twinPrimes_le` applies and

```
card (twinPrimes M) ≤ 900 M/(log M)² + √M + 1.
```

With `t = k + 1` and `P = 2ᵏ`, so that `M = 2P`, the three terms are compared with `P/t²`
(`sieve_numeric`):

* `(log M)² = t² (log 2)² ≥ 0.48 t²`, so `900 M/(log M)² = 1800 P/(log M)² ≤ 3750 P/t²`;
* `t⁴ ≤ M` (`pow_four_le_two_pow`, an induction from `47⁴ ≤ 2⁴⁷`) gives `√M ≤ M/t² = 2P/t²`;
* the same inequality gives `t² ≤ P`, that is `1 ≤ P/t²`.

Hence `card (twinPrimes M) ≤ 3753 P/t²` and `blockSum k ≤ 3753/(k+1)²`. For `k < 46` the crude
bound `blockSum k ≤ 1` suffices, since `3753/(k+1)² ≥ 3753/2116 > 1` there.

**Summation.** `∑_{k < K} 3753/(k+1)² = 3753 ∑_{d ≤ K} 1/d² ≤ 3753 × 7/4 < 6600`, using the
telescoping bound `sum_inv_sq_Icc_one_le`. Since `N < 2^N`, the partial sums over `range N` are
bounded by those over `range (2^N)`, so `∑_{n < N} twinInv n ≤ 6600` for every `N`; the terms
being nonnegative, `summable_of_sum_range_le` and `Real.tsum_le_of_sum_range_le` conclude.

**A corollary.** The indicator of the prime reciprocals splits as `twinInv + nonTwinInv`, where
`nonTwinInv` carries the primes `p` with `p + 2` composite. Mathlib's
`not_summable_one_div_on_primes` says the left-hand side is not summable, and Brun's theorem
makes `twinInv` summable, so `nonTwinInv` is not summable; a function supported on a finite set
is summable, hence the set `{p : p prime, p + 2 composite}` is infinite.

## What is *not* proved

* The bound `6600` is very far from the truth: the Brun constant is `B₂ = 1.902…`. The loss is
  the non-sharp constant `900` of `card_twinPrimes_le` (see the open boundary of
  `M2-BRUN-TWIN`), the dyadic summation in place of partial summation, and the crude treatment
  of the blocks below `2⁴⁶`. No lower bound for the sum is proved, and no numerical value or
  digit of `B₂` is certified.
* Nothing follows about the *number* of twin primes from below: the twin-prime conjecture is
  open, and convergence of the sum is compatible with there being finitely many twin primes.
  In particular `infinite_setOf_prime_not_prime_add_two` is a statement about the non-twin
  primes only, and says nothing about how often `p` and `p + 2` are both prime.
* Only the pair `n, n + 2` is treated: no `n, n + 2k` and no Hardy–Littlewood asymptotics.
* Nothing about `ζ` follows: no zero-free region, no zero-density estimate, no mean value
  theorem.

## Gates

```
lake build RiemannHypothesis.BrunConstant
./scripts/audit.sh
```

`#print axioms` for `blockSum_le`, `sum_inv_twinPrimes_le`, `summable_twinInv`,
`tsum_twinInv_le`, `not_summable_nonTwinInv` and `infinite_setOf_prime_not_prime_add_two`
gives exactly `[propext, Classical.choice, Quot.sound]`; the file contains no
`sorry`.
