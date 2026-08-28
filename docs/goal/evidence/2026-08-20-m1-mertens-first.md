# Evidence: Mertens' first theorem (2026-08-20)

Row: `M1-MERTENS-FIRST` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/Mertens.lean`:

* `mertensSum x = ∑_{n ≤ x} Λ(n)/n` (a definition).
* `sum_log_eq_sum_vonMangoldt_mul_floor_div` : `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`.
* `sum_log_le` : `∑_{n ≤ N} log n ≤ N log N`.
* `sum_log_ge` : `N log N − N ≤ ∑_{n ≤ N} log n`.
* `sum_vonMangoldt_mul_floor_div_le` : `∑_d Λ(d)⌊N/d⌋ ≤ N ∑_d Λ(d)/d ≤ ∑_d Λ(d)⌊N/d⌋ + ψ(N)`.
* `mertens_first_nat` : `|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4` for `N ≥ 1`.
* `mertens_first` : `|mertensSum x − log x| ≤ log 4 + 4 + log 2` for real `x ≥ 1`.
* `mertens_first_isBigO` : `mertensSum x − log x = O(1)` at `atTop`.
* `primeLogSum x = ∑_{p ≤ x} log p / p` (a definition), and the prime form of the theorem:
  `properPrimePower_sum_le` (the proper prime powers contribute at most `8`),
  `mertensSum_sub_primeLogSum_bounds` (`0 ≤ mertensSum x − primeLogSum x ≤ 8`),
  `mertens_first_prime` : `|∑_{p ≤ x} log p/p − log x| ≤ log 4 + 12 + log 2` for `x ≥ 1`, and
  `mertens_first_prime_isBigO`.

Mathlib contains none of Mertens' three theorems.

## The argument

1. `∑_{d ∣ n} Λ(d) = log n` (Mathlib's `ArithmeticFunction.vonMangoldt_sum`). Summing over
   `n ≤ N` and interchanging the two summations — the inner count is
   `#{n ≤ N : d ∣ n} = ⌊N/d⌋`, Mathlib's `Nat.Ioc_filter_dvd_card_eq_div` — gives
   `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`.
2. `∑_{n ≤ N} log n ≤ N log N` termwise; and `∑_{n ≤ N} log n ≥ N log N − N` by induction,
   the step being `N log(1 + 1/N) ≤ 1`, i.e. `log(1+u) ≤ u`.
3. `0 ≤ N/d − ⌊N/d⌋ < 1` and `Λ ≥ 0` give
   `∑_d Λ(d)⌊N/d⌋ ≤ N ∑_d Λ(d)/d ≤ ∑_d Λ(d)⌊N/d⌋ + ψ(N)`, and
   `ψ(N) ≤ (log 4 + 4) N` is Mathlib's `Chebyshev.psi_le_const_mul_self`.

Combining, `N(log N − 1) ≤ N ∑_{n ≤ N} Λ(n)/n ≤ N(log N + log 4 + 4)`; dividing by `N ≥ 1`
gives the integer form. For real `x ≥ 1` the passage from `⌊x⌋` to `x` costs
`log x − log⌊x⌋ ≤ log 2`, because `⌊x⌋ ≥ x/2` for `x ≥ 1`.

For the prime form, the difference between `∑_{n ≤ x} Λ(n)/n` and `∑_{p ≤ x} log p/p` is the
contribution of the proper prime powers. Each such `n` is written as `p^k` with
`p = minFac n` and `k = ν_p(n) ≥ 2`; the map `n ↦ (p, k)` is injective, so the contribution is
at most `∑_{p = 2}^{N} ∑_{k = 2}^{N} log p / p^k`. The geometric tail gives
`∑_{k ≥ 2} p^{−k} ≤ 2/p²`, and `log m ≤ 2√m` together with the telescoping bound
`∑_{m ≥ 2} 1/(m√m) ≤ 2` gives `∑_{m = 2}^{N} log m/m² ≤ 4`. Hence the correction is at most
`2 · 4 = 8`, and it is non-negative because `Λ ≥ 0`.

## Commands run

```
lake build RiemannHypothesis.Mertens
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `mertens_first_nat`, `mertens_first`, `mertens_first_isBigO` reports
exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* Mertens' *second* theorem `∑_{p ≤ x} 1/p = log log x + M + o(1)` and his *third* theorem
  (the product form) are not proved here; nor is the sharper form of the first theorem with
  the constant `−γ`. What is proved is boundedness of the error, with the explicit constant
  `log 4 + 4 + log 2 ≈ 6.08`.
* This is not the prime number theorem, and does not imply it: Mertens' first theorem is
  strictly weaker.

## Adversarial revalidation: M1-MERTENS-FIRST

Second, independent pass.

* **Claim mode.** All items are `theorem`s proved in this repository; `mertensSum` is a
  `def`, and the theorems are stated about it, not about a `Prop` placeholder. The Mathlib
  inputs are named: `ArithmeticFunction.vonMangoldt_sum`, `Nat.Ioc_filter_dvd_card_eq_div`,
  `Chebyshev.psi_le_const_mul_self`.
* **Constants, checked by hand.** At `N = 10`,
  `∑_{n ≤ 10} Λ(n)/n = log 2/2 + log 3/3 + log 2/4 + log 5/5 + log 7/7 + log 2/8 + log 3/9
  ≈ 1.695` and `log 10 ≈ 2.303`, so the error is `≈ −0.61`, comfortably inside
  `log 4 + 4 ≈ 5.386`. The two sides of the sandwich are the ones proved: the lower error
  `−1` comes from `∑ log n ≥ N log N − N`, the upper error `log 4 + 4` from Chebyshev's
  upper bound for `ψ`; neither is claimed to be optimal (the true error tends to `−γ`).
* **Vacuity and load-bearing hypotheses.** `N ≥ 1` is needed to divide by `N`; at `N = 0`
  the sum is empty and `log 0 = 0` in Lean, so the statement would be true but empty. `x ≥ 1`
  is needed both for `⌊x⌋ ≥ 1` and for `⌊x⌋ ≥ x/2`. The conclusion is a genuine two-sided
  bound on a non-trivial quantity, not an inequality between a term and itself.
* **The prime form, checked by hand.** At `x = 10`,
  `∑_{p ≤ 10} log p/p = log 2/2 + log 3/3 + log 5/5 + log 7/7 ≈ 1.313` against
  `log 10 ≈ 2.303`; the error `≈ −0.99` is inside `log 4 + 12 + log 2 ≈ 14.1`. The correction
  bound `8` is genuine (the true value of `∑_{p, k ≥ 2} log p/p^k` is `≈ 0.755`), and the
  three inputs to it — `∑_{k ≥ 2} r^k ≤ 2r²` for `r ≤ 1/2`, `log m ≤ 2√m`, and
  `∑_{m=2}^{M} 1/(m√m) ≤ 2` — are each proved here, not assumed.
* **Statement pinning.** `scripts/revalidation.lean` writes out `mertensSum`, `primeLogSum`,
  `mertens_first_nat`, `mertens_first`, `mertens_first_isBigO`, `mertens_first_prime` and
  `mertens_first_prime_isBigO` in full and supplies the repository's declarations as the
  proof terms; `scripts/audit.sh` prints their axioms.
