# Evidence: Chebyshev's lower bound for ψ, θ and π (2026-08-20)

Row: `M1-CHEBYSHEV-BOUNDS` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ChebyshevLower.lean`:

* `log_eq_sum_factorization_mul_log` : `log m = ∑_{p ∣ m} ν_p(m) · log p` for `m ≠ 0`.
* `sum_factorization_mul_log_le_psi` : if `p ^ ν_p(m) ≤ N` for every prime `p ∣ m`, then
  `∑_p ν_p(m) log p ≤ ψ N`.
* `log_le_psi_of_pow_factorization_le` : the same conclusion phrased as `log m ≤ ψ N`.
* `log_centralBinom_le_psi` : `log C(2n, n) ≤ ψ(2n)` for `n ≥ 1`.
* `psi_two_mul_ge` : `2n log 2 − log n ≤ ψ(2n)` for `n ≥ 4`.
* `psi_lower_bound` : `(x − 2) log 2 − log x ≤ ψ(x)` for real `x ≥ 8`.
* `psi_ge_half_log_two_mul` : `(log 2 / 2) x ≤ ψ(x)` for real `x ≥ 12`.
* `theta_ge_eventually` : `(log 2 / 4) x ≤ θ(x)` for all large `x`.
* `primeCounting_ge_eventually` : `(log 2 / 4) · x / log x ≤ π(⌊x⌋)` for all large `x`.
* `psi_asymptotic_bounds`, `theta_asymptotic_bounds` : the two-sided bounds `ψ(x) ≍ x` and
  `θ(x) ≍ x`, combining the lower bounds proved here with Mathlib's upper bounds.
* `primeCounting_asymptotic_bounds` : **Chebyshev's theorem**, the two-sided bound
  `c · x/log x ≤ π(⌊x⌋) ≤ C · x/log x` for all large `x`, with `c = log 2 / 4` and
  `C = log 4 + 1`.

Mathlib supplies Chebyshev's *upper* bounds (`Chebyshev.theta_le_log4_mul_x`,
`Chebyshev.psi_le_const_mul_self`, `Chebyshev.eventually_primeCounting_le`) and lists the
lower bound as a TODO in `Mathlib/NumberTheory/Chebyshev.lean`; the lower bound is proved
here.

## The argument

Chebyshev's central-binomial argument, in three steps.

1. **Arithmetic.** For `m ≠ 0`, `log m = ∑_p ν_p(m) log p`. If every prime power
   `p ^ ν_p(m)` is at most `N`, then the integers `p ^ j` with `1 ≤ j ≤ ν_p(m)` are pairwise
   distinct elements of `(0, N]`, and the von Mangoldt function takes the value `log p` at
   each of them. Summing the non-negative function `Λ` over that subset of `(0, N]` gives
   `∑_p ν_p(m) log p ≤ ψ N`.
2. **Kummer's bound.** `p ^ ν_p(C(2n,n)) ≤ 2n` (Mathlib's
   `Nat.pow_factorization_choose_le`), hence `log C(2n, n) ≤ ψ(2n)`.
3. **Size of the central binomial coefficient.** `4 ^ n < n · C(2n, n)` for `n ≥ 4`
   (Mathlib's `Nat.four_pow_lt_mul_centralBinom`), hence
   `ψ(2n) ≥ log C(2n,n) > n log 4 − log n = 2n log 2 − log n`.

For real `x ≥ 8` take `n = ⌊x/2⌋ ≥ 4`; then `2n ≤ x` and `2n > x − 2`, and `ψ` is monotone,
so `ψ(x) ≥ (x − 2) log 2 − log x`. The constant form for `x ≥ 12` uses the concavity bound
`log x ≤ 4 log 2 + x/16 − 1` together with `0.6931471803 < log 2 < 0.6931471808`
(`Real.log_two_gt_d9`, `Real.log_two_lt_d9`); with `L = log 2` the required inequality is
`(L/2 − 1/16) x ≥ 6L − 1`, and at `x = 12` the left side is at least `3.40` while the right
side is at most `3.16`.

The transfer to `θ` uses Mathlib's `|ψ(x) − θ(x)| ≤ 2 √x log x` and `log x / √x → 0`,
which loses only half of the constant. The transfer to `π` uses Mathlib's Abel-summation
identity `π(⌊x⌋) = θ(x)/log x + ∫₂ˣ θ(t)/(t log²t) dt`, whose integrand is non-negative,
so `π(⌊x⌋) ≥ θ(x)/log x`.

## Commands run

```
lake build RiemannHypothesis.ChebyshevLower
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for every theorem listed above reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* This is **not** the prime number theorem. Chebyshev's bounds give
  `π(x) ≍ x/log x` with explicit constants `log 2/4 ≈ 0.173` and `log 4 + 1 ≈ 2.386`, not
  the asymptotic `π(x) ∼ x/log x`; the row `M1-PNT` therefore stays open, and its remaining
  content is still exactly `ψ(x) ~ x`.
* The constants are not optimal (Chebyshev's own constants are `0.921` and `1.106`), and no
  claim of optimality is made.

## Adversarial revalidation: M1-CHEBYSHEV-BOUNDS

Second, independent pass.

* **Claim mode.** Every item above is a `theorem` proved in this repository, not a `def` of
  a `Prop` and not a Mathlib re-export. The two Mathlib inputs used are named explicitly
  (`Nat.pow_factorization_choose_le`, `Nat.four_pow_lt_mul_centralBinom`), as are the two
  Mathlib results used for the transfer to `θ` and `π`
  (`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`,
  `Chebyshev.primeCounting_eq_theta_div_log_add_integral`) and the Mathlib upper bound
  `Chebyshev.eventually_primeCounting_le` used for the upper half of
  `primeCounting_asymptotic_bounds`.
* **Constants, checked by hand.** At `x = 12` the claim `psi_ge_half_log_two_mul` asserts
  `ψ(12) ≥ 6 log 2 ≈ 4.159`; in fact
  `ψ(12) = 3 log 2 + 2 log 3 + log 5 + log 7 + log 11 ≈ 10.23`, so the bound holds with
  room to spare. At `x = 8`, `psi_lower_bound` asserts
  `ψ(8) ≥ 6 log 2 − log 8 = 3 log 2 ≈ 2.079`; in fact
  `ψ(8) = 3 log 2 + log 3 + log 5 + log 7 ≈ 5.30`. The threshold `n ≥ 4` in
  `psi_two_mul_ge` is load-bearing: `4 ^ n < n · C(2n,n)` fails at `n = 1` (`4 > 2`), and
  the conclusion `2n log 2 − log n ≤ ψ(2n)` itself fails at `n = 1`, where
  `2 log 2 ≈ 1.386 > log 2 = ψ(2)`. The threshold `x ≥ 12` in `psi_ge_half_log_two_mul` is
  needed for the elementary comparison used: at `x = 8` the inequality
  `(L/2 − 1/16)x ≥ 6L − 1` reads `2.27 ≥ 3.16`, which is false.
* **Vacuity.** No hypothesis is unsatisfiable: `x ≥ 8`, `x ≥ 12`, `n ≥ 4` and the filter
  `atTop` all describe non-empty situations, and the conclusions are non-trivial
  inequalities (each right-hand side is a genuine Chebyshev function value, and each left
  side is positive for large `x`).
* **Statement pinning.** `scripts/revalidation.lean` writes out `psi_lower_bound`,
  `psi_ge_half_log_two_mul`, `theta_ge_eventually`, `primeCounting_ge_eventually`,
  `primeCounting_asymptotic_bounds`, `psi_asymptotic_bounds` and `theta_asymptotic_bounds`
  in full and supplies the repository's declarations as the proof terms;
  `scripts/audit.sh` prints their axioms.
