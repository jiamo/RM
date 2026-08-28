# M1-EULER-MACLAURIN — the Euler–Maclaurin representation of ζ and the logarithmic bound

Date: 2026-08-20
File: `RiemannHypothesis/EulerMaclaurin.lean`
Gates: `lake build`, `bash scripts/audit.sh`

## What is proved

Write `a_n = (n+1)^(-s) - ∫_{n+1}^{n+2} x^(-s) dx` for the error committed when the integral
of `x ↦ x^(-s)` over `[n+1, n+2]` is replaced by the value at the left endpoint.  In the file
this is `RiemannHypothesis.eulerTerm n s`, defined in closed form as

```
eulerTerm n s = (n+1)^(-s) - ((n+1)^(1-s) - (n+2)^(1-s)) / (s - 1)
```

and `eulerTerm_eq_integral` identifies it with the integral above (for `s ≠ 1`), using
`integral_cpow`.

1. `norm_cpow_neg_sub_le` — a mean value bound for `x ↦ x^(-s)`:
   `‖u^(-s) - v^(-s)‖ ≤ ‖s‖ (log v - log u) u^(-re s)` for `0 < u ≤ v` and `0 ≤ re s`.
   Proved by writing `x^(-s) = exp(-s log x)` and applying
   `Convex.norm_image_sub_le_of_norm_deriv_le` on the segment joining `-s log u` to `-s log v`.

2. `norm_eulerTerm_le` — `‖eulerTerm n s‖ ≤ ‖s‖ (n+1)^(-(1 + re s))` for `0 ≤ re s`, `s ≠ 1`.
   The integral representation plus (1) plus `log(1 + 1/(n+1)) ≤ 1/(n+1)`.

3. `riemannZeta_eq_zetaApprox` — **the Euler–Maclaurin representation**: for every `N : ℕ`
   and every `s` with `1 < re s`,

   ```
   ζ(s) = ∑_{n < N} (n+1)^(-s) + (N+1)^(1-s)/(s-1) + ∑'_n eulerTerm (n + N) s .
   ```

   The proof is elementary: the Dirichlet series converges absolutely, the tail splits as
   `∑'_n (n+N+1)^(-s) = ∑'_n eulerTerm(n+N) s + ∑'_n (g n - g (n+1))` with
   `g n = (n+N+1)^(1-s)/(s-1)`, and the telescoping series sums to `g 0 = (N+1)^(1-s)/(s-1)`
   because `g n → 0` (here `re(1-s) < 0`).  No analytic continuation and no differentiation
   under the integral sign are used.

4. `norm_riemannZeta_le_log_of_one_lt_re` — for `1 < re s ≤ 2` and `|im s| ≥ 2`,

   ```
   ‖ζ(s)‖ ≤ 6 + log(1 + |im s|).
   ```

   Take `N = ⌈|im s|⌉₊` in (3).  The truncated Dirichlet sum is at most the harmonic number
   `H_N ≤ 1 + log N ≤ 1 + log(1 + |t|)` (mathlib's `harmonic_le_one_add_log`); the pole term
   is at most `1/2` because `(N+1)^(1-σ) ≤ 1` and `‖s-1‖ ≥ |t| ≥ 2`; and the Euler–Maclaurin
   tail is at most `‖s‖ · 2/(N+1) ≤ (2+|t|)·2/(1+|t|) ≤ 4`, using mathlib's
   `sum_Ioo_inv_sq_le` for the tail of the `p`-series.

5. `norm_riemannZeta_le_log` — the same bound on the closed strip `1 ≤ re s ≤ 2`.  The
   representation (3) needs `re s > 1`, so the line `re s = 1` is reached by continuity:
   `σ ↦ ζ(σ + it)` is continuous at `σ = 1` when `t ≠ 0` (`differentiableAt_riemannZeta`),
   and the bound of (4) holds on `(1, 2)`, so it passes to the limit along `𝓝[>] 1`.

## Why this matters for the board

`M1-GROWTH` asked for the bound used by the zero-free-region argument, `|ζ(σ+it)| = O(log t)`
for `1 < σ ≤ 2`.  That is item (4), in the stronger form of a bound uniform in `σ` (no
`1/(σ-1)` factor) and valid down to `σ = 1` by item (5).  The eta route of
`RiemannHypothesis/Growth.lean` provably cannot give it: the factor `1 - 2^(1-s)` vanishes on
`re s = 1` at arbitrarily large heights.

## Verification

* `lake build` succeeds; `RiemannHypothesis/EulerMaclaurin.lean` contains no `sorry`.
* `#print axioms` for `riemannZeta_eq_zetaApprox`, `norm_riemannZeta_le_log_of_one_lt_re` and
  `norm_riemannZeta_le_log` gives exactly `[propext, Classical.choice, Quot.sound]`.
* The claims are pinned in `scripts/revalidation.lean` (section `M1-EULER-MACLAURIN`), and the
  axiom checks are part of `scripts/audit.sh`.

## What is still open

The convexity bound `|ζ(σ+it)| = O(|t|^((1-σ)/2 + ε))` inside the critical strip is *not*
proved here; it needs the approximate functional equation, which needs the full
Euler–Maclaurin expansion with Bernoulli polynomials (or Phragmén–Lindelöf applied to the
functional equation).  `M1-GROWTH` therefore stays `DONE_WEAK`.
