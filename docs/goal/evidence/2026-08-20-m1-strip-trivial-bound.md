# Evidence: the trivial convexity bound for `ζ` inside the critical strip (2026-08-20)

Rows: `M1-STRIP-TRIVIAL-BOUND` (new, `DONE_STRONG`), `M1-GROWTH` (still `DONE_WEAK`).

## What is proved (without `sorry`)

### `RiemannHypothesis/StripGrowth.lean`

* `strip_bound_arith` : the elementary inequality
  `2T(2+L) + T + (2/σ)T ≤ (8/σ) T (1+L)` for `0 < σ ≤ 1`, `1 ≤ L`, `0 ≤ T`, which performs
  the final assembly.
* `norm_riemannZeta_le_strip` : **for `0 < re s ≤ 1` and `|im s| ≥ 3`,**

  `‖ζ(s)‖ ≤ (8 / re s) · |im s|^(1 - re s) · (1 + log |im s|)`.

## The argument

Write `σ = re s`, `t = |im s| ≥ 3`, `L = log t ≥ 1` (`one_le_log_of_three_le`), and truncate
the Euler–Maclaurin representation `ζ(s) = zetaApprox N s` of `M1-ZETA-CONTINUATION` at
`N = ⌈t⌉₊`, so that `t ≤ N < t + 1 ≤ 2t`. The three pieces are bounded separately.

* **Dirichlet sum.** For `n + 1 ≤ N` one has `(n+1)^(-σ) = (n+1)^(1-σ)(n+1)^(-1) ≤
  N^(1-σ)(n+1)^(-1)`, so `∑_{n<N} (n+1)^(-σ) ≤ N^(1-σ)(1 + log N)`. Since
  `N ≤ 2t` and `2^(1-σ) ≤ 2`, `N^(1-σ) ≤ 2 t^(1-σ)`, and `log N ≤ log 2 + log t ≤ 1 + L`.
  Total: `2 t^(1-σ) (2 + L)`.
* **Pole term.** `‖s - 1‖ ≥ |im s| = t`, and `(N+1)^(1-σ) ≤ (2t)^(1-σ) ≤ 2 t^(1-σ)`, so
  `‖(N+1)^(1-s)/(s-1)‖ ≤ 2 t^(1-σ)/t ≤ t^(1-σ)` (using `t ≥ 3 ≥ 2`).
* **Euler–Maclaurin tail.** `‖eulerTerm n s‖ ≤ ‖s‖ (n+1)^(-(1+σ))`, and
  `∑'_n (n+N+1)^(-(1+σ)) ≤ N^(-σ)/σ ≤ t^(-σ)/σ` by `tsum_shift_rpow_neg_le_rpow`. With
  `‖s‖ ≤ σ + t ≤ 1 + t` and `t^(-σ) · t = t^(1-σ)` this is at most
  `(1+t) t^(1-σ)/(σ t) ≤ (2/σ) t^(1-σ)`, the last step using `1 + t ≤ 2t`.

Adding and applying `strip_bound_arith` with `T = t^(1-σ)` gives
`(8/σ) t^(1-σ) (1 + L)`.

## Why it is a genuine improvement

`M1-STRIP-GROWTH` gives `‖ζ(σ + it)‖ ≤ C(σ)(1 + |t|)`, linear in `|t|` for every `σ`. The
bound here has exponent `1 - σ < 1`; at `σ = 1/2` it reads `16 √|t| (1 + log|t|)`, i.e.
`O(√|t| log|t|)`.

## Commands run

```
lake build                                  # success, 0 errors
lake build RiemannHypothesis.StripGrowth
bash scripts/audit.sh                       # OK
```

`#print axioms RiemannHypothesis.norm_riemannZeta_le_strip` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Not** the convexity bound `O(|t|^((1-σ)/2 + ε))` of the first exit criterion of
  `M1-GROWTH`; the exponent here is the trivial `1 - σ`, twice too large. Halving it needs
  the approximate functional equation (Euler–Maclaurin with Bernoulli polynomials) or
  Phragmén–Lindelöf applied to the functional equation, neither of which is available.
* Nothing at all for `|im s| < 3`, and nothing about `Re s ≤ 0`.
* Nothing about the Riemann hypothesis: a polynomial growth bound in the strip is
  compatible with zeroes off the critical line.
