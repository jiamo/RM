# Evidence: the convexity bound without an `ε` (2026-08-20)

Rows: `M1-CONVEXITY-LOG` (new, `DONE_STRONG`), `M1-GROWTH` (still `DONE_WEAK`).

## What is proved (without `sorry`)

### `RiemannHypothesis/ConvexityLog.lean`

* `logAux s = log(s(1 − s) + 4)`, `hAux s = gAux 0 s / logAux s` (definitions).
* `norm_logAux_ge` : `log 4 ≤ ‖log u(s)‖` on the closed strip, and `logAux_ne_zero`.
* `norm_logAux_le` : `‖log u(s)‖ ≤ 3(1 + log|t|)` for `|t| ≥ 3`.
* `norm_hAux_le_boundary_large` : `‖h(s)‖ ≤ 4 e^(π/8)` on the two edges at height `|t| ≥ 3`.
* **`norm_riemannZeta_le_convexity_log`** : there is `C > 0` with

  `‖ζ(s)‖ ≤ C (1 + log|im s|) |im s| ^ ((1 − re s)/2)`   for `0 ≤ re s ≤ 1`, `|im s| ≥ 3`.

* **`norm_riemannZeta_le_critical_line_log`** : `‖ζ(1/2 + i t)‖ ≤ C (1 + log|t|) |t|^(1/4)`
  for `|t| ≥ 3`.

## The argument

This is the Phragmén–Lindelöf apparatus of `M1-CONVEXITY` run at `ε = 0` — the interpolating
factor is `exp(−((1 − s)/4) log u(s))`, `u(s) = s(1 − s) + 4` — with one extra division, by
the analytic function `log u(s)` itself.

* On the closed strip `re u ≥ s.im² + 4 ≥ 4`, so `log u` is analytic there and
  `‖log u‖ ≥ Re log u = log‖u‖ ≥ log 4 > 1`. Dividing by it therefore cannot spoil the
  doubly-exponential growth hypothesis of Phragmén–Lindelöf: `‖h‖ ≤ ‖g₀‖` pointwise on the
  strip, and `g₀` was already handled in `M1-CONVEXITY`.
* On either edge, the numerator obeys `‖g₀(s)‖ ≤ e^(π/8)(6 + log(1 + |t|))` — the boundary
  bounds of `M1-EULER-MACLAURIN` and `M1-IMAGINARY-AXIS` multiplied by the modulus of the
  interpolating factor — while `‖log u‖ ≥ log‖u‖ ≥ log(t²) = 2 log|t|`. Since `log|t| > 1`
  for `|t| ≥ 3`, the quotient is at most `4 e^(π/8)`: a *constant*, with the boundary
  logarithm absorbed. The remaining compact part `|t| ≤ 3` of the two edges is bounded by
  continuity.
* Phragmén–Lindelöf therefore gives `‖h‖ ≤ C` on the closed strip, i.e.
  `‖g₀(s)‖ ≤ C ‖log u(s)‖ ≤ 3C(1 + log|t|)`, and unwinding `g₀` exactly as in `M1-CONVEXITY`
  (the rational factor is `≥ 9/25` and the interpolating factor is
  `≥ e^(−π/8)/2 · |t|^(−(1−σ)/2)`) yields the stated bound.

## Why it is a genuine improvement

`M1-CONVEXITY` gives `C_ε |t|^((1−σ)/2+ε)` for each `ε > 0`, with a constant that blows up as
`ε → 0`. The bound here has the exact convexity exponent `(1 − σ)/2` and only a logarithmic
loss, with a single absolute constant; at `σ = 1/2` it is `O(|t|^(1/4) log|t|)`, the classical
statement.

## Commands run

```
lake build RiemannHypothesis.ConvexityLog       # success, 0 errors, no sorry
lake build                                      # success, 0 errors
bash scripts/audit.sh                           # OK
```

`#print axioms RiemannHypothesis.norm_riemannZeta_le_convexity_log` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Adversarial revalidation: M1-CONVEXITY-LOG

Second, independent pass.

* **Claim mode.** Both main statements are `theorem`s whose statements mention only `ζ`, and
  they are pinned verbatim in `scripts/revalidation.lean`.
* **Non-vacuity.** The bound is asserted for every `s` in a non-empty region and the constant
  is asserted positive; nothing is hidden in an unsatisfiable hypothesis. The auxiliary
  division is legitimate: `logAux_ne_zero` is proved on the whole closed strip, so `hAux` is
  not a quotient by something that could vanish.
* **The logarithm is still there.** This is *not* the bound `O(|t|^((1−σ)/2))` demanded
  literally by the first exit criterion of `M1-GROWTH`; that row stays `DONE_WEAK`. Removing
  the logarithm needs a genuinely different method (van der Corput / approximate functional
  equation).
* **Consistency check.** At `σ = 1` the bound reads `C(1 + log|t|)`, which agrees with the
  independently proved `M1-EULER-MACLAURIN` bound `6 + log(1 + |t|)` up to constants; at
  `σ = 0` it reads `C(1 + log|t|)|t|^(1/2)`, agreeing with `M1-IMAGINARY-AXIS`. So the
  interpolation does not claim more at the edges than what went in.
* **No consequence for the hypothesis.** Growth bounds in the strip say nothing about the
  location of the zeroes.
