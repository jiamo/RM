# Evidence: the Euler–Maclaurin continuation, the logarithmic bound near the line, and a zero-free region with exponent 9 (2026-08-20)

Rows: `M1-ZETA-CONTINUATION`, `M1-NEARLINE-LOG-BOUND`, `M1-ZERO-FREE-REGION-NINTH`.

## What is proved (all without `sorry`)

### `RiemannHypothesis/Continuation.lean`

* `differentiableAt_eulerTerm` : each `eulerTerm n` is differentiable away from `s = 1`.
* `differentiableOn_tsum_eulerTerm` : the Euler–Maclaurin tail `∑' n, eulerTerm (n+N) s` is
  differentiable on `{s | 0 < re s} \ {1}` (locally uniform convergence of the series of
  analytic terms, via `differentiableOn_tsum_of_summable_norm` and the bound
  `‖eulerTerm n s‖ ≤ ‖s‖ (n+1)^(-(1+re s))`).
* `analyticOnNhd_zetaApprox` : `zetaApprox N` is analytic on `{s | 0 < re s} \ {1}`.
* `riemannZeta_eq_zetaApprox_of_pos_re` : **`ζ(s) = zetaApprox N s` for `0 < re s`, `s ≠ 1`
  and every `N`** — the identity of `M1-EULER-MACLAURIN`, extended from `1 < re s` to the
  whole punctured right half-plane by the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, with preconnectedness supplied by
  `isPreconnected_punctured_halfPlane` from `M0-CONNECTED`).

### `RiemannHypothesis/NearLine.lean`

* `tsum_shift_rpow_neg_le_rpow` : `∑' n, (n+N+1)^(-p) ≤ N^(1-p)/(p-1)` for `1 < p`, `1 ≤ N`,
  by comparison with `∫ x^(-p)` (`AntitoneOn.sum_le_integral`).  The tail bound already in
  the repository needed `p ≥ 2`, which is not available to the left of the line.
* `norm_riemannZeta_le_log_near_line` : **for `|t| ≥ 3` and `1 - 1/(2 log|t|) ≤ re s ≤ 2`,
  `‖ζ(s)‖ ≤ 18 log|t|`.**

  With `σ = re s < 1`, `N = ⌈|t|⌉₊` the three pieces of `zetaApprox N s` are bounded by
  `N^(1-σ)(1 + log N) ≤ 3 + 6 log|t|`, `(N+1)^(1-σ)/‖s-1‖ ≤ 3/|t| ≤ 1`, and
  `‖s‖ · N^(-σ)/σ ≤ (1+|t|)(3/|t|)/(1/2) ≤ 8`; the total is `12 + 6 log|t| ≤ 18 log|t|`.
  The width `1/(2 log|t|)` of the region is what makes `N^(1-σ) ≤ e ≤ 3`.
  For `1 ≤ re s ≤ 2` the bound is the earlier `6 + log(1+|t|)` of `M1-EULER-MACLAURIN`.

### `RiemannHypothesis/ZeroFreeRegion.lean`

* `norm_deriv_riemannZeta_le_near_line` : **`‖ζ'(s)‖ ≤ 288 (log|t|)²` for `|t| ≥ 4` and
  `1 - 1/(8 log|t|) ≤ re s ≤ 5/4`.**  Cauchy's estimate
  (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) on the disc of radius
  `r = 1/(8 log|t|)`: every point `w` of that disc satisfies `|im w| ≥ 3`,
  `log|im w| ≤ 2 log|t|` and `re w ≥ 1 - 1/(2 log|im w|)`, so `‖ζ(w)‖ ≤ 36 log|t|`, and
  `36 log|t| / r = 288 (log|t|)²`.
* `norm_riemannZeta_le_of_zero` : the mean value inequality along the horizontal segment
  from a hypothetical zero `s` to `1 + x + i·im s`.
* `riemannZeta_ne_zero_of_near_one` : **`ζ(s) ≠ 0` whenever `|im s| ≥ 4` and
  `re s > 1 - 2^(-45)/(log|im s|)^9`**, and its existential form `zeroFreeRegionNinth`
  (`ZeroFreeRegionNinth`, the statement with `(log|t|)^9` in place of `log|t|`).

  Combination: with `L = log|im s|`, `x = 2^(-45)/L^9` and a hypothetical zero at `s`,
  the mean value inequality gives `‖ζ(1+x+i·im s)‖ ≤ 288 L² (1 + x - re s) ≤ 576 L² x`,
  while the Mertens `3-4-1` bound of `M1-ZETA-LOWER-BOUND` gives
  `‖ζ(1+x+i·im s)‖⁴ ≥ x³/(8(6+log(1+2|im s|))) ≥ x³/(64 L)`.  Hence
  `1 ≤ 64 · 576⁴ · L⁹ · x = 64 · 576⁴ · 2^(-45) ≈ 0.20`, a contradiction.
  `re s ≥ 1` is covered by mathlib's `riemannZeta_ne_zero_of_one_le_re`.

## Commands run

```
lake build                      # success, 0 errors; only Challenge.lean has `sorry`
lake build RiemannHypothesis.Continuation
lake build RiemannHypothesis.NearLine
lake build RiemannHypothesis.ZeroFreeRegion
./scripts/audit.sh              # OK
```

`#print axioms` for `riemannZeta_eq_zetaApprox_of_pos_re`,
`norm_riemannZeta_le_log_near_line`, `norm_deriv_riemannZeta_le_near_line`,
`riemannZeta_ne_zero_of_near_one` and `zeroFreeRegionNinth` each reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Not** the classical de la Vallée Poussin region `re s > 1 - c/log|t|`
  (`RiemannHypothesis.ZeroFreeRegion` in `RiemannHypothesis/Partial.lean` remains an
  unproved `Prop`).  The exponent here is `9`, not `1`.  The loss has two identified
  sources: the derivative bound `O((log|t|)²)` costs one power of `log`, and the fourth
  root of the `3-4-1` lower bound costs the rest.  Removing it needs the Landau /
  Borel–Carathéodory estimate for `ζ'/ζ` on a disc, which is in neither mathlib nor this
  repository.
* Nothing about the zeroes with `|im s| < 4`, and nothing about the Riemann hypothesis
  itself: the region proved here has width tending to `0`, and every known zero-free region
  of this shape is compatible with the conjecture being false.
