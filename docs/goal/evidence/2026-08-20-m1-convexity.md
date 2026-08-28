# Evidence: the Phragmén–Lindelöf convexity bound for `ζ` in the strip (2026-08-20)

Rows: `M1-CONVEXITY` (new, `DONE_STRONG`), `M1-GROWTH` (still `DONE_WEAK`, boundary rewritten).

## What is proved (without `sorry`)

### `RiemannHypothesis/Convexity.lean`

* `norm_Gamma_le_Gamma_re` : `‖Γ(s)‖ ≤ Γ(re s)` for `0 < re s`, directly from Euler's integral.
* `Gamma_le_one_of_mem_Icc`, `Gamma_le_two_of_mem_Icc` : `Γ ≤ 1` on `[1,2]` and `Γ ≤ 2` on
  `[1/2,1]`, from log-convexity of `Γ` and `Γ(x) = Γ(x+1)/x`.
* `norm_riemannZeta_le_sixteen` : `‖ζ(s)‖ ≤ 16 |t|²` for `1/2 ≤ re s ≤ 1`, `|t| ≥ 3`.
* `norm_riemannZeta_le_exp_strip` : the crude bound `‖ζ(s)‖ ≤ 100 e^(π|t|/2) |t|²` on the
  whole closed strip `0 ≤ re s ≤ 1`, `|t| ≥ 3`.
* `norm_riemannZeta_le_boundary` : on either edge of the strip,
  `‖ζ(s)‖ ≤ |t|^((1−σ)/2) (6 + log(1 + |t|))`.
* **`norm_riemannZeta_le_convexity`** : for every `ε ∈ (0,1]` there is `C > 0` with

  `‖ζ(s)‖ ≤ C |im s| ^ ((1 − re s)/2 + ε)`   for `0 ≤ re s ≤ 1`, `|im s| ≥ 3`.

* **`norm_riemannZeta_le_critical_line`** : the case `σ = 1/2`, i.e. for every `ε ∈ (0,1]`
  there is `C > 0` with `‖ζ(1/2 + i t)‖ ≤ C |t|^(1/4 + ε)` for `|t| ≥ 3`.

## The argument

Phragmén–Lindelöf (`PhragmenLindelof.vertical_strip`) is applied to

`g(s) = ((s − 1)/(s + 3))² · ζ(s) · exp(−w(s) · log u(s))`,
`u(s) = s(1 − s) + 4`,  `w(s) = (1 − s)/4 + ε/2`.

* **Analyticity.** On the closed strip `re u = σ(1−σ) + t² + 4 ≥ 4 > 0`, so `u` never leaves
  the slit plane and the principal `log u` is analytic there; `expAux` is therefore entire on
  the strip. The square of `(s−1)/(s+3)` cancels the simple pole of `ζ` at `s = 1`: the
  product is genuinely continuous there (value `0`, limit `0` via `riemannZeta_residue_one`),
  so `DiffContOnCl` holds without any `Function.update` surgery.
* **Modulus of the interpolating factor.** `‖expAux‖ = exp(−((1−σ)/4 + ε/2) log‖u‖ − (t/4) arg u)`.
  The argument is controlled by `|arg u| ≤ (π/2)|t|/‖u‖` (from `Real.mul_le_sin` and
  `Complex.sin_arg`), whence the `arg` contribution is at most `π/8` in absolute value; and
  `t² + 4 ≤ ‖u‖ ≤ 2t²` for `|t| ≥ 3`. This gives the two-sided estimate

  `e^(−π/8)/2 · |t|^(−((1−σ)/2+ε)) ≤ ‖expAux‖ ≤ e^(π/8) · |t|^(−((1−σ)/2+ε))`.

* **Boundary.** On `re s = 1` the logarithmic bound `6 + log(1 + |t|)` of `M1-EULER-MACLAURIN`
  is used; on `re s = 0` the square-root bound of `M1-IMAGINARY-AXIS`. Multiplied by
  `‖expAux‖`, both give `≤ e^(π/8)(6 + log(1+|t|))|t|^(−ε) ≤ e^(π/8)(6 + 2/ε)`, using
  `log x ≤ x^ε/ε`. The remaining part of the two edges, `|t| ≤ 3`, is compact and `g` is
  continuous there, so it contributes only another finite constant.
* **Growth hypothesis.** The crude bound `‖ζ‖ ≤ 100 e^(π|t|/2)|t|²` plus
  `‖expAux‖ ≤ e^(π|t|/4)` gives `‖g‖ ≤ 100 e^(3π|t|/4)|t|² ≤ 100 exp(5 e^(|t|))`, which is of
  the required doubly-exponential shape with `c = 1 < π`.
* **Unwinding.** Phragmén–Lindelöf gives `‖g‖ ≤ C` on the whole closed strip. Since
  `‖((s−1)/(s+3))²‖ ≥ 9/25` for `|t| ≥ 3`, dividing by the lower bound for `‖expAux‖` yields
  `‖ζ(s)‖ ≤ C' |t|^((1−σ)/2 + ε)`.

The crude bound itself is proved by cases: for `1/2 ≤ σ` it is the trivial bound of
`M1-STRIP-TRIVIAL-BOUND`, and for `σ ≤ 1/2` it is the functional equation applied at `1 − s`,
with `‖(2π)^(−(1−s))‖ ≤ 1`, `‖Γ(1−s)‖ ≤ Γ(1−σ) ≤ 2` and `‖cos(π(1−s)/2)‖ ≤ e^(π|t|/2)`.

## Why it is a genuine improvement

`M1-STRIP-TRIVIAL-BOUND` gives the exponent `1 − σ`; the exponent here is `(1 − σ)/2 + ε`,
half of it up to `ε`. At `σ = 1/2` the bound is `O(|t|^(1/4+ε))`, the classical convexity
bound, instead of `O(√|t| log|t|)`.

## Commands run

```
lake build RiemannHypothesis.Convexity          # success, 0 errors, no sorry
lake build                                      # success, 0 errors
bash scripts/audit.sh                           # OK
```

`#print axioms RiemannHypothesis.norm_riemannZeta_le_convexity` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Adversarial revalidation: M1-CONVEXITY

Second, independent pass.

* **Claim mode.** `norm_riemannZeta_le_convexity` and `norm_riemannZeta_le_critical_line` are
  `theorem`s with no hypotheses beyond `0 < ε ≤ 1`; the auxiliary objects `uAux`, `wAux`,
  `expAux`, `gAux` are `def`s, and the statements of the main theorems mention none of them.
  Both statements are pinned verbatim in `scripts/revalidation.lean`.
* **Non-vacuity.** The conclusion is an upper bound quantified over a non-empty set of points
  (every `s` with `0 ≤ re s ≤ 1`, `|im s| ≥ 3`), and the constant is asserted positive, so the
  statement cannot be satisfied by a degenerate `C`. The existential is over `C` only: the
  bound is uniform in `s`, which is the content.
* **The ε is real.** The bound is *not* the ε-free `O(|t|^((1−σ)/2))`; this is the usual
  convexity bound and the ε cannot be removed by this method. That is recorded in the open
  boundary of `M1-GROWTH`.
* **Where the classical input sits.** The only two analytic inputs are the two boundary
  bounds, both proved in this repository (`M1-EULER-MACLAURIN`, `M1-IMAGINARY-AXIS`); the
  interpolation itself is mathlib's `PhragmenLindelof.vertical_strip`. No unproved growth
  assumption is smuggled in: the doubly-exponential hypothesis is discharged from the crude
  bound proved in the same file.
* **No consequence for the hypothesis.** A polynomial growth bound in the strip is compatible
  with zeroes off the critical line; nothing here bears on `ZetaForm`.
