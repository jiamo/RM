# Evidence: the square-root bound for `ζ` on the imaginary axis (2026-08-20)

Rows: `M1-IMAGINARY-AXIS` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

### `RiemannHypothesis/ImaginaryAxis.lean`

* `norm_Gamma_one_sub_mul_I_sq` : for `t ≠ 0`,

  `‖Γ(1 − i t)‖² = π t / sinh(π t)`.

* `norm_cos_pi_one_sub_mul_I_div_two` : for every real `t`,

  `‖cos(π(1 − i t)/2)‖ = |sinh(π t / 2)|`.

* `norm_Gamma_mul_cos_le` : for `t ≠ 0`,

  `‖Γ(1 − i t)‖ · ‖cos(π(1 − i t)/2)‖ ≤ √(π |t| / 2)`.

* `norm_riemannZeta_mul_I_le` : **for `|t| ≥ 2`,**

  `‖ζ(i t)‖ ≤ √(|t| / 2π) · (6 + log(1 + |t|))`.

* `norm_riemannZeta_isBigO_imaginary_axis` :
  `(fun t => ‖ζ(i t)‖) =O[atTop] (fun t => √t · log t)`.

## The argument

The functional equation in the form proved in mathlib,
`ζ(1 − s) = 2 (2π)^(−s) Γ(s) cos(π s / 2) ζ(s)`, is applied at `s = 1 − i t`, so that
`1 − s = i t` lies on the imaginary axis and `s` lies on the line `re s = 1`, where this
repository already has the logarithmic bound `‖ζ(s)‖ ≤ 6 + log(1 + |im s|)`
(`RiemannHypothesis.norm_riemannZeta_le_log`, from `M1-EULER-MACLAURIN`).

The point of the file is that the modulus of the factor `Γ(s) cos(π s / 2)` is computed
*exactly*, not merely estimated by Stirling's formula (which mathlib does not provide in a
usable vertical-line form):

* Euler's reflection formula `Γ(z) Γ(1 − z) = π / sin(π z)` together with `Γ(z+1) = z Γ(z)`
  and `Γ(conj z) = conj (Γ z)` give `‖Γ(1 − i t)‖² = Γ(1 − i t) Γ(1 + i t) = π t / sinh(π t)`.
* `cos(π(1 − i t)/2) = cos(π/2 − i π t/2) = sin(i π t / 2)`, whose modulus is `|sinh(π t/2)|`.
* Multiplying, and using `sinh(π t) = 2 sinh(π t/2) cosh(π t/2)` and `cosh ≥ |sinh|`, the
  product is at most `√(π|t|/2)`; the remaining constant `2 (2π)^(−1)` converts this into
  `√(|t|/2π)`.

## Commands run

```
lake build RiemannHypothesis.ImaginaryAxis      # success, 0 errors
lake build                                      # success, 0 errors
bash scripts/audit.sh                           # OK
```

`#print axioms RiemannHypothesis.norm_riemannZeta_mul_I_le` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Adversarial revalidation: M1-IMAGINARY-AXIS

Second, independent pass.

* **Claim mode.** Every item is a `theorem` or `lemma` proved in this file; the statements
  are pinned verbatim in `scripts/revalidation.lean`, so a later weakening or renaming stops
  the audit from elaborating.
* **Non-vacuity.** The hypotheses `t ≠ 0` and `|t| ≥ 2` are load-bearing but satisfiable, and
  the conclusions are genuine upper bounds on a quantity that is not identically zero
  (`ζ(i t) ≠ 0` for large `|t|` is not claimed here, but `ζ` is certainly not the zero
  function). `norm_Gamma_one_sub_mul_I_sq` is an *equality*, so it cannot be vacuous.
* **Direction of the inequality.** The `√(|t|/2π)` factor grows, so the bound is weaker than
  the one on the line `re s = 1`; that is expected, and it matches the classical convexity
  value `1/2` of the exponent at `σ = 0`.
* **What is not claimed.** No lower bound for `‖ζ(i t)‖`, nothing for `|t| < 2`, and nothing
  about the location of zeroes: growth estimates on the boundary of the strip are consistent
  with the Riemann hypothesis being false.
