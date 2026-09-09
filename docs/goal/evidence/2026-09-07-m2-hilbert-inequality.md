# Hilbert's inequality with the constant `π`

Date: 2026-09-07
Module: `RiemannHypothesis/HilbertInequality.lean`

## Why

Several rows of the board record the same gap: the mean value theorem for exponential sums with
well-spaced frequencies is proved here by the Gaussian majorant method, with the constant
`18 (T + 1/δ)`, because Montgomery and Vaughan's generalized Hilbert inequality — the estimate
that yields the sharp constants — is not formalized.  This row attacks that inequality and
proves its discrete core.

## What is proved

* `trigSum` — the exponential sum `f(θ) = ∑_r x_r e^{i k_r θ}` with integer frequencies.
* `integral_exp_int_mul` — `∫₀^{2π} e^{i m θ} dθ = 2π` for `m = 0` and `0` otherwise.
* `integral_sawtooth_exp` — `∫₀^{2π} (π − θ) e^{i m θ} dθ = 2π i / m` for `m ≠ 0`, and `0` for
  `m = 0`: the Fourier coefficients of the sawtooth are exactly the reciprocals `1/m`.
* `trigSum_mul_conj`, `integral_normSq_trigSum` — the expansion of `|f|²` and Parseval,
  `∫₀^{2π} |f|² = 2π ∑ |x_r|²`, where the distinctness of the frequencies is used.
* `integral_sawtooth_normSq_trigSum` — the identity
  `∫₀^{2π} (π − θ) |f(θ)|² dθ = 2π i ∑_{r ≠ s} x_r conj(x_s)/(k_r − k_s)`.
* `hilbert_inequality` — **Hilbert's inequality**: for distinct integers `k_r`,
  `‖∑_{r ≠ s} x_r conj(x_s)/(k_r − k_s)‖ ≤ π ∑_r ‖x_r‖²`.
* `hilbert_inequality_lattice` — for `λ_r = δ k_r`, which are `δ`-separated, the same with the
  constant `π/δ`: the Montgomery–Vaughan bound in the lattice case.
* `GeneralizedHilbertInequality` — the general Montgomery–Vaughan theorem, recorded as a `Prop`
  and **not** proved, with the four hypothesis-hygiene answers in its docstring.
* `generalizedHilbert_of_lattice` — the instance of that statement which is proved here.

## Proof

Let `g(θ) = π − θ` on `(0, 2π)`.  An explicit antiderivative, `e^{imθ}(A(π−θ) + A²)` with
`A = 1/(im)`, gives `ĝ(m) = 1/m`; the diagonal coefficient `ĝ(0)` vanishes because `g` has mean
zero.  Expanding `|f|²` and integrating term by term therefore produces the Hilbert form,
multiplied by `2π i`.  Since `|π − θ| ≤ π` on `[0, 2π]`, the left side is at most
`π ∫₀^{2π}|f|² = 2π² ∑ |x_r|²`, and dividing by `2π` gives the inequality.  The lattice form is
the substitution `λ_r = δ k_r`, which multiplies the form by `1/δ`.

## Scope

Only the lattice case.  The general theorem, for an arbitrary `δ`-separated family of *real*
frequencies, is strictly stronger and is not proved: the argument above needs the characters to
be orthogonal on a fixed period, which is exactly what a common lattice provides, and the
extremal problem that replaces it in general is the content of Montgomery and Vaughan's theorem.
The optimality of the constant `π` is classical but is not proved here.  Nothing in the
repository is made conditional on the general statement: `MeanValueWellSpaced` remains
unconditional, with its own (worse) constant, and is not improved by this row.

## Adversarial review

* *Is the inequality vacuous for small families?*  No.  For `S` a singleton both sides are
  meaningful (`0 ≤ π‖x‖²`), and for `k_r = r` over `S = {0, 1}` the left side is
  `‖x₀ conj(x₁) − x₁ conj(x₀)‖`, which is genuinely bounded by the right side and not zero in
  general.
* *Is the distinctness hypothesis load-bearing?*  Yes, twice: Parseval fails without it, and the
  sum over `r ≠ s` would divide by zero.  It enters as `Set.InjOn k S`.
* *Does the lattice corollary secretly assume separation it does not have?*  The frequencies
  `δ k_r` with `k_r` distinct integers satisfy `|λ_r − λ_s| ≥ δ`; that is a consequence, not an
  assumption, and it is what makes the corollary an instance of the Montgomery–Vaughan
  statement (`generalizedHilbert_of_lattice`).
* *Axioms.*  `#print axioms` on the two pinned statements gives exactly `propext`,
  `Classical.choice`, `Quot.sound`.
