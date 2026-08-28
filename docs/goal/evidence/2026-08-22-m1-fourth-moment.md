# M1-FOURTH-MOMENT — the fourth moment of `ζ` on a line of absolute convergence

Date: 2026-08-22
Module: `RiemannHypothesis/FourthMoment.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

`divisorCount n = #n.divisors` is the number of divisors of `n`, and

* `convolution_zeta_zeta_eq_divisorCount` — the Dirichlet convolution of the constant-one
  arithmetic function with itself is `divisorCount`: for every `n`,
  `(↗ζ ⍟ ↗ζ) n = d(n)` (both sides are `0` at `n = 0`, and for `n ≠ 0` every factor in the
  divisor antidiagonal is nonzero, so the sum counts the divisors).
* `lseriesSummable_divisorCount` — for `re s > 1` the Dirichlet series `∑ d(n) n^(-s)`
  converges absolutely, by `LSeriesSummable.convolution` applied to Mathlib's
  `LSeriesSummable_zeta_iff`.
* `lseries_divisorCount` — for `re s > 1`, `∑ d(n) n^(-s) = ζ(s)²`, by `LSeries_convolution'`
  together with `LSeries_zeta_eq_riemannZeta`.
* `summable_shift_rpow_of_lseriesSummable` — a bridge lemma: if `∑ aₙ n^(-s)` is
  `LSeriesSummable` at the *real* point `σ` with real coefficients `aₙ`, then
  `∑ a_{n+1} (n+1)^(-σ)` is summable as a real series (the `LSeries` terms at a real point are
  themselves real, so `Complex.summable_ofReal` transfers the summability).
* `dirichletLineSum_divisorCount` — for `σ > 1` the Dirichlet series with coefficients `d(n+1)`
  is `ζ²` on the line of real part `σ`.
* `fourthMomentAvg_tendsto_tsum_divisorCount` — **the fourth moment**: for `σ > 1`,

  `(1/T) ∫₀ᵀ |ζ(σ + i t)|⁴ dt → ∑' n, d(n+1)² (n+1)^(-2σ)`  as `T → ∞`,

  obtained from `meanSquareAvg_tendsto_tsum_of_summable` of `RiemannHypothesis/MeanSquare.lean`
  applied to the coefficients `d(n+1)`, using `‖ζ(s)²‖² = ‖ζ(s)‖⁴`.

## What is *not* proved

* Nothing about the critical strip. The Ingham fourth-moment asymptotic
  `∫₀ᵀ |ζ(1/2 + i t)|⁴ dt ~ T (log T)⁴ / (2π²)` is a different problem, needing the approximate
  functional equation, and is not claimed here.
* The limit is left as a series: the closed form `∑ d(n)² n^(-2σ) = ζ(2σ)⁴ / ζ(4σ)` is not
  proved.
* No consequence for the location of the zeroes is drawn: on the region covered `ζ` has no
  zeroes at all.

## Gates

* `lake build RiemannHypothesis.FourthMoment` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-FOURTH-MOMENT

Re-checked by pinning, not by reading: `scripts/revalidation.lean` writes out
`divisorCount n = #n.divisors` (by `rfl`), the identity `∑ d(n) n^(-s) = ζ(s)²` for
`re s > 1`, and the fourth-moment limit with the line written out explicitly as
`(σ : ℂ) + (t : ℂ) * I` and with the fourth power of the modulus of `ζ` itself (not of `ζ²`),
each discharged by the repository's declaration; a weakening or a renaming stops the file
elaborating.

Hidden-assumption check: the only hypothesis is `1 < σ` (resp. `1 < re s`), and it is
load-bearing — the divisor series diverges otherwise. Vacuity check: `σ = 2` satisfies the
hypothesis, the conclusion is a genuine limit statement about a non-constant function of `T`,
and the limit `∑ d(n+1)² (n+1)^(-2σ)` is a convergent series of positive terms, so nothing is
trivially true. Non-circularity: the input is Mathlib's convolution theory for `LSeries`
together with the mean value theorem of `RiemannHypothesis/MeanSquare.lean`; nothing about the
Riemann hypothesis is used or produced.

Scope check: only the half-plane of absolute convergence; nothing about the critical strip and
nothing about the zeroes of `ζ` is claimed.
