# M1-HIGHER-MOMENTS — every even moment of `ζ` on a line of absolute convergence

Date: 2026-08-22
Module: `RiemannHypothesis/HigherMoments.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

`divisorCountK k n = (ζ^k) n`, the `k`-th convolution power of the constant-one arithmetic
function evaluated at `n` — the number of ordered factorizations of `n` into `k` factors
(`d_k(n)`; `d_0 = δ`, `d_1 = 1`, `d_2 = d` the divisor count, checked as
`divisorCountK_zero`, `divisorCountK_one`, `divisorCountK_two`).

* `natCoe_zeta_pow`, `divisorCountK_apply_complex`, `convolution_zeta_divisorCountK` — the
  recursion `d_{k+1} = 1 ⍟ d_k` at the level of `LSeries.convolution`.
* `lseriesSummable_divisorCountK` — for `re s > 1` the series `∑ d_k(n) n^(-s)` converges
  absolutely, by induction on `k` from `LSeriesSummable.convolution` (base case: the series of
  `δ` has a single nonzero term).
* `lseries_divisorCountK` — for `re s > 1`, `∑ d_k(n) n^(-s) = ζ(s)^k`, by induction from
  `LSeries_convolution'` and `LSeries_zeta_eq_riemannZeta` (base case `LSeries_delta`).
* `dirichletLineSum_divisorCountK`, `summable_dirichletWeight_divisorCountK` — the same series
  in the shifted indexing used by the mean value theorem.
* `momentAvg_tendsto_tsum_divisorCountK` — **all even moments**: for `σ > 1` and every `k`,

  `(1/T) ∫₀ᵀ |ζ(σ + i t)|^{2k} dt → ∑' n, d_k(n+1)² (n+1)^(-2σ)`  as `T → ∞`,

  by `meanSquareAvg_tendsto_tsum_of_summable` applied to the coefficients `d_k(n+1)`, using
  `‖ζ(s)^k‖² = ‖ζ(s)‖^{2k}`.

`k = 1` recovers the second moment of `RiemannHypothesis/MeanSquare.lean` and `k = 2` the
fourth moment of `RiemannHypothesis/FourthMoment.lean`.

## What is *not* proved

* Nothing about the critical strip: the moment conjectures, and even the proved cases
  `∫₀ᵀ |ζ(1/2 + i t)|² dt ∼ T log T` (Hardy–Littlewood) and
  `∫₀ᵀ |ζ(1/2 + i t)|⁴ dt ∼ T (log T)⁴/(2π²)` (Ingham), are not claimed.
* The limits are left as series; the closed forms `∑ d_k(n)² n^(-2σ)` (an Euler product) are
  not evaluated.
* Odd moments, and moments of `|ζ|` to non-even powers, are not covered: the method computes
  `‖ζ^k‖²` and needs the Dirichlet series of an integral power of `ζ`.

## Gates

* `lake build RiemannHypothesis.HigherMoments` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-HIGHER-MOMENTS

Re-checked by pinning, not by reading: `scripts/revalidation.lean` writes out the definition
of `divisorCountK` (by `rfl`), the identification `divisorCountK 2 n = #n.divisors`, the
identity `∑ d_k(n) n^(-s) = ζ(s)^k` for `re s > 1`, and the `2k`-th moment limit with the line
written out explicitly as `(σ : ℂ) + (t : ℂ) * I` and with the `2k`-th power of the modulus of
`ζ` itself, each discharged by the repository's declaration; a weakening or a renaming stops
the file elaborating.

Hidden-assumption check: the only hypothesis is `1 < σ` (resp. `1 < re s`), and it is
load-bearing for `k ≥ 1` — the series diverges otherwise. Vacuity check: the statement is
quantified over all `k`, and for `k ≥ 1` at `σ = 2` it is a genuine limit statement about a
non-constant function of `T` with a convergent positive limit; the degenerate case `k = 0`
merely says that the average of the constant `1` is `1`, and it is subsumed, not relied upon.
Non-circularity: the inputs are Mathlib's `LSeries` convolution theory and the mean value
theorem of `RiemannHypothesis/MeanSquare.lean`; nothing about the Riemann hypothesis is used
or produced.

Scope check: only the half-plane of absolute convergence; nothing about the critical strip and
nothing about the zeroes of `ζ` is claimed.
