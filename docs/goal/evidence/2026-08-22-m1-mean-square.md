# M1-MEAN-SQUARE — the second moment on a line of absolute convergence

Date: 2026-08-22
Module: `RiemannHypothesis/MeanSquare.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

The computation is carried out once, for a general Dirichlet series
`D(s) = ∑ aₙ (n+1)^(-s)` (`dirichletLineSum`), with weights
`dirichletWeight A σ n = ‖aₙ‖ (n+1)^(-σ)`:

* `normSq_dirichletLineSum_eq_tsum` — the pointwise expansion

  `|D(σ + i t)|² = ∑_{(m,n)} aₘ conj(aₙ) ((m+1)(n+1))^(-σ) · e^{i t log((n+1)/(m+1))}`,

  an absolutely convergent double series, obtained by multiplying the series by the conjugate
  of itself (`tsum_mul_tsum_of_summable_norm`).
* `oscIntegral`, `norm_oscIntegral_le`, `norm_oscIntegral_le_two_div`, `oscAvg_tendsto_zero` —
  the oscillatory integral `∫₀ᵀ e^{i θ t} dt` is bounded by `T` always, and by `2/|θ|`
  uniformly in `T` when `θ ≠ 0`; hence its average over `[0, T]` tends to `0`.
* `integral_normSq_dirichletLineSum` — termwise integration of the expansion over `[0, T]`,
  justified by `integral_tsum_of_summable_integral_norm` (each term has constant modulus).
* `meanSquareAvg_tendsto_tsum_of_summable` — **the mean value theorem**: if
  `∑ ‖aₙ‖ (n+1)^(-σ)` converges then

  `(1/T) ∫₀ᵀ |D(σ + i t)|² dt → ∑' n, (‖aₙ‖ (n+1)^(-σ))²`  as `T → ∞`,

  by Tannery's theorem (`tendsto_tsum_of_dominated_convergence`): the diagonal terms `m = n`
  have frequency `0` and average `1`, every off-diagonal term has nonzero frequency and
  average tending to `0` (`tsum_diagonal_eq` collects the diagonal).

Specializations:

* `meanSquareAvg_tendsto_tsum`, `meanSquareAvg_tendsto_riemannZeta` — for `aₙ = 1` and
  `σ > 1`, `(1/T) ∫₀ᵀ |ζ(σ + i t)|² dt → ∑' n, (n+1)^(-2σ) = ζ(2σ)` (the limit is written as
  the real part of `ζ(2σ)`, which is real because `2σ > 1`); `riemannZeta_ofReal_eq_tsum`
  identifies the two forms.
* `dirichletLineSum_moebius`, `meanSquareAvg_tendsto_tsum_moebius` — for `aₙ = μ(n+1)` the
  series is `1/ζ` on the line (from Mathlib's `L ↗ζ s * L ↗μ s = 1`), so
  `(1/T) ∫₀ᵀ |1/ζ(σ + i t)|² dt → ∑' n, μ(n)² n^(-2σ)` for `σ > 1`.
  `lseries_eq_dirichletLineSum` is the bridge between Mathlib's `LSeries` indexing and the
  shifted indexing used here.

## What is *not* proved

* Nothing about the critical strip. For `1/2 < σ ≤ 1` the Dirichlet series no longer converges
  and the same computation needs the Euler–Maclaurin approximation together with a mean-value
  theorem for Dirichlet polynomials; the Hardy–Littlewood asymptotic
  `∫₀ᵀ |ζ(1/2 + i t)|² dt ~ T log T` is further out still.
* No consequence for the location of the zeroes is drawn here: the region covered is one where
  `ζ` has no zeroes at all.
* The limits are left as series; they are not evaluated in closed form (for instance
  `∑ μ(n)² n^(-2σ) = ζ(2σ)/ζ(4σ)` is not proved).

## Gates

* `lake build RiemannHypothesis.MeanSquare` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-MEAN-SQUARE

Re-checked by pinning, not by reading: `scripts/revalidation.lean` writes out
`linePoint σ t = σ + i t`, the unfoldings of `dirichletLineSum` and `dirichletWeight` (all by
`rfl`), the oscillation limit, the double-series expansion of `|ζ(σ + i t)|²`, the general
mean value theorem, and both specializations — the `ζ` one and the `1/ζ` one — with the line
written out explicitly as `(σ : ℂ) + (t : ℂ) * I`, each discharged by the repository's
declaration; a weakening or a renaming stops the file elaborating.

Hidden-assumption check: the general theorem assumes exactly the absolute convergence of the
coefficient series, which is what makes the double series converge; the specializations assume
only `1 < σ`, and both use it (for `ζ` the series diverges otherwise, and `1/ζ` is not even
given by the Möbius series). Vacuity check: the hypotheses are satisfiable (`σ = 2`), the
conclusions are genuine limit statements about non-constant functions of `T`, and the limit
values are positive, so nothing here is trivially true.

Scope check: nothing about the critical strip, and nothing about the zeroes of `ζ`, is
claimed.
