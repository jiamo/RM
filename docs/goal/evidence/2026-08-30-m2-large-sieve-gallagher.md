# M2-LARGE-SIEVE-GALLAGHER — the large sieve without a logarithm

Date: 2026-08-30
File: `RiemannHypothesis/LargeSieveGallagher.lean`

## Claim

Write `intDist θ = |θ − round θ|` for the distance to the nearest integer, `e(x)` for
`exp(2πi x)`, and `expPoly a N c θ = ∑_{n < N} a n e((n − c) θ)`.

* `integral_normSq_expPoly` — **Parseval over one period**:

      ∫₀¹ ‖expPoly a N c θ‖² dθ = ∑_{n < N} ‖a n‖²,

  for every real shift `c` of the frequencies (the frequencies `n − c` differ by integers, so the
  cross terms integrate to zero).

* `hasDerivAt_expPoly` — the derivative of `expPoly a N c` is `expPoly (derivCoeff a c) N c`, the
  exponential polynomial with coefficients `2π (n − c) i · a n`.

* `integral_normSq_deriv_le` — for the centred shift `c = (N − 1)/2`,

      ∫₀¹ ‖(expPoly a N c)′‖² ≤ (π N)² ∑_{n < N} ‖a n‖².

* `sum_normSq_le_of_separated_sharp` — **Gallagher's lemma**, in the form that keeps the cross
  term: for `δ`-separated points `t i` in `[A + δ/2, B − δ/2]`,

      δ ∑_i ‖f (t i)‖² ≤ ∫_A^B ‖f‖² + (δ/2) ∫_A^B 2 ‖f‖ ‖f′‖.

* `sum_normSq_expPoly_le`, `large_sieve_gallagher` — **the large sieve inequality with the
  constant `δ⁻¹ + π N`**: for points `t i` that are pairwise `δ`-separated modulo one
  (`δ ≤ 1/2`),

      ∑_i ‖∑_{n < N} a n e(n t i)‖² ≤ (δ⁻¹ + π N) ∑_{n < N} ‖a n‖².

* `card_le_of_large_values_gallagher` — the counting form: the number of such points at which the
  exponential sum has modulus at least `V` is at most `(δ⁻¹ + π N) ‖a‖² / V²`.

## Proof

The Sobolev step is the one-interval inequality already proved for `M2-DISCRETE-MEANVALUE`
(`Gallagher.mul_normSq_le_integral_of_mem_Icc`), applied to the two halves `[t i − δ/2, t i]` and
`[t i, t i + δ/2]` of the window around each point and added; this is what produces the factor
`δ/2` in front of the cross term, in place of the factor `δ` of the crude one-interval form.  The
windows around `δ`-separated points are disjoint, so `Gallagher.sum_integral_window_le` adds them
up to the integral over the enclosing interval.

For the exponential polynomial the two integrals are computed rather than estimated: Parseval
gives `∫₀¹ ‖f‖² = ∑ ‖a n‖²`, and, once the frequencies are centred at `c = (N − 1)/2`, the same
identity applied to the derivative gives `∫₀¹ ‖f′‖² ≤ (π N)² ∑ ‖a n‖²`, because `|n − c| ≤
(N − 1)/2` for `n < N`.  The cross term is then split by `2xy ≤ k x² + k⁻¹ y²` with the explicit
choice `k = π N`, which balances the two contributions exactly and yields `∫₀¹ 2 ‖f‖ ‖f′‖ ≤
2 π N ∑ ‖a n‖²` — the same value that Cauchy–Schwarz would give, without needing it.  Dividing
Gallagher's lemma by `δ` gives `δ⁻¹ + π N`.

Points that are separated modulo one are moved into the window `[δ/2, 1 − δ/2]` by translating by
a base point of the family and taking fractional parts: `v i = frac(t i − t i₀) + δ/2`.  The
translation multiplies the coefficients by unimodular constants, which changes neither the values
`‖∑_n a n e(n t i)‖` (periodicity, `e2pi_sub_int`) nor the right-hand side `∑ ‖a n‖²`; the
separation of the `v i` follows from `intDist_le_abs_sub_int`, and the same lemma applied to
`⌊t i − t i₀⌋` and `⌊t i − t i₀⌋ + 1` shows `δ ≤ frac(t i − t i₀) ≤ 1 − δ` for `i ≠ i₀`.

## Gates

* `lake build RiemannHypothesis.LargeSieveGallagher` — succeeds.
* `#print axioms` on every statement above: exactly `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry` in the file; the statements are pinned in `scripts/revalidation.lean` and their
  axioms checked in `scripts/audit.sh`.

## Open boundary

The constant is not sharp: Selberg and Montgomery–Vaughan prove the large sieve with `N + δ⁻¹`,
and the factor `π` on `N` is the cost of the Sobolev step.  Against the constant
`N + δ⁻¹(1 + log (2δ)⁻¹)` of `M2-LARGE-SIEVE` this row is an improvement in the `δ⁻¹` term — the
logarithm is gone — and a loss of the factor `π` in the `N` term; the two bounds are
incomparable, and a user may take the minimum of the two.  Both terms are necessary in some form:
`LargeSieve.le_of_admissibleConstant` shows that every admissible constant is at least
`max N (2δ)⁻¹`.  As in `M2-LARGE-SIEVE`, everything here is about exponential sums, not about `ζ`:
no mean value theorem for `ζ` is improved, no zero-density estimate follows and no zero is
located.
