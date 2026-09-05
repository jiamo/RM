# M2-LARGE-SIEVE-FAREY — the arithmetic large sieve

Date: 2026-08-30
File: `RiemannHypothesis/LargeSieveFarey.lean`

## Claim

Write `intDist θ = |θ − round θ|` for the distance to the nearest integer and `e(x)` for
`exp(2πi x)`.

* `one_div_den_le_abs` — a nonzero rational is at least `1 / den` in absolute value.

* `one_div_den_le_intDist` — a rational `x` that is not an integer satisfies
  `1 / x.den ≤ intDist x`.

* `inv_sq_le_intDist_sub` — **the separation of Farey fractions**: two distinct rationals
  `x ≠ y` in `[0, 1)` with `x.den ≤ Q` and `y.den ≤ Q` satisfy

      Q⁻² ≤ intDist (x − y).

* `large_sieve_farey` — for a finite set `s` of rationals in `[0, 1)` with denominators at most
  `Q` (and `Q ≥ 2`),

      ∑_{x ∈ s} ‖∑_{n < N} a n e(n x)‖² ≤ (Q² + π N) ∑_{n < N} ‖a n‖².

* `large_sieve_farey_pairs` — **the arithmetic large sieve** in its classical double-sum form:

      ∑_{q = 1}^{Q} ∑_{0 ≤ b < q, (b, q) = 1} ‖∑_{n < N} a n e(n b/q)‖²
        ≤ (Q² + π N) ∑_{n < N} ‖a n‖².

* `card_le_of_large_values_farey` — the counting form: the number of such fractions at which
  the exponential sum has modulus at least `V` is at most `(Q² + π N) ‖a‖² / V²`.

## Proof

The separation is arithmetic.  If `x ≠ y` both lie in `[0, 1)` then `0 < |x − y| < 1`, so `x − y`
is not an integer, its denominator is not `1`, and for the nearest integer `k` the rational
`x − y − k` is nonzero with denominator dividing `(x − y).den`.  A nonzero rational is at least
`1 / den` in absolute value (its numerator is at least `1` in absolute value), and
`(x − y).den ∣ x.den · y.den ≤ Q²` by `Rat.sub_den_dvd`; hence `intDist (x − y) ≥ Q⁻²`.

With `δ = Q⁻² ≤ 1/2` (which is where `Q ≥ 2` is used) the analytic large sieve in Gallagher's
form, `RiemannHypothesis.LargeSieveGallagher.large_sieve_gallagher`, applies verbatim to the
points `x ∈ s` viewed as reals, and `δ⁻¹ = Q²`.

For the double-sum form the index set of pairs `(q, b)` with `1 ≤ q ≤ Q`, `0 ≤ b < q` and
`(b, q) = 1` is identified with a set of rationals: a reduced fraction `b / q` has denominator
exactly `q` (`den_natCast_div`, from `Rat.den_div_eq_of_coprime`), so the images of distinct `q`
are disjoint, and within one `q` the map `b ↦ b / q` is injective.  The double sum is therefore
the sum over the union, which is a set of rationals in `[0, 1)` with denominators at most `Q`.

## Gates

* `lake build RiemannHypothesis.LargeSieveFarey` — succeeds, with no warnings.
* `#print axioms` on every statement above: exactly `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry` in the file; the statements are pinned in `scripts/revalidation.lean` and their
  axioms checked in `scripts/audit.sh`.

## Open boundary

The constant `Q² + π N` is not sharp: Selberg and Montgomery–Vaughan give `Q² + N − 1`, and the
factor `π` on `N` is inherited from the Sobolev step of `M2-LARGE-SIEVE-GALLAGHER`.  What is
proved is the large sieve for exponential sums at *rational points*; the multiplicative form for
Dirichlet characters needs Gauss sums and is not proved here, and neither is any consequence such
as the Bombieri–Vinogradov theorem.  Nothing about `ζ` follows: no mean value theorem is
improved, no zero-density estimate is obtained, and no zero is located.
