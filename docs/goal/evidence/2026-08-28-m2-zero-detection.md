# M2-ZERO-DETECTION — the Möbius mollifier identity

Date: 2026-08-28
File: `RiemannHypothesis/Mollifier.lean`

## Claim

Let `M_y(s) = ∑_{n ≤ y} μ(n) n^{−s}` be the Möbius mollifier of length `y`
(`RiemannHypothesis.Mollifier.mollifier`).  Multiplying the Dirichlet series of `ζ` by `M_y`
produces the coefficients `c_n = ∑_{d ∣ n, d ≤ y} μ(d)` (`detectCoeff`), and these vanish in the
initial range:

```lean
theorem detectCoeff_one {y : ℕ} (hy : 1 ≤ y) : detectCoeff y 1 = 1
theorem detectCoeff_eq_zero_of_le {y n : ℕ} (hn : 2 ≤ n) (hny : n ≤ y) : detectCoeff y n = 0
```

Hence the mollifier identity, in the half-plane of absolute convergence:

```lean
theorem zeta_mul_mollifier_eq_one_add_tail {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mollifier y s = 1 + LSeries (tailCoeff y) s
```

where `tailCoeff y n = c_n` for `n > y` and `0` otherwise.  Equivalently
`LSeries (tailCoeff y) s = ζ(s) M_y(s) − 1` (`LSeries_tailCoeff_eq`), so at a zero of `ζ` the tail
Dirichlet series — which has *no short terms* — takes the value `−1`.

The same mechanism is also recorded in a purely finite form, with no convergence hypothesis, so
that it holds for **every** complex `s`:

```lean
theorem mollified_partialSum (y K : ℕ) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 y, (μ d : ℂ) * (d : ℂ) ^ (-s)) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = ∑ m ∈ Finset.Icc 1 (y * K), finiteDetectCoeff y K m * (m : ℂ) ^ (-s)

theorem mollified_partialSum_eq_one_add_tail {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 y, (μ d : ℂ) * (d : ℂ) ^ (-s)) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = 1 + ∑ m ∈ Finset.Ioc y (y * K), finiteDetectCoeff y K m * (m : ℂ) ^ (-s)
```

with `finiteDetectCoeff y K m = ∑_{d ∣ m, d ≤ y, m/d ≤ K} μ(d)`, which vanishes for
`2 ≤ m ≤ min y K` (`finiteDetectCoeff_eq_zero_of_le`) and equals `1` at `m = 1`.

## Proof

The coefficient identity is `((1 : ℕ → ℂ) ⍟ mollCoeff y) n = detectCoeff y n`
(`convolution_one_mollCoeff`), obtained from `LSeries.convolution_def`,
`Nat.sum_divisorsAntidiagonal` and `Nat.sum_div_divisors`.  Combined with
`LSeries_convolution'`, `LSeriesSummable_one_iff` and `LSeries_one_eq_riemannZeta` this gives
`ζ(s) M_y(s) = LSeries (detectCoeff y) s` for `re s > 1`.  The vanishing
`detectCoeff_eq_zero_of_le` is the repository's `sum_divisors_moebius`
(`∑_{d ∣ n} μ(d) = [n = 1]`, from `RiemannHypothesis/MertensSums.lean`): for `n ≤ y` every divisor
of `n` is at most `y`, so the truncated divisor sum is the full one.  Splitting
`detectCoeff = δ + tailCoeff` and using `LSeries_delta = 1` gives the identity.

The finite identity is the same combinatorics without any analysis: the product of the two finite
sums is a sum over `Icc 1 y ×ˢ Icc 1 K`, `(d k)^{−s} = d^{−s} k^{−s}` for natural `d, k`
(`natCast_mul_cpow_neg`, via `Complex.mul_cpow_ofReal_nonneg`), and
`Finset.sum_fiberwise_of_maps_to` groups the pairs by their product `m`.  The fibre over `m` is in
bijection with the admissible divisors of `m` by `(d, k) ↦ d`, with inverse `d ↦ (d, m/d)`
(`sum_moebius_fiber_eq`).

## Scope

This is the *third* step of the density chain (large sieve → large values → zero detection →
assembly), and only that step.  Explicitly:

* The infinite identity is proved for `re s > 1`, where `ζ` has no zeroes.  It therefore detects
  no zero on its own; carrying it into the critical strip, where it is applied, needs the infinite
  tail to be replaced by a finite Dirichlet polynomial with an explicit error term (an approximate
  functional equation or a contour shift), and neither is available in this repository.
* The finite identity holds for every `s`, but it is an identity between finite sums and says
  nothing about `ζ` outside the region of convergence: relating
  `∑_{k ≤ K} k^{−s}` to `ζ(s)` in the strip is again the missing analytic input.
* No mollified mean value, no large-value bound for the tail, and no zero-density estimate is
  claimed here.  In particular this row does *not* close M2-MOLLIFIER, which asks for a mollified
  first moment of `ζ` on the critical line.

## Gates

* `lake build RiemannHypothesis.Mollifier` succeeds; the module contains no `sorry` and is
  imported by the root `RiemannHypothesis.lean`.
* `#print axioms` on the identities gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
