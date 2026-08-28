# M1-ZETA-CHI-AFE — the `χ` factor of the functional equation, and the approximate functional equation as a statement

Date: 2026-08-27
Files: `RiemannHypothesis/SqrtHarmonic.lean`, `RiemannHypothesis/ZetaChi.lean`,
`RiemannHypothesis/ApproximateFunctionalEquation.lean`

## Claim

Unconditional:

* `sum_one_div_sqrt_le` — `∑_{1 ≤ n ≤ N} 1/√n ≤ 2 √N`;
* `sum_sqrt_le` — `∑_{n < N} √n ≤ N √N`;
* `zetaChi s = 2 (2π)^(s−1) Γ(1−s) sin(πs/2)`, and
  `riemannZeta_eq_zetaChi_mul` — `ζ(s) = χ(s) ζ(1−s)` away from the poles;
* `zetaChi_conj` — `χ(s̄) = conj (χ s)`;
* `zetaChi_mul_zetaChi_one_sub` — `χ(s) χ(1−s) = 1` when `sin(πs) ≠ 0`;
* `norm_zetaChi_criticalLine` — **`‖χ(1/2 + i t)‖ = 1`**, the fact that makes the two Dirichlet
  polynomials of the approximate functional equation contribute equally;
* `zetaSum N s = ∑_{1 ≤ n ≤ N} n^(−s)`, `zetaSumDual N s = ∑_{1 ≤ n ≤ N} n^(s−1)`, and
  `zetaSumDual_criticalLine` — on the critical line the second is the conjugate of the first;
* `norm_zetaSum_criticalLine_le` — the trivial bound `‖zetaSum N (1/2 + i t)‖ ≤ 2 √N`, uniform
  in `t`;
* `afeLength t = ⌊√(t/2π)⌋` and `sqrt_afeLength_le` — `√(afeLength t) ≤ t^(1/4)`.

Conditional, on the hypothesis `AFECriticalLine C`:

* `norm_riemannZeta_criticalLine_le_of_afe` — `‖ζ(1/2 + i t)‖ ≤ (C + 4) t^(1/4)` for `t ≥ 2`.

## The hypothesis

`AFECriticalLine C` is a `def ... : Prop`, a **statement**, not a theorem of this repository:

    ∀ t ≥ 2,
      ‖ζ(1/2+it) − ∑_{n ≤ x} n^(−1/2−it) − χ(1/2+it) ∑_{n ≤ x} n^(−1/2+it)‖ ≤ C t^(−1/4),
      x = √(t/2π).

The four hypothesis-hygiene questions of `AGENTS.md` are answered in the module docstring of
`RiemannHypothesis/ApproximateFunctionalEquation.lean`.  In short:

1. **Direction.**  What is free unconditionally is the *Euler–Maclaurin* representation
   (`RiemannHypothesis.Continuation`, `RiemannHypothesis.StripMeanSquareBernoulli`): `ζ` as a
   Dirichlet polynomial of length `N` plus an error that is small only for `N ≫ t`.  The
   successive Euler–Maclaurin corrections have relative size `(t/N)^k`, so the expansion stops
   gaining at `N ≍ t` and says nothing at `N ≍ √t`.  Halving the length from `t` to `√t` is
   exactly the content of the approximate functional equation and exactly what Euler–Maclaurin
   cannot do.
2. **Strength.**  It gives the convexity bound `t^(1/4)` here and, with cancellation, `t^(1/6)`
   (`M1-AFE-SUBCONVEXITY`).  It does not give Lindelöf, and a fortiori not the Riemann
   hypothesis: it is a statement about `ζ` on one line with a power-of-`t` error, and no
   zero-free region follows from it.
3. **Non-triviality.**  It is an unconditional classical theorem of Hardy and Littlewood (1921).
   Its proofs go through the Riemann–Siegel contour integral, or through truncated Poisson
   summation followed by stationary phase (van der Corput's B process).  Neither is in mathlib or
   in this repository, which is why it is recorded rather than proved.  It is in no way derived
   from the Riemann hypothesis.
4. **Attribution.**  Titchmarsh, *The Theory of the Riemann Zeta-Function*, Theorem 4.12,
   specialized to `σ = 1/2`, `x = y = √(t/2π)`, where the error is
   `O(x^(−σ) + t^(1/2−σ) y^(σ−1)) = O(t^(−1/4))`.  It quantifies over `ζ` on the critical line
   and over nothing else.

## Proof of the conditional bound

Both Dirichlet polynomials are bounded trivially: `‖zetaSum N (1/2+it)‖ ≤ ∑_{n ≤ N} n^(−1/2)
≤ 2√N` and, since `‖χ(1/2+it)‖ = 1` and the dual sum is the conjugate of the direct one, the
`χ`-term has the same bound.  With `N = afeLength t ≤ √(t/2π)` this is `2 t^(1/4)` each, and
`C t^(−1/4) ≤ C t^(1/4)`.

`‖χ(1/2+it)‖ = 1` is proved from `χ(s) χ(1−s) = 1` together with `χ(s̄) = conj (χ s)`: on the
critical line `1 − s = s̄`, so `χ(s) conj(χ(s)) = 1`, i.e. `‖χ(s)‖² = 1`.

## Boundary

The approximate functional equation itself is not proved.  Only the trivial bound for the two
Dirichlet polynomials is used, so no cancellation is exploited; that is `M1-AFE-SUBCONVEXITY`.
Nothing about the second moment `∫_0^T |ζ(1/2+it)|² dt ∼ T log T` follows: that additionally
needs the Montgomery–Vaughan mean value theorem, which is not in the repository.

## Gates

* `lake build RiemannHypothesis.ApproximateFunctionalEquation`
* `./scripts/audit.sh` — no `sorry`; axioms exactly `propext`, `Classical.choice`, `Quot.sound`;
  the one conditional theorem is recorded in `docs/goal/conditional-theorems.txt`.
