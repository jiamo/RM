# M2-MEANVALUE — the mean value theorem for Dirichlet polynomials with arbitrary coefficients

Date: 2026-08-24
File: `RiemannHypothesis/DirichletPolyMeanValue.lean`
Related: `RiemannHypothesis/DirichletPolyMeanSquare.lean` (the expansion of the mean square into
a diagonal term and the off-diagonal remainder `offDiagSum`),
`RiemannHypothesis/StripMeanSquareAsymptotic.lean` (the two-sided form
`abs_integral_normSq_dirichletPoly_sub_diag_le`)

## Claim

For **every** choice of coefficients `a : ℕ → ℂ`, every length `N`, every abscissa `σ` and every
`T`,

    |∫₀ᵀ ‖∑_{1 ≤ n ≤ N} a n · n^(-σ-i t)‖² dt − T ∑_{1 ≤ n ≤ N} ‖a n‖² n^(-2σ)|
        ≤ 8 N (1 + log N) ∑_{1 ≤ n ≤ N} ‖a n‖² n^(-2σ),

`RiemannHypothesis.abs_integral_normSq_dirichletPoly_sub_diag_le_mvt`; that is,

    ∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)

with the explicit constant `8`.  On the imaginary axis this reads

    |∫₀ᵀ ‖∑_{n ≤ N} a n · n^(-i t)‖² dt − T ∑_{n ≤ N} ‖a n‖²| ≤ 8 N (1 + log N) ∑_{n ≤ N} ‖a n‖²,

`RiemannHypothesis.integral_normSq_dirichletPoly_mvt_zero`.

The intermediate estimate, which is the new content, is

    offDiagSum a N σ ≤ 8 N (1 + log N) ∑_{n ≤ N} ‖a n‖² n^(-2σ),

`RiemannHypothesis.offDiagSum_le`.

## Proof

Write `b k = ‖a k‖ k^(-σ)`, so the diagonal is `∑ b n ²` and a pair `m ≠ n` contributes
`2 b m · b n / |log (n/m)|` to `offDiagSum`.  Three elementary steps:

1. *Separation of the logarithms.*  `inv_abs_log_div_le` gives
   `1/|log (n/m)| ≤ (m + n)/|n − m|`, and `m, n ≤ N` gives `m + n ≤ 2N`, so the pair term is at
   most `4 N b m · b n / |n − m|`.
2. *The arithmetic–geometric mean inequality.*  `2 b m · b n ≤ b m ² + b n ²`, so the pair term
   is at most `2 N (b m ² + b n ²)/|n − m|` — this is `offDiag_term_le`.
3. *The harmonic bound.*  `sum_inv_abs_sub_le` (already in the repository) gives
   `∑_{n ≤ N, n ≠ m} 1/|n − m| ≤ 2 (1 + log N)`, restated in the `if`-form of `offDiagSum` as
   `sum_inv_abs_sub_le'`.

Summing, the `b m ²` half contributes `4 N (1 + log N) ∑ b n ²` directly and the `b n ²` half
contributes the same after `Finset.sum_comm`; together `8 N (1 + log N) ∑ b n ²`.  Feeding this
into the two-sided expansion `abs_integral_normSq_dirichletPoly_sub_diag_le` gives the mean value
theorem.

## Scope — what is *not* claimed

* This is the **elementary** mean value theorem.  The sharp Montgomery–Vaughan form replaces the
  factor `N log N` in front of the whole sum by the weight `n` inside it,
  `∫₀ᵀ |D(i t)|² dt = ∑ |a n|² (T + O(n))`; that needs Montgomery and Vaughan's generalized
  Hilbert inequality, which is **not** formalized here.  The `log N` is likewise not removed.
* The **large sieve inequality** proper — a bound for `∑_r |D(i t_r)|²` over well-spaced points
  `t_r` — is not proved; only the continuous mean square over an interval is treated.
* The **fourth moment** `∫₀ᵀ |ζ(1/2 + i t)|⁴ dt = O(T log⁴ T)` is not proved: it needs the
  approximate functional equation on the critical line and the divisor correlation sums, neither
  of which is available here.  The row therefore stays `DONE_WEAK`.

## Adversarial revalidation: M2-MEANVALUE

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for `offDiagSum_le`,
  `abs_integral_normSq_dirichletPoly_sub_diag_le_mvt` and
  `integral_normSq_dirichletPoly_mvt_zero`; the checks are in `scripts/audit.sh`.
* The three claims are pinned in `scripts/revalidation.lean`.
* The statement is not vacuous: it is an equality up to an error, quantified over *all*
  coefficient sequences, and for `T` large compared with `N log N` the main term dominates, so
  it is a genuine two-sided asymptotic and not merely an upper bound.  Specialized to `a ≡ 1` it
  recovers a bound of the same shape as `offDiagSum_one_le` (which is sharper in the exponent,
  being tuned to that coefficient sequence).
* The statement is unconditional: it takes no unproved `Prop` of this repository as a hypothesis,
  and the module adds no row to `docs/goal/conditional-theorems.txt`.
