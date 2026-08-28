# M2-ZERO-EXPONENT — the exponent of convergence of the nontrivial zeroes is at most `1`

Date: 2026-08-24
File: `RiemannHypothesis/ZeroExponent.lean`
Predecessor: `docs/goal/evidence/2026-08-20-m2-zero-sum.md` (`∑_ρ 1/‖ρ‖² < ∞`)

## Claim

For every `e > 0` the sum over the nontrivial zeroes of `ζ`, counted without multiplicity,

    ∑_ρ ‖ρ‖^(-(1+e))

converges: `RiemannHypothesis.summable_inv_norm_rpow`, with the uniform bound over finite
subsets `RiemannHypothesis.sum_inv_norm_rpow_le`. In the classical language, the exponent of
convergence of the zero set is at most `1`.

## Proof

The dyadic decomposition of `M2-ZERO-SUM`, run with the sharper weight `‖ρ‖^(-(1+e))`.

* `blockIndex ρ = log₂ ⌊|im ρ|⌋` splits the zeroes into blocks `2^k ≤ |γ| < 2^(k+1)`
  (`two_pow_blockIndex_le_abs_im`), together with the block of bounded height, which is finite.
* The Riemann–von Mangoldt upper bound `N(T) = O(T log T)` of `M2-ZERO-COUNT` bounds the `k`-th
  block by `C 2^(k+1)(k+1)` elements, and each element contributes at most `2^(-k(1+e))`, so the
  block contributes `O((k+1) 2^(-k e))`.
* `summable_succ_mul_geometric` — `∑_k (k+1) r^k` converges for `0 ≤ r < 1`, applied with
  `r = 2^(-e) < 1`; this gives the uniform bound `sum_inv_norm_rpow_le` over all finite sets of
  zeroes, hence summability over the subtype.

## Scope — what is *not* claimed

* Zeroes are counted **without multiplicity**, exactly as in `M2-ZERO-COUNT`.
* The complementary statement — that the exponent of convergence is *exactly* `1`, i.e. that
  `∑_ρ 1/‖ρ‖` diverges — is not proved: it needs the lower bound `N(T) ≫ T log T`, whereas
  `M2-ZERO-COUNT-LOWER` gives only a qualitative divergence with no rate. The row therefore
  stays `DONE_WEAK`.
* The Hadamard product for `ξ`, for which this summability is the analytic input, is not proved
  here; `M2-ZERO-INFINITE` uses only the finite factorization of an entire function whose zeroes
  form a finite set.

## Adversarial revalidation: M2-ZERO-EXPONENT

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `sum_inv_norm_rpow_le` and `summable_inv_norm_rpow`; the checks are in `scripts/audit.sh`.
* Both claims are pinned in `scripts/revalidation.lean`.
* The statement is not vacuous: it is stronger than `M2-ZERO-SUM` for `e < 1`, and the zero set
  it quantifies over is known to be infinite (`M2-ZERO-INFINITE`), so it is not a statement
  about an empty index set.
* The statement is unconditional: it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
