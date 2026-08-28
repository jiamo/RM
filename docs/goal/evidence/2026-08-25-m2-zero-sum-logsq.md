# M2-ZERO-SUM-LOGSQ — `∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²`

Date: 2026-08-25
File: `RiemannHypothesis/ZeroSumLogSq.lean`
Predecessor: `docs/goal/evidence/2026-08-25-m2-zero-exponent-one.md` (`∑_ρ 1/‖ρ‖` diverges)

## Claim

Counting the nontrivial zeroes of `ζ` without multiplicity, and summing over those of ordinate
in `(0, T]`:

* `exists_mul_log_sq_le_sum_inv_norm` — there are `c > 0` and `T₀` with
  `c (log T)² ≤ ∑_{0 < γ ≤ T} 1/‖ρ‖` for all `T ≥ T₀`;
* `exists_sum_inv_norm_le_mul_log_sq` — there are `C > 0` and `T₀` with
  `∑_{0 < γ ≤ T} 1/‖ρ‖ ≤ C (log T)²` for all `T ≥ T₀`;
* `exists_sum_inv_norm_asymptotic` — the two together, on a common range.

The predecessor row proved only that this quantity tends to infinity (with the lower bound
`≫ log T`); the order of growth is now pinned down on both sides.

## Proof

Both halves are the same dyadic decomposition of `(0, T]` into the windows
`2^k < γ ≤ 2^(k+1)`, whose zero sets are pairwise disjoint
(`pairwiseDisjoint_dyadic_windowZeros`).

**Lower bound.**

* `exists_mul_le_windowCount_dyadic` — `N(T, 2T) ≫ T log T`. This is read off directly from the
  vendored Riemann–von Mangoldt formula `Zeta23.RvM.riemannVonMangoldt`, which bounds
  `|N(T, 2T) − (T/2π)·ell1 T|` by `C log T` with `ell1 T = log T − K`,
  `K = log(2π) − 2 log 2 + 1`; for `T ≥ max(exp(2K), 8π C)` the main term dominates and the
  constant `1/(8π)` survives.
* `exists_mul_le_windowCountDistinct_dyadic` — the same for *distinct* zeroes, by
  `five_sixths_distinct` at `ε = 1/6` (factor `2/3`).
* `div_le_sum_inv_norm_windowZeros` — every zero of ordinate in `(a, b]` with `a ≥ 0` has
  `‖ρ‖ ≤ |re ρ| + |im ρ| ≤ 1 + b`, so the sum over the window is at least
  `N_d(a, b)/(1 + b)`.
* `exists_mul_le_sum_inv_norm_block` — combining the two at `a = 2^k`, `b = 2^(k+1)`, the block
  contributes at least `c·2^k·k log 2 / (1 + 2^(k+1)) ≫ k`.
* Summing the blocks with `⌊log₂ T⌋/2 ≤ k < ⌊log₂ T⌋` — there are `≫ log T` of them, each
  contributing `≫ log T`, and they are disjoint subsets of the window `(0, T]` — gives
  `≫ (log T)²`.

**Upper bound.**

* `exists_sum_inv_norm_block_le` — every zero with `2^k < γ` has `‖ρ‖ ≥ |im ρ| > 2^k`, and by
  the Riemann–von Mangoldt *upper* bound `ncard_nontrivialZeros_le` (`M2-ZERO-COUNT`) there are
  at most `C·2^(k+1)·log 2^(k+1) ≤ 2C·2^k·(k+1)` zeroes of height at most `2^(k+1)`. So the
  block contributes at most `2C(k + 1)`.
* The window `(0, T]` is covered by `(0, 1]` together with the blocks `k < ⌈log₂ T⌉`: for a zero
  with `γ > 1` the least `j` with `γ ≤ 2^j` satisfies `j ≥ 1` and `2^(j−1) < γ ≤ 2^j`. The
  contribution of `(0, 1]` is a fixed finite constant `B ≥ 0`, and the blocks contribute at most
  `C·⌈log₂ T⌉² ≤ 4C (log₂ T)²`. For `T ≥ 4` this is `≤ ((4C + B)/(log 2)²)·(log T)²`.

## Scope — what is *not* claimed

* Zeroes are counted **without multiplicity** throughout.
* The constants are not explicit and the two constants do not match; no asymptotic
  `∑_{0 < γ ≤ T} 1/‖ρ‖ ~ (log T)²/(4π)` (the classical value) is claimed, only the order.
* The sum is over the zeroes of *positive* ordinate only.
* Nothing about the real parts of the zeroes is claimed, and nothing here bears on the Riemann
  hypothesis.

## Verification

* `lake build` — the whole project, clean.
* `bash scripts/audit.sh` — exit 0; the new statements are pinned in full in
  `scripts/revalidation.lean` and their axioms are checked.
* No `sorry` in `RiemannHypothesis/ZeroSumLogSq.lean`.

## Adversarial revalidation: M2-ZERO-SUM-LOGSQ

* `lake build` of the whole repository succeeds with `RiemannHypothesis/ZeroSumLogSq.lean`
  imported by `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `exists_mul_le_windowCountDistinct_dyadic`, `pairwiseDisjoint_dyadic_windowZeros`,
  `exists_mul_le_sum_inv_norm_block`, `exists_sum_inv_norm_block_le`,
  `exists_mul_log_sq_le_sum_inv_norm`, `exists_sum_inv_norm_le_mul_log_sq` and
  `exists_sum_inv_norm_asymptotic`; the checks are in `scripts/audit.sh`.
* All seven statements are pinned in full in `scripts/revalidation.lean`.
* The statements are not vacuous. The lower bound is an inequality on a sum over a set already
  known to be nonempty and, in fact, of cardinality `≫ T log T` (`M2-BOHR-LANDAU`); the upper
  bound is not implied by it, and neither is implied by the predecessor row, which gave only
  `≫ log T`. The `∃ T₀` quantifiers range over all sufficiently large `T`, and the constants are
  required positive, so neither statement can be satisfied by a degenerate choice.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
* Direction check: the two halves use genuinely different inputs — the Riemann–von Mangoldt
  *lower* bound (vendored `Zeta23.RvM.riemannVonMangoldt`, plus Theorem C for distinctness) for
  the lower half, and the Jensen-type *upper* bound `ncard_nontrivialZeros_le` for the upper
  half. Both inputs are proved in the repository, not assumed.
