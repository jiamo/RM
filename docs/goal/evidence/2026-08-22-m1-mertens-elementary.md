# M1-MERTENS-ELEMENTARY — the elementary Möbius sums and Landau's inequality

Date: 2026-08-22
Module: `RiemannHypothesis/MertensSums.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `sum_divisors_moebius` — `∑_{d ∣ k} μ(d) = 1` if `k = 1` and `0` otherwise, read off from
  mathlib's `moebius_mul_coe_zeta`.
* `sum_pairs_inner`, `sum_pairs_outer` — the two hyperbola reindexings of the set of pairs
  `(d, e)` with `d·e ≤ m`: the bijection `(d, e) ↦ (d·e, e)` onto the pairs `(k, e)` with
  `k ≤ m` and `e ∣ k`, once with the summand depending on the second coordinate and once on
  the first.  They are stated for an arbitrary `f : ℕ → ℤ`.
* `sum_Icc_sum_divisors_moebius` — `∑_{k ≤ m} ∑_{e ∣ k} μ(e) = 1` for `m ≥ 1`.
* `sum_moebius_mul_div` — `∑_{n ≤ N} μ(n)⌊N/n⌋ = 1` for `N ≥ 1`.
* `abs_littleMertens_le_one` — **Landau's inequality** `|∑_{n ≤ N} μ(n)/n| ≤ 1`, for every `N`,
  where `littleMertens` is the sum already used by `RiemannHypothesis.MoebiusOverNCriterion`.
  The proof replaces `⌊N/n⌋` by `N/n` in the previous identity: the `N` fractional parts have
  absolute value at most one and the term `n = 1` contributes nothing, so
  `|N · m(N)| ≤ 1 + (N − 1) = N`.

`RiemannHypothesis/Redheffer.lean` now takes its Möbius input (`sum_mertens_div`) from
`sum_pairs_inner` and `sum_Icc_sum_divisors_moebius` here, instead of duplicating the
reindexing.

## Scope and claim mode

* Landau's inequality is unconditional but weak: the criterion of
  `RiemannHypothesis.MoebiusOverNCriterion` needs `m(N) = O(N^{-1/2+ε})`, which is *equivalent*
  to the Riemann hypothesis and is not proved anywhere in this repository.  The bound `1` shows
  no cancellation beyond the trivial one and implies nothing about the zeroes.
* No `sorry`; `#print axioms` gives exactly `propext`, `Classical.choice`, `Quot.sound`
  (checked in `scripts/audit.sh`).

## Adversarial revalidation: M1-MERTENS-ELEMENTARY

Pinned in `scripts/revalidation.lean` (section `M1-MERTENS-ELEMENTARY`):

* the definition of `littleMertens` is pinned definitionally (`rfl`);
* `sum_moebius_mul_div hN : ∑ n ∈ Finset.Icc 1 N, (⌊N/n⌋ : ℤ) * μ n = 1` for `1 ≤ N`;
* `abs_littleMertens_le_one N : |littleMertens N| ≤ 1`.

Checks run: `lake build`, `lake build RiemannHypothesis.MertensSums`, `./scripts/audit.sh`,
`python3 scripts/goal_state.py validate`.

Counter-check on the claim: nothing here produces a term of type `LittleMertensBoundForm`,
`MertensBoundForm` or `ZetaForm`; the inequality is an unconditional bound by the constant `1`,
not a square-root bound.
