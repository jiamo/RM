# Koksma's inequality for a Lipschitz integrand, with the sharp constant

Date: 2026-09-07
Module: `RiemannHypothesis/KoksmaSharp.lean`

## Why

`M1-KOKSMA` proves the Lipschitz form of Koksma's inequality with the constant `3 L`, and
`M1-KOKSMA-VARIATION` improves it to `2 L`; both rows record the same open boundary, that the
classical constant is `L`.  The factor came entirely from the detour through monotone functions:
an `L`-Lipschitz `f` was written as a difference of two monotone functions, and the rises of the
two pieces, not `L`, entered the bound.  This row removes the detour and proves the sharp form.

## What is proved

* `abs_sum_weight_cellDev_le` — the summation-by-parts step with monotonicity removed: for an
  arbitrary weight sequence `a`, every `K ≥ 1` and every `N ≥ 1`,

      |∑_{j<K} a_j (c_j/N − 1/K)| ≤ (∑_{j<K} |a_{j+1} − a_j|) · D_N(x),

  where `c_j = countIn x (j/K) ((j+1)/K) N` counts the `n < N` in the `j`-th cell.  The boundary
  terms vanish as in `M1-KOKSMA`, and each tail deviation is at most `D_N(x)`.
* `abs_avg_sub_stepAvg_le` — for an `L`-Lipschitz `f`, replacing each value `f(⟨xₙ⟩)` by the value
  at the left endpoint of its cell changes the sum by at most `N · L/K`.
* `abs_integral_sub_riemannSum_le` — the left Riemann sum on the same grid differs from `∫₀¹ f`
  by at most `L/K`.
* `sum_abs_grid_diff_le` — `∑_{j<K} |f((j+1)/K) − f(j/K)| ≤ L`.
* `abs_avg_sub_integral_le_add` — the quantitative step: the error is at most
  `L · D_N(x) + 2 L/K` for every `K ≥ 1`.
* `koksma_lipschitz_sharp` — hence, for every `L`-Lipschitz `f` on `[0,1]`, every sequence `x`
  and every `N ≥ 1`,

      |(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ L · D_N(x) .

* `tendsto_average_of_tendsto_discrepancy_lipschitz` — the limiting form.

## Proof

With `t_j = j/K` and `c_j` the cell counts,

    (1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f
      = [(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∑_j (c_j/N) f(t_j)]
        + ∑_j f(t_j) (c_j/N − 1/K)
        − [∫₀¹ f − ∑_j (1/K) f(t_j)] .

The first bracket is at most `L/K` because every point of the `j`-th cell is within `1/K` of
`t_j`; the third likewise, cell by cell, using
`intervalIntegral.sum_integral_adjacent_intervals` to split the integral and
`intervalIntegral.norm_integral_le_of_norm_le_const` on each cell.  The middle sum is
`abs_sum_weight_cellDev_le` applied to `a_j = f(t_j)`, whose grid variation
`∑_j |f(t_{j+1}) − f(t_j)| ≤ K · (L/K) = L`.  So the error is at most `L D_N(x) + 2L/K` for every
`K ≥ 1`; since `K` is arbitrary and the left side does not depend on it, the error is at most
`L D_N(x)`.

## Scope

The statement is sharp in the constant for Lipschitz integrands.  The sharp constant for a
general function of bounded variation, `V(f)` rather than `2 V(f)`, remains open
(`M1-KOKSMA-VARIATION`): the argument above bounds the in-cell oscillation by `L/K`, which for a
mere bounded-variation integrand is replaced by the cell variations, and controlling their
maximum needs the continuity of the variation function — not available in mathlib.  Nothing here
concerns `ζ`.

## Adversarial revalidation: M1-KOKSMA-LIPSCHITZ-SHARP

* **Is the constant checked by hand?**  Yes.  Take `f = id` on `[0,1]`, which is `1`-Lipschitz,
  and the sequence `xₙ = 0`: the average is `0`, the integral is `1/2`, so the left side is
  `1/2`, and the inequality reads `1/2 ≤ 1 · D_N`.  The repository proves
  `half_le_discrepancy_const_zero`, `D_N ≥ 1/2`, and `discrepancy_le_one`, `D_N ≤ 1`, so the
  instance is consistent and is attained at the extreme end of the admissible range: the constant
  `L = 1` cannot be lowered on this example.  With the old constant `3 L` the same instance was
  three times weaker.
* **Does the `K → ∞` step hide anything?**  No.  `abs_avg_sub_integral_le_add` is fully
  quantitative for each fixed `K`, and the passage to the limit is `le_of_forall_pos_le_add`
  applied to the term `2L/K`, which does not touch the `L D_N(x)` term.  No limit is taken in
  `N`, and the final statement holds for every fixed `N ≥ 1`.
* **Is `abs_sum_weight_cellDev_le` really weight-agnostic?**  Yes: no monotonicity, no
  Lipschitz, no sign condition — only the summation-by-parts identity, `S_0 = S_K = 0` and
  `|S_j| ≤ D_N`.  It specialises to the monotone lemma of `M1-KOKSMA` because for a nondecreasing
  `f` the grid variation telescopes to `f 1 − f 0`.
* **Are the hypotheses load-bearing?**  `0 < N` is needed for the division; `0 ≤ L` is used for
  the continuity/integrability of `f` and in the discretisation bounds; the Lipschitz hypothesis
  is used in all three terms.  Nothing is assumed about continuity beyond what the Lipschitz
  condition itself gives.
* **Claim mode.**  A theorem proved here, not a `Prop`, not a mathlib re-export; mathlib supplies
  only the interval-integral lemmas named above.
* **Anything claimed about `ζ`?**  Nothing.

## Gates

* `lake build RiemannHypothesis.KoksmaSharp`
* `lake build`
* `./scripts/audit.sh`
* Axioms of `abs_sum_weight_cellDev_le`, `koksma_lipschitz_sharp`,
  `tendsto_average_of_tendsto_discrepancy_lipschitz`: exactly `propext`, `Classical.choice`,
  `Quot.sound`.
