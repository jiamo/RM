# Weyl's criterion in its counting form

Date: 2026-09-04
Module: `RiemannHypothesis/WeylPortmanteau.lean`

## Why

`M1-WEYL-CRITERION` proved Weyl's criterion in the analytic form — equidistribution stated
against *continuous* test functions on `ℝ/ℤ` — and recorded in its open boundary that "the
equivalent count of `n < N` with fractional part in a subinterval is not derived".  Half of that
gap was closed by `M1-WEYL-COUNT`, `M1-WEYL-COUNT-GENERAL` and `M1-WEYL-COUNT-ARC`, which deduce
the counting statement *from* equidistribution.  The converse — that the counting statement, taken
for every subinterval, already forces equidistribution — was missing, and it is the direction that
makes the criterion usable in the form in which it is normally stated: no test function, no
integral, only counts.

## What is proved

All statements live in `RiemannHypothesis.WeylPortmanteau`.

* `CountsEquidistribute x` : for every `0 ≤ a < b ≤ 1`,
  `#{n < N : Int.fract (x n) ∈ [a, b)} / N → b − a`.
* `countsEquidistribute_of_equidistributedMod1` : the easy direction, from
  `tendsto_countIn_div_of_le`.
* `weylSumsVanish_of_countsEquidistribute` : **the new direction** — the counting statement
  implies `‖∑_{n<N} e(m xₙ)‖ / N → 0` for every nonzero integer `m`.
* `equidistributedMod1_of_countsEquidistribute`,
  `equidistributedMod1_iff_countsEquidistribute`,
  `weylSumsVanish_iff_countsEquidistribute` : the three formulations are equivalent.
* `countsEquidistribute_quadratic` : for every irrational `α` the fractional parts of `α n²`
  satisfy the counting statement.

Supporting lemmas, all of independent use:

* `norm_e2pi_sub_one_le`, `norm_e2pi_sub_e2pi_le` : the phase is `2π`-Lipschitz,
  `‖e(u) − e(v)‖ ≤ 2π|u − v|`.
* `e2pi_int_mul_fract` : an integer frequency does not see the integer part of its argument.
* `e2pi_nat_mul`, `sum_e2pi_roots_eq_zero` : `e(nθ) = e(θ)ⁿ`, and the mean of a nontrivial
  character over the `K`-th roots of unity vanishes — proved from `geom_sum_eq` together with
  `Complex.exp_eq_one_iff`, whose hypothesis `K ∤ m` is exactly what `K > |m| > 0` gives.
* `cell`, `cell_lt`, `cell_eq_iff`, `countIn_cell_eq_card` : the partition of `[0, 1)` into `K`
  equal cells, and the identification of the counting function of a cell with the cardinality of
  a fibre of `n ↦ cell K (x n)`.
* `norm_sum_e2pi_sub_stepSum_le` : replacing each phase `e(m xₙ)` by the value of the phase at the
  left endpoint of the cell containing `Int.fract (x n)` costs at most `N · 2π|m|/K` in total.

## Proof of the new direction

Fix `m ≠ 0` and `ε > 0`, and choose `K` with `K > |m|` and `2π|m|/K < ε/2`.  Cutting `[0, 1)`
into the `K` cells `[j/K, (j+1)/K)` and replacing every term of the exponential sum by the value
of the phase at the left endpoint of its cell changes the sum by at most `N · 2π|m|/K < Nε/2`
(`norm_sum_e2pi_sub_stepSum_le`, whose proof is the Lipschitz bound applied fibre by fibre through
`Finset.sum_fiberwise_of_maps_to`).  What is left is `∑_{j<K} c_j(N) e(m j/K)` with
`c_j(N)` the counting function of the `j`-th cell; the hypothesis gives `c_j(N)/N → 1/K` for each
of the finitely many `j`, so the average converges to `(1/K) ∑_{j<K} e(m j/K)`, which is `0`
because `K ∤ m`.  Beyond a threshold both contributions are below `ε/2`, so `‖S_N‖/N < ε`.

The `K > |m|` condition is not cosmetic: for `K ∣ m` the mean over the roots of unity is `1`, and
the argument would prove nothing.

## Gates

* `lake build RiemannHypothesis.WeylPortmanteau` — success, no `sorry`.
* `lake build` — success (9201 jobs), the only `sorry`s in the repository being the three
  intentional ones in `Challenge.lean`.
* `#print axioms` on `sum_e2pi_roots_eq_zero`, `norm_sum_e2pi_sub_stepSum_le`,
  `weylSumsVanish_of_countsEquidistribute`, `equidistributedMod1_iff_countsEquidistribute`,
  `weylSumsVanish_iff_countsEquidistribute`, `countsEquidistribute_quadratic`: each is exactly
  `[propext, Classical.choice, Quot.sound]`.
* `./scripts/audit.sh` — `OK`.
* Three statements pinned in `scripts/revalidation.lean`, written out with `countIn`, `e2pi` and
  `CountsEquidistribute` fully unfolded, so a later weakening of any of the three declarations
  stops the audit from elaborating.

## Adversarial revalidation: M1-WEYL-PORTMANTEAU

* **Is the new direction vacuous, or does it silently assume equidistribution?**  No.  The
  hypothesis `CountsEquidistribute` mentions no test function, no measure and no character: it is a
  statement about cardinalities of subsets of `Finset.range N`.  The pins in
  `scripts/revalidation.lean` restate it with `countIn` unfolded, so what is assumed is literally
  `((Finset.range N).filter fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card / N → b − a`.
* **Is the equivalence non-trivial in both directions?**  The forward direction is the earlier
  rows' work (`tendsto_countIn_div_of_le`, itself a trapezoid approximation argument); the reverse
  direction is proved here from scratch and does not call it.  Neither direction is definitional:
  `EquidistributedMod1` quantifies over `C(ℝ/ℤ, ℂ)` and `CountsEquidistribute` over pairs of reals.
* **Does the statement hold for a sequence that is not equidistributed?**  It must not, and it
  does not: `not_equidistributedMod1_const_zero` (`M1-WEYL-CRITERION`) shows the constant sequence
  `0` is not equidistributed, and by the equivalence proved here it therefore fails the counting
  statement — as it visibly does, since every fractional part is `0` and the interval `[1/2, 1)`
  receives none of them.
* **Is the constant `K > |m|` load-bearing?**  Yes; it is exactly the hypothesis `¬ (K ∣ m)` of
  `sum_e2pi_roots_eq_zero`, without which the character sum over the `K`-th roots of unity is `K`
  rather than `0`.  The choice `K > max (|m|, 4π|m|/ε)` supplies both that and the fineness of the
  partition.
* **Is anything conditional?**  No unproved `Prop` of this repository is used; the module imports
  only `RiemannHypothesis.WeylCountGeneral` and Mathlib, and every declaration's axioms are the
  standard three.
