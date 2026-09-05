# The discrepancy itself, and a power saving for `α n`

Date: 2026-09-05
Module: `RiemannHypothesis/Discrepancy.lean`

## Why

Every discrepancy statement of this repository was, until now, a statement about one interval
at a time: `M1-WEYL-DISCREPANCY` and `M1-WEYL-DISCREPANCY-GENERAL` bound
`|#{n < N : {xₙ} ∈ [a, b)}/N − (b − a)|` for a given `[a, b)`, with a parameter `K` supplied by
the caller.  The quantity that classical statements are about is the supremum

    D_N(x) = sup { |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| : 0 ≤ a ≤ b ≤ 1 } ,

and no such object existed here.  Introducing it is what makes it possible to state a rate in
the shape it is usually quoted in — `D_N = O(N^(−1/9))` — with no auxiliary parameter, and it is
only legitimate now: a supremum over all subintervals cannot be bounded by an inequality that
excludes the short intervals, which is why `M1-WEYL-DISCREPANCY-GENERAL` had to come first.

## What is proved

* `discrepancySet`, `discrepancy` — the set of interval deviations, and its supremum.  The set is
  nonempty (`discrepancySet_nonempty`, the degenerate interval `[0, 0)`) and bounded above by `1`
  (`discrepancySet_bddAbove`, from `abs_countIn_div_sub_le_one`), so the supremum is a genuine
  least upper bound.
* `le_discrepancy`, `discrepancy_le_of_forall`, `discrepancy_nonneg`, `discrepancy_le_one` — the
  interface: every interval is dominated by `D_N`, and a bound holding for all intervals bounds
  `D_N`.
* `half_le_discrepancy_const_zero` — a non-vacuity check: the constant sequence `0` has
  `D_N ≥ 1/2`, since `[1/2, 1)` receives none of its fractional parts.
* `discrepancy_le_pow` — the Erdős–Turán inequality in discrepancy form,
  `D_N ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N` for `K ≥ 8` and `N ≥ 1`.
* `discrepancy_linear_le` — `D_N(α n) ≤ (20 + 2/c)/K` for a badly approximable `α`, `K ≥ 8`,
  `K⁹ ≤ N`.
* `discrepancy_linear_le_rpow` — **the power saving**: for `N ≥ 8⁹`,

      D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9) .

* `tendsto_discrepancy_linear` — hence `D_N(α n) → 0`: Weyl's theorem for `α n` with a rate.

## Proof of the power saving

Take `K = ⌊N^(1/9)⌋`.  Then `K ≥ 8` because `N ≥ 8⁹`, and `K⁹ ≤ N` because `K ≤ N^(1/9)`, so
`discrepancy_linear_le` applies and gives `D_N ≤ (20 + 2/c)/K`.  For the other side,
`K > N^(1/9) − 1 ≥ N^(1/9)/2` — the second inequality again because `N^(1/9) ≥ 8` — so
`1/K ≤ 2 N^(−1/9)`.  The convergence to `0` then follows by squeezing between `0` and
`2 (20 + 2/c) N^(−1/9)`, which tends to `0` by `tendsto_rpow_neg_atTop`.

## Verification

* `lake build` — succeeds, zero errors and zero warnings for the new module.
* No `sorry`; the axioms of every declaration are exactly
  `[propext, Classical.choice, Quot.sound]`, checked by the `#print axioms` block of
  `scripts/audit.sh`.
* `./scripts/audit.sh` — `OK`.
* Three statements pinned in `scripts/revalidation.lean`: the definition of `discrepancy`
  written out with `countIn` unfolded and checked by `rfl`, the non-vacuity bound for the
  constant sequence, and the power saving.

## Adversarial revalidation: M1-DISCREPANCY

* **Is the supremum well defined, or is `sSup` silently `0` on an unbounded set?**  Well defined:
  `discrepancySet_nonempty` and `discrepancySet_bddAbove` are proved and used, and the pinned
  `rfl` in `scripts/revalidation.lean` shows that the set is the intended one, written out with
  no abbreviation.
* **Could the definition be trivially `0`?**  No: `half_le_discrepancy_const_zero` exhibits a
  sequence with `D_N ≥ 1/2` for every `N`, so the definition separates sequences.
* **Does the power saving hold for every `α`?**  No, and it is not claimed to: the hypothesis is
  that `α` is badly approximable, `‖mα‖ ≥ c/m` for every `m ≥ 1`.  For an irrational of infinite
  type no power saving is true, and the repository claims none.
* **Is the exponent honest?**  The exponent `1/9` is the one that the kernel of
  `M1-WEYL-DISCREPANCY` yields, with weight `1` on the `m`-th exponential sum; the classical
  Erdős–Turán inequality, which needs the Beurling–Selberg extremal majorant, would give
  `O(log N / N)` for the same `α`.  The gap is recorded, not hidden.
* **Is anything conditional?**  No unproved `Prop` of this repository is used; the module imports
  only `RiemannHypothesis.WeylDiscrepancyGeneral` and Mathlib, and
  `docs/goal/conditional-theorems.txt` is unchanged.
