# Weyl's criterion in discrepancy form

Date: 2026-09-05
Module: `RiemannHypothesis/DiscrepancyCriterion.lean`

## Why

With the discrepancy `D_N(x)` available (`M1-DISCREPANCY`) the classical statement of Weyl's
theorem becomes expressible: *a sequence is equidistributed modulo one exactly when its
discrepancy tends to `0`*.  Neither `M1-WEYL-CRITERION` (equidistribution against continuous test
functions) nor `M1-WEYL-PORTMANTEAU` (the counting form, one interval at a time) can state it,
because both quantify over intervals or test functions *inside* the limit; the discrepancy puts
the supremum inside and the limit outside, which is a stronger-looking assertion and the one
usually quoted.

## What is proved

* `exists_nat_ge_eight_div_lt` — the choice of parameter: for every `ε > 0` there is `K ≥ 8` with
  `20/K < ε`.
* `tendsto_discrepancy_of_weylSumsVanish` — **the forward direction**: if
  `‖∑_{n<N} e(m xₙ)‖/N → 0` for every nonzero integer `m`, then `D_N(x) → 0`.
* `countsEquidistribute_of_tendsto_discrepancy` — the converse: `D_N(x) → 0` gives the counting
  form of equidistribution, by squeezing each interval deviation below `D_N`.
* `weylSumsVanish_iff_tendsto_discrepancy`, `equidistributedMod1_iff_tendsto_discrepancy`,
  `countsEquidistribute_iff_tendsto_discrepancy` — the three earlier formulations and the
  discrepancy form are all equivalent.
* `tendsto_discrepancy_quadratic` — for every irrational `α`, `D_N(α n²) → 0`.
* `not_tendsto_discrepancy_const_zero` — the criterion separates sequences: the constant sequence
  `0` has `D_N ≥ 1/2`, so its discrepancy does not tend to `0`.

## Proof of the forward direction

The naive argument fails: each interval deviation tends to `0`, but a supremum of infinitely many
null sequences need not be null, and `D_N` is exactly such a supremum.  The Erdős–Turán inequality
of `M1-WEYL-DISCREPANCY-GENERAL` is what repairs it, because it bounds all intervals at once:

    D_N ≤ 20/K + 4 ∑_{m=1}^{K⁴−1} ‖∑_{n<N} e(m xₙ)‖/N .

Given `ε > 0`, first choose `K ≥ 8` with `20/K < ε/2` — this uses no information about `x`.  The
remaining sum has *finitely many* terms, each tending to `0` by hypothesis, so the sum tends to
`0` and is eventually below `ε/8`.  Beyond that threshold `D_N < ε/2 + 4·(ε/8) = ε`.

## Verification

* `lake build` — succeeds, zero errors and zero warnings for the new module.
* No `sorry`; the axioms of every declaration are exactly
  `[propext, Classical.choice, Quot.sound]`, checked by the `#print axioms` block of
  `scripts/audit.sh`.
* `./scripts/audit.sh` — `OK`.
* Three statements pinned in `scripts/revalidation.lean`: the equivalence, the quadratic
  application, and the non-vacuity of the criterion.

## Adversarial revalidation: M1-DISCREPANCY-CRITERION

* **Is the forward direction a repackaging of the pointwise statement?**  No.  A supremum over
  infinitely many intervals is not controlled by the pointwise limits, and the proof does not use
  them: it uses the uniform inequality of `M1-WEYL-DISCREPANCY-GENERAL` and then passes to the
  limit in a *finite* sum, the finiteness being what the choice of `K` buys.
* **Is the equivalence circular?**  No.  The reverse direction goes through
  `CountsEquidistribute` and the criterion of `M1-WEYL-PORTMANTEAU`; the forward direction goes
  through the Erdős–Turán inequality.  Neither uses the other.
* **Could the equivalence hold vacuously, both sides being always true?**  No:
  `not_tendsto_discrepancy_const_zero` exhibits a sequence for which both sides fail.
* **Is any rate claimed?**  None.  Rates live in `M1-DISCREPANCY`, and only for badly
  approximable coefficients; for a general irrational no rate is available in this repository, as
  is correct, since none is true in general.
* **Is anything conditional?**  Nothing is assumed that is not proved elsewhere here, but the
  boundary file does record one new line: `tendsto_discrepancy_of_weylSumsVanish` takes the
  *definitional* `Prop` `WeylSumsVanish x` as a hypothesis, exactly as the earlier criterion
  theorems `weylSumsVanish_of_equidistributedMod1` and `weylSumsVanish_of_diff` do.  That is a
  hypothesis on the sequence, not an unproved conjecture of this repository, and
  `docs/goal/conditional-theorems.txt` was regenerated in the same commit to list it.
