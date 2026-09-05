# The discrepancy bound for every subinterval

Date: 2026-09-05
Module: `RiemannHypothesis/WeylDiscrepancyGeneral.lean`

## Why

`M1-WEYL-DISCREPANCY` proves an Erdős–Turán type inequality

    |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 4/K + 2 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N

but only for intervals with `1/K < a`, `b + 1/K < 1` and `a + 2/K ≤ b`, and its open boundary
records exactly that: "the interval is required to satisfy `1/K < a` and `b + 1/K < 1` and
`a + 2/K ≤ b`, so intervals shorter than `2/K` or touching the glueing point are not covered at
that value of `K`".  The restriction is not cosmetic.  A *discrepancy* is by definition a
supremum over all subintervals of `[0, 1]`, and the intervals a supremum is attained on are
precisely the short ones and the ones with an endpoint at `0` or `1`; so long as they are
excluded, the inequality bounds no discrepancy, and it says nothing at all about, for instance,
`[0, 1/2)`.  This row removes the restriction.

## What is proved

All statements live in `RiemannHypothesis.WeylDiscrepancy`, in the new module.

* `norm_expSum_add_const`, `sum_norm_expSum_add_const` : translating the sequence by a constant
  multiplies each exponential sum by the unimodular factor `e(mc)`, so the right-hand side of the
  inequality is unchanged.
* `countIn_mono`, `countIn_le`, `countIn_add_countIn`, `countIn_split_unit` : the elementary
  properties of the counting function — monotone in the interval, at most `N`, additive over
  adjacent intervals, and `#[0,a) + #[a,b) + #[b,1) = N`.
* `abs_countIn_div_sub_le_pow_shift` : the bound `4/K + 2 ∑_{m<K⁴} ‖·‖/N` for **every** interval
  `[a, b) ⊆ [0, 1]` whose length lies between `2/K` and `1 − 4/K`, with no condition on its
  position.
* `countIn_div_le_of_le` : the one-sided bound `#[a,b)/N ≤ (b − a) + 10/K + 2 ∑_{m<K⁴} ‖·‖/N` for
  every `0 ≤ a ≤ b ≤ 1`, short intervals included.
* `abs_countIn_div_sub_le_pow_of_le` : **the discrepancy bound**, for every `0 ≤ a ≤ b ≤ 1`,
  every `K ≥ 8` and every `N ≥ 1`,

      |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N .

* `sum_norm_expSum_div_le_linear`, `abs_countIn_div_sub_le_linear_of_le` : for `α` badly
  approximable with constant `c`, the discrepancy of `α n` over *all* subintervals is at most
  `(20 + 2/c)/K` as soon as `K⁹ ≤ N`, i.e. `O(N^(−1/9))`.
* `sum_norm_expSum_div_le_quadratic`, `abs_countIn_div_sub_le_quadratic_of_le`,
  `abs_countIn_div_sub_le_sqrt_two_of_le` : the same for `α n²` with `2α` badly approximable, and
  the concrete instance `α = √2/2`.

## Proof

Three elementary devices, one per restriction.

*Rotation* removes the two position conditions.  For an interval of length between `2/K` and
`1 − 4/K` set `c = (1 − (b − a))/2 − a`; then `a + c = (1 − (b − a))/2 ≥ 2/K > 1/K` and
`b + c = 1 − (a + c) ≤ 1 − 2/K`, so `[a + c, b + c)` satisfies all three hypotheses of
`abs_countIn_div_sub_le_pow` for the translated sequence `x + c`.  The counting function is
unchanged by the matched translation (`WeylCount.countIn_add_const`) and so is the right-hand
side (`sum_norm_expSum_add_const`).

*Enlargement* removes the length condition in the upper bound.  With `a' = min a (1 − 2/K)` and
`b' = max b (a' + 2/K)` the interval `[a', b') ⊆ [0, 1]` contains `[a, b)`, has length at least
`2/K`, and — as long as `b − a ≤ 1 − 6/K` — at most `1 − 4/K`; monotonicity of the count and the
rotated bound give `#[a,b)/N ≤ (b − a) + 10/K + 2∑`.  When `b − a > 1 − 6/K` the trivial bound
`#[a,b) ≤ N` already gives it.  In the lower bound a short interval needs no argument at all:
the count is nonnegative and `(b − a) − 2/K < 0`.

*Complementation* handles the intervals so long that they cannot be enlarged.  For
`b − a > 1 − 6/K` the identity `#[0,a) + #[a,b) + #[b,1) = N` turns the lower bound for `[a, b)`
into the two upper bounds just proved for the short intervals `[0, a)` and `[b, 1)`, and loses
exactly `2 · (10/K + 2∑)`.  Adding the cases gives `20/K + 4∑`, which is the constant claimed.

## Verification

* `lake build` — succeeds, zero errors and zero warnings for the new module.
* No `sorry`; the axioms of every declaration of the module are exactly
  `[propext, Classical.choice, Quot.sound]`, checked by the `#print axioms` block of
  `scripts/audit.sh`.
* `./scripts/audit.sh` — `OK`.
* Three statements pinned in `scripts/revalidation.lean`, with `countIn` and `e2pi` written out,
  so a later weakening of the declarations stops the audit from elaborating.

## Adversarial revalidation: M1-WEYL-DISCREPANCY-GENERAL

* **Is the new statement weaker than the old one where they overlap?**  Only in the constant:
  `20/K + 4∑` against `4/K + 2∑`.  The earlier theorem is unchanged and still available, and the
  new one is not derived by weakening its hypotheses but by covering the intervals it excludes.
* **Is it vacuous for the intervals that motivate it?**  No.  For `a = 0`, `b = 1/2` and `K ≥ 8`
  it gives `|#[0,1/2)/N − 1/2| ≤ 20/K + 4∑`, a statement the earlier form cannot make at any `K`,
  since `1/K < a` fails for `a = 0`.  For an interval of length `< 2/K` the bound is weaker than
  the trivial `≤ b − a + 20/K` only by the sum term, as it must be: at that scale nothing better
  is available from `K⁴` frequencies.
* **Is `K ≥ 8` load-bearing?**  Yes, and mildly so: it is what makes `2/K ≤ 1 − 4/K` (so that an
  interval of length `2/K` fits inside the admissible range) and `1 − 2/K ≥ 0` (so that the
  enlarged interval stays inside `[0, 1]`).  Any `K ≥ 6` would do for the first and `K ≥ 2` for
  the second; `8` was chosen to keep the arithmetic uniform.
* **Does the rotation smuggle in an assumption on the sequence?**  No.  `x + c` is an arbitrary
  translate of an arbitrary sequence, and the translation identity for the counts,
  `WeylCount.countIn_add_const`, is proved for every real sequence with no hypothesis beyond
  `0 ≤ a`, `b ≤ 1` and the position of the translated interval.
* **Is anything conditional?**  No unproved `Prop` of this repository is used; the module imports
  only `RiemannHypothesis.WeylDiscrepancyQuadratic`, `RiemannHypothesis.WeylCountGeneral` and
  Mathlib, and `docs/goal/conditional-theorems.txt` is unchanged.
* **What is still open?**  Everything the inherited rows record: the weight of the `m`-th
  exponential sum is `1` rather than `1/m`, so the exponent in the linear application stays at
  `1/9`; the Beurling–Selberg extremal majorant is not formalized; the constants are not
  optimized; and nothing here concerns `ζ`.
