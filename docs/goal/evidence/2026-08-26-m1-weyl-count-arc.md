# M1-WEYL-COUNT-ARC — the counting form for an arbitrary arc of the circle

Date: 2026-08-26
File: `RiemannHypothesis/WeylCountArc.lean`

## Claim

An arc of `ℝ/ℤ` need not be an interval of `[0, 1)`: the arc running forwards from `a` through the
glueing point `0` to some `b < a` is described inside `[0, 1)` by the wrap-around set
`[a, 1) ∪ [0, b)`, of length `(1 − a) + b`. With

```
countArc x a b N = #{ n < N : Int.fract (x n) ∈ [a, 1) ∪ [0, b) }
```

the module proves

* `countIn_eq_zero_of_le` — an interval `[a, b)` with `b ≤ a` catches no term;
* `tendsto_countIn_div_of_le'` — the counting form for every `0 ≤ a ≤ b ≤ 1`, the degenerate
  interval `a = b` included;
* `countArc_eq_add` — for `b ≤ a`, `countArc x a b N = countIn x a 1 N + countIn x 0 b N`;
* `tendsto_countArc_div` — **the counting form for an arbitrary arc**: if `x` is equidistributed
  modulo one and `0 ≤ b ≤ a ≤ 1`, then `countArc x a b N / N → (1 − a) + b`;
* `tendsto_countArc_div_quadratic`, `tendsto_countArc_div_linear` — the specializations to
  `x n = α n²` and `x n = α n` with `α` irrational.

## Proof

The two pieces `[a, 1)` and `[0, b)` are disjoint precisely because `b ≤ a`, so the filter over
`Finset.range N` splits as a disjoint union and the cardinalities add. `M1-WEYL-COUNT-GENERAL`
applies to each piece — `[a, 1)` needs `0 ≤ a ≤ 1` and `[0, b)` needs `0 ≤ b ≤ 1`, both implied by
`0 ≤ b ≤ a ≤ 1` — once its hypothesis `a < b` is relaxed to `a ≤ b`, which is the content of
`tendsto_countIn_div_of_le'`: for `a = b` the count is identically `0` and the limit `b − a` is
`0` as well. Adding the two limits gives `(1 − a) + (b − 0)`.

## Why this row exists

The scope section of `M1-WEYL-COUNT-GENERAL` reads: "the wrap-around arc `[a, 1) ∪ [0, b)` with
`b < a` is not stated separately (it is the complement of `[b, a)`, but that complement statement
is not derived here)." This row states and proves it. Together the two rows cover every arc of
the circle.

## Scope, and what is *not* claimed

* No rate of convergence: the input carries none, so neither does the conclusion.
* Only arcs are treated; no statement is made for a general measurable subset of the circle
  (equidistribution does give the Jordan-measurable case, but that is not formalized here).
* Only the sequences `α n²` and `α n` are applied, and nothing about `ζ` is claimed.

## Adversarial revalidation: M1-WEYL-COUNT-ARC

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylCountArc`
  succeeds, the file contains no `sorry`, and it triggers no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `tendsto_countIn_div_of_le'`, `tendsto_countArc_div`, `tendsto_countArc_div_quadratic` and
  `tendsto_countArc_div_linear` (checked in `scripts/audit.sh`).
* All of the headline statements are pinned in `scripts/revalidation.lean` with `countArc`
  unfolded to the cardinality of an explicit `Finset.filter` over the disjunction, so the counting
  definition cannot be weakened.
* The statement is not vacuous and is not a restatement of an earlier row: at `a = 3/4`,
  `b = 1/4` the counted set is not an interval of `[0, 1)`, and the limit `1/2` is a nontrivial
  proportion.
* The degenerate endpoints are genuinely covered: at `b = 0` the arc is `[a, 1)` and the limit is
  `1 − a`; at `a = 1` it is `[0, b)` and the limit is `b`; at `a = b = 0` the arc is all of
  `[0, 1)` and the limit is `1`.
* The hypothesis `b ≤ a` is load-bearing for the splitting step: without it the two pieces
  overlap and the counts would be double-counted.
* No unproved `Prop` of this repository occurs as a hypothesis; the two specializations discharge
  `EquidistributedMod1`, so they are unconditional.
