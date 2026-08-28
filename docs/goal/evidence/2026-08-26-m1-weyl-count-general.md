# M1-WEYL-COUNT-GENERAL — the counting form for an arbitrary subinterval

Date: 2026-08-26
File: `RiemannHypothesis/WeylCountGeneral.lean`

## Claim

With `countIn x a b N = #{ n < N : Int.fract (x n) ∈ [a, b) }` as in `M1-WEYL-COUNT`, the module
proves

* `equidistributedMod1_add_const` — if `x` is equidistributed modulo one then so is `x + c` for
  every real `c`;
* `fract_mem_Ico_iff_add` — for `0 ≤ a < b ≤ 1` and `c` with `0 < a + c` and `b + c < 1`,
  `Int.fract y ∈ [a, b) ↔ Int.fract (y + c) ∈ [a + c, b + c)`;
* `countIn_add_const` — hence the counting function is unchanged by the matched translation;
* `tendsto_countIn_div_of_le` — **the counting form for every subinterval of `[0, 1]`**: if `x`
  is equidistributed modulo one and `0 ≤ a < b ≤ 1`, then `countIn x a b N / N → b − a`;
* `tendsto_countIn_div_quadratic_of_le` — the same for `x n = α n²` with `α` irrational.

## Proof

`M1-WEYL-COUNT` needs `0 < a < b < 1` because its trapezoids must avoid the point `0` where
`[0, 1)` is glued into the circle.  The restriction is removed by a rotation.

Translation invariance is immediate from Weyl's criterion (`M1-WEYL-CRITERION`): translating the
sequence by `c` multiplies the exponential sum at frequency `m` by the unimodular constant
`e(m c)`, so the normalized sums have the same norm, and vanishing at every nonzero frequency is
preserved.

For `0 ≤ a < b ≤ 1` with `b − a < 1`, the choice `c = (1 − (b − a))/2 − a` centres the translated
interval: `a + c = (1 − (b − a))/2 > 0` and `b + c = (1 + (b − a))/2 < 1`.  The membership
equivalence is a three-case check on `u = Int.fract y ∈ [0, 1)`: if `u + c ∈ [0, 1)` the
fractional part is `u + c`; the cases `u + c < 0` and `u + c ≥ 1` force `u < b − 1 ≤ 0`
respectively `u ≥ a + 1 ≥ 1`, both impossible.  So the two counting problems are literally the
same finite set, and the previous theorem applies to the translated data.

The remaining case `b − a = 1` forces `a = 0` and `b = 1`, where every term is counted
(`countIn_zero_one`) and the quotient is `1` for every `N ≥ 1`.

## Why this row exists

The open boundary of `M1-WEYL-COUNT` reads: "The interval must satisfy `0 < a < b < 1`: it has to
avoid the point where `[0,1)` is glued into the circle, so an interval containing `0` is not
covered."  This row covers it.

## Scope, and what is *not* claimed

* No rate of convergence: the input carries none, so neither does the conclusion.
* Only intervals of the form `[a, b) ⊆ [0, 1]` are treated; an arc of the circle is described by
  its representative in `[0, 1)`, and the wrap-around arc `[a, 1) ∪ [0, b)` with `b < a` is not
  stated separately (it is the complement of `[b, a)`, but that complement statement is not
  derived here).
* Only the quadratic sequence is applied, and nothing about `ζ` is claimed.

## Adversarial revalidation: M1-WEYL-COUNT-GENERAL

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.WeylCountGeneral` succeeds, the file contains no `sorry`, and it triggers no
  linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `equidistributedMod1_add_const`, `tendsto_countIn_div_of_le` and
  `tendsto_countIn_div_quadratic_of_le` (checked in `scripts/audit.sh`).
* All three are pinned in `scripts/revalidation.lean` with `countIn` written out as the
  cardinality of an explicit `Finset.filter`, so the counting definition cannot be weakened.
* The statement is not vacuous and is strictly stronger than `M1-WEYL-COUNT`: the hypotheses now
  admit `a = 0` and `b = 1`, which the earlier row excluded, and the conclusion at `a = 0`,
  `b = 1/2` is a nontrivial proportion `1/2` rather than the trivial bounds `0 ≤ · ≤ 1`.
* The conclusion still fails for sequences that are not equidistributed — for a constant sequence
  the quotient is `0` or `1` for every `N` — so equidistribution is genuinely used.
* No unproved `Prop` of this repository occurs as a hypothesis; `EquidistributedMod1` is a
  definition, and the headline `tendsto_countIn_div_quadratic_of_le` discharges it, so it is
  unconditional.
