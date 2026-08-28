# M1-WEYL-COUNT — equidistribution modulo one in its counting form

Date: 2026-08-26
File: `RiemannHypothesis/WeylCount.lean`

## Claim

For a real sequence `x : ℕ → ℝ` and `0 < a < b < 1`, write

    countIn x a b N = #{ n < N : Int.fract (x n) ∈ [a, b) }.

The module proves

* `tendsto_avg_real` — equidistribution tested against *real*-valued continuous functions on the
  circle (the complex statement of `M1-WEYL-CRITERION` restricted to real test functions);
* `tendsto_countIn_div` — **the counting form**: if `x` is equidistributed modulo one, then
  `countIn x a b N / N → b − a`;
* `tendsto_countIn_div_quadratic` — **Weyl's theorem for `α n²` in its classical form**: for
  every irrational `α`,

      #{ n < N : {α n²} ∈ [a, b) } / N → b − a .

## Proof

The indicator of `[a, b)` is squeezed between two trapezoids (`trap u v η`, equal to `1` on
`[u, v]`, `0` off `(u − η, v + η)`, linear in between):

* the lower one, `trap (a + η) (b − η) η`, is supported in `[a, b]` and hence is `≤` the
  indicator;
* the upper one, `trap a b η`, is `1` on `[a, b]` and hence is `≥` the indicator.

For `η` small enough both supports lie inside `(0, 1)`, so each descends to a *continuous*
function on the circle (`trapCirc`, via `AddCircle.liftIco_zero_continuous`; the value at the
glueing point `0` is `0` on both sides).  A real number and its fractional part have the same
image in the circle (`coe_eq_coe_fract`), so evaluating the descended trapezoid along the sequence
evaluates the trapezoid at the fractional parts, and the averages are squeezed accordingly.

The means are computed by pulling the circle integral back to `[0, 1]`
(`integral_trapCirc_eq`) and splitting the interval: `b − a ≤ ∫ trapCirc ≤ b − a + 2η` for the
upper trapezoid and `b − a − 2η ≤ ∫ trapCirc` for the lower one (`integral_trapCirc_le`,
`le_integral_trapCirc`).  Equidistribution moves each average to within `ε/4` of its mean, and
`η` is chosen with `4η < ε`, so the counting quotient is caught within `ε` of `b − a`.

## Why this row exists

`M1-WEYL-CRITERION` states equidistribution against continuous test functions and records in its
open boundary that the counting statement — the classical formulation, "the proportion of terms
landing in a subinterval tends to its length" — is not derived.  This row derives it.

## Scope, and what is *not* claimed

* The interval is required to satisfy `0 < a < b < 1`: it must avoid the point where `[0, 1)` is
  glued into the circle.  The statement for an interval containing `0`, or for the whole circle
  minus a point, is not derived.
* No rate of convergence is claimed; the input carries none.
* Only the quadratic sequence is applied, and nothing about `ζ` is claimed.

## Adversarial revalidation: M1-WEYL-COUNT

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylCount`
  succeeds, the file contains no `sorry`, and it triggers no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements (checked in `scripts/audit.sh`).
* Both counting statements are pinned in `scripts/revalidation.lean` with `countIn` written out
  as the cardinality of an explicit `Finset.filter`, so the definition cannot be weakened.
* The statement is not vacuous: the hypotheses `0 < a < b < 1` are satisfiable (`a = 1/4`,
  `b = 1/2`), the conclusion `b − a` is a nonzero proportion, and the sequences it applies to
  exist — `Irrational (√2)` is available in mathlib.
* The conclusion is a genuine restriction: the trivial bounds are `0 ≤ countIn/N ≤ 1`, whereas
  the theorem pins the limit at the exact value `b − a`; and it fails for sequences that are not
  equidistributed, for instance a constant sequence, whose quotient is `0` or `1` for every `N`.
* No unproved `Prop` of this repository occurs as a hypothesis.  The manifest
  `docs/goal/conditional-theorems.txt` records `tendsto_countIn_div <- EquidistributedMod1` and
  `tendsto_avg_real <- EquidistributedMod1`, but `EquidistributedMod1` is a definition, and the
  headline `tendsto_countIn_div_quadratic` discharges it, so it is unconditional.
