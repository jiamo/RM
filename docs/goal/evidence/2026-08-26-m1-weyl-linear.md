# M1-WEYL-LINEAR — Weyl's theorem for the linear sequence `α n`

Date: 2026-08-26
File: `RiemannHypothesis/WeylLinear.lean`

## Claim

For every irrational `α` the module proves

* `weylSumsVanish_linear` — the exponential sums of `α n` at every nonzero integer frequency `m`
  are bounded by the constant `1/(2‖mα‖)`, uniformly in `N`, hence their normalizations
  `‖∑_{n<N} e(m α n)‖ / N` tend to `0`;
* `equidistributedMod1_linear` — **the fractional parts of `α n` are equidistributed modulo one**;
* `tendsto_countIn_div_linear` — the counting form: for every `0 ≤ a < b ≤ 1`,
  `#{ n < N : Int.fract (α n) ∈ [a, b) } / N → b − a`.

## Proof

The quadratic case `α n²` of `M1-WEYL-CRITERION` needed the van der Corput A process to difference
the phase down to a linear one. The linear case needs none of that machinery: the sum
`∑_{n<N} e(θ n + c)` is geometric, and `M1-WEYL-QUADRATIC` already provides the geometric-series
bound `norm_geomSum_e2pi_le : ‖∑_{j<M} e(θ j + c)‖ ≤ 1/(2‖θ‖)`, where `‖θ‖ = intDist θ` is the
distance of `θ` to the nearest integer, valid whenever `‖θ‖ ≠ 0` and uniform in `M`.

For a nonzero integer `m`, `m α` is irrational (`Irrational.intCast_mul`), so
`intDist_pos_of_irrational` gives `‖mα‖ > 0`. Rewriting `m * (α * n)` as `(m α) * n + 0`, the sum
at frequency `m` is exactly a geometric sum, so it is bounded by `C = 1/(2‖mα‖)` for every `N`.
Squeezing `0 ≤ ‖∑‖/N ≤ C/N` against `C/N → 0` gives `WeylSumsVanish`.

Weyl's criterion (`equidistributedMod1_iff_weylSumsVanish`) then yields equidistribution, and
`tendsto_countIn_div_of_le` of `M1-WEYL-COUNT-GENERAL` yields the counting form for every
subinterval of `[0, 1]`, including those with an endpoint at `0` or at `1`.

## Scope, and what is *not* claimed

* No rate of convergence. The bound `1/(2‖mα‖)` is uniform in `N` but depends on the Diophantine
  quality of `α`, and nothing is assumed about that quality, so no effective statement follows.
* Irrationality is necessary, not merely convenient: for rational `α` the fractional parts of
  `α n` take finitely many values and are not equidistributed.
* Nothing here concerns `ζ`; the row is part of the equidistribution track only.

## Adversarial revalidation: M1-WEYL-LINEAR

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylLinear`
  succeeds, the file contains no `sorry`, and it triggers no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `weylSumsVanish_linear`, `equidistributedMod1_linear` and `tendsto_countIn_div_linear`
  (checked in `scripts/audit.sh`).
* `equidistributedMod1_linear` and `tendsto_countIn_div_linear` are pinned in
  `scripts/revalidation.lean`; the counting statement is written out with `countIn` unfolded to
  the cardinality of an explicit `Finset.filter`, so the counting definition cannot be weakened.
* The statement is not vacuous: irrational numbers exist (`irrational_sqrt_two`), and at
  `a = 0, b = 1/2` the conclusion is the nontrivial proportion `1/2`, not the trivial bounds
  `0 ≤ · ≤ 1`.
* The irrationality hypothesis is load-bearing: for `α` rational the conclusion is false, and the
  repository already records the corresponding failure for a constant sequence
  (`not_equidistributedMod1_const_zero`).
* No unproved `Prop` of this repository occurs as a hypothesis, so the results are unconditional.
