# M1-ZERO-MULTIPLICITY — the multiplicity of a nontrivial zero is `O(log |gamma|)`

Date: 2026-08-23
Modules: `RiemannHypothesis/MultiplicityCountingLemma.lean`,
`RiemannHypothesis/ZeroMultiplicityBound.lean` (both imported by `RiemannHypothesis.lean`),
with small refactors of `RiemannHypothesis/ZeroCountLocal.lean` and
`RiemannHypothesis/ZeroCount.lean`.

## Why this row exists

Every counting result in the repository so far counts zeroes *without* multiplicity:
`ncard_nontrivialZeros_le` (`N(T) = O(T log T)`) and `ncard_zerosNearHeight_le`
(`O(log T)` zeroes in a unit-height window) are statements about the cardinality of a *set* of
points.  The counting function *with* multiplicity, `multCount`, was defined in
`RiemannHypothesis/ZeroMultiplicitySymmetry.lean` and its symmetry properties were proved there,
but nothing bounded it — indeed nothing in the repository excluded a nontrivial zero of enormous
order.  This row closes that gap.

## What is proved

`RiemannHypothesis/MultiplicityCountingLemma.lean` (general complex analysis, no zeta):

* `exists_divided` — if `f` is holomorphic on `B(c, R)`, continuous on the closed ball, and
  vanishes to order at least `m` at a point `a` of the ball, then `f / (· − a) ^ m` extends to a
  function with the same regularity.  The hypothesis `(m : ℕ∞) ≤ analyticOrderAt f a` gives a
  local factorization `f = (· − a) ^ m • g`, so the quotient extends holomorphically across `a`.
* `pow_three_sum_mul_norm_le` — the main estimate, for a *finite set* of zeroes counted with
  multiplicity: if `‖f‖ ≤ M` on the circle `‖z − c‖ = R` and `f` vanishes to order at least
  `m a` at each point `a` of a finite set `S` with `dist a c ≤ R/4`, then
  `3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M`.  The proof is an induction on `S`: dividing out one point
  with its full multiplicity gives `G` with `‖G‖ ≤ M / (3R/4) ^ m a` on the circle, while
  `‖G c‖ = ‖f c‖ / ‖c − a‖ ^ m a ≥ ‖f c‖ / (R/4) ^ m a`, so each point improves the ratio
  `M / ‖f c‖` by a factor `3 ^ m a`; the orders of the remaining points are unchanged by the
  division.  No use is made of Jensen's formula.
* `pow_three_pow_mul_norm_le` — the single-point case `S = {a}`: `3 ^ m * ‖f c‖ ≤ M`.
* `analyticOrder_le_log_div_log_three`, `sum_analyticOrder_le_log_div_log_three` — the
  logarithmic forms, bounding the (total) order by `log (M / ‖f c‖) / log 3`.

`RiemannHypothesis/ZeroCountLocal.lean` and `RiemannHypothesis/ZeroCount.lean` (refactors, no
change of statements):

* `exists_disc_data_near_height` — for `T ≥ 25` there is a bound `M` for `ξ` on the circle of
  radius `20` about `c = 4 + i T`, with `ξ(c) ≠ 0` and `log (M / ‖ξ(c)‖) ≤ 41 log T`.  This was
  the first half of the proof of `ncard_zerosNearHeight_le`, which now uses it; the multiplicity
  bound below uses the same disc.
* `exists_global_disc_bound` — for `T ≥ 2` there is a bound `M` for `ξ` on the circle of radius
  `4 (T + 2)` about `s = 2` with `log (M / ‖ξ(2)‖) / log 3 ≤ A T log T` for an absolute `A`.
  This was the first half of the proof of `ncard_nontrivialZeros_le`, which now uses it; the
  global multiplicity count below uses the same disc, which is why it comes out at the same
  order.

`RiemannHypothesis/ZeroMultiplicityBound.lean` (application to `ζ`):

* `analyticOrderAt_xiFn_eq` — inside the critical strip `ξ` and `ζ` vanish to the same order:
  they differ by `s (s − 1) / 2`, nonzero there, and by the nonvanishing factor `Γ_ℝ` already
  handled in `analyticOrderAt_completedRiemannZeta_eq`.
* `zeroMultiplicity_le_of_mem_zerosNearHeight` — a zero of `ζ` in the strip whose height differs
  from `T ≥ 25` by at most `1` has multiplicity at most `41 log T`.
* `zeroMultiplicity_le_log_abs_im` — **the classical bound**: a nontrivial zero `ρ` with
  `|im ρ| ≥ 25` has `zeroMultiplicity ρ ≤ 41 log |im ρ|`.  Zeroes below the real axis are reduced
  to the ones above it by `zeroMultiplicity_conj`.
* `exists_zeroMultiplicity_bound_low` — the multiplicities of the zeroes of height at most `25`
  are bounded by an absolute constant (they all lie in the single disc of radius `50` about
  `s = 2`, where the growth bound `norm_xiFn_le` applies).
* `exists_zeroMultiplicity_bound` — combining the two: an absolute `K` with
  `zeroMultiplicity ρ ≤ K log T` for every nontrivial zero of height at most `T`, `T ≥ 25`.
* `finite_zerosNearHeight` — the zeroes in a unit-height window are finitely many.
* `sum_zeroMultiplicity_zerosNearHeight_le` — **the local count with multiplicity**: for
  `T ≥ 25`, `∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ ≤ 41 log T`, the same bound as the
  count of *distinct* zeroes in the window.
* `multCount_le` — **Riemann–von Mangoldt with multiplicity**: there is an absolute `C > 0` with
  `multCount T ≤ C · T · log T` for all `T ≥ 2` — the same order as the count without
  multiplicity, with the same constant produced by `exists_global_disc_bound`.

## Scope, stated plainly

* Nothing here decides the Riemann hypothesis, and nothing here produces a zero of high
  multiplicity — the results are upper bounds.
* The multiplicity bound `O(log |γ|)` is the classical one and is not known to be improvable; no
  zero of `ζ` is known to be multiple.
* `multCount T = O(T log T)` is the correct order of magnitude, but only as an upper bound with
  a non-explicit constant: the true asymptotic `N(T) ~ (T/2π) log(T/2π)` — in particular the
  matching lower bound and the value of the constant — is not proved here.
* The constants (`41`, and the constant `K` for the low zeroes) are not optimized; the constant
  for the low zeroes is not explicit, because `norm_xiFn_le` has a non-explicit constant.
* No `sorry`; `#print axioms` on each result above yields exactly `propext`, `Classical.choice`,
  `Quot.sound` (checked in `scripts/audit.sh`).

## Adversarial revalidation: M1-ZERO-MULTIPLICITY

Each exit criterion is pinned in `scripts/revalidation.lean` (section `M1-ZERO-MULTIPLICITY`) by
an `example` whose statement is written out in full and whose proof is the repository's
declaration, so a weakening or renaming breaks the audit:

* the general disc estimate in all four forms (`exists_divided`, `pow_three_sum_mul_norm_le`,
  `pow_three_pow_mul_norm_le`, `analyticOrder_le_log_div_log_three`,
  `sum_analyticOrder_le_log_div_log_three`), with the order hypothesis stated as
  `(m : ℕ∞) ≤ analyticOrderAt f a` — the mathlib notion, not a repository-local one;
* the two disc-data lemmas `exists_disc_data_near_height` and `exists_global_disc_bound`, so the
  refactors of the earlier counting rows cannot weaken what those rows supply;
* `analyticOrderAt_xiFn_eq : analyticOrderAt xiFn s = analyticOrderAt riemannZeta s` in the
  strip, so the passage from `ζ` to `ξ` cannot silently change the multiplicity;
* `zeroMultiplicity_le_of_mem_zerosNearHeight`, `zeroMultiplicity_le_log_abs_im`,
  `exists_zeroMultiplicity_bound_low`, `exists_zeroMultiplicity_bound`,
  `finite_zerosNearHeight`, `sum_zeroMultiplicity_zerosNearHeight_le`, `multCount_le`, each with
  the quantifiers and constants as stated.

`zeroMultiplicity` is the repository's existing definition
`(analyticOrderAt riemannZeta ρ).toNat` from `RiemannHypothesis/Zeta23Bridge.lean` and
`multCount T = ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ` is the existing definition from
`RiemannHypothesis/ZeroMultiplicitySymmetry.lean`; neither was modified for this row, so the
bounds are bounds on the objects the earlier rows already used.

Counter-check on the claim: the statements are upper bounds on a nonnegative quantity, so they
cannot be met by making the quantity vacuous — `multCount` is pinned definitionally elsewhere in
the same file and its symmetry results (`multCount_eq_two_mul`, `even_multCount`) show it is not
identically zero for large `T`.

Checks run: `lake build`, `lake build RiemannHypothesis.MultiplicityCountingLemma`,
`lake build RiemannHypothesis.ZeroMultiplicityBound`, `./scripts/audit.sh` (no `sorry` outside
`Challenge.lean`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`, no `Float`),
`python3 scripts/goal_state.py validate`.
