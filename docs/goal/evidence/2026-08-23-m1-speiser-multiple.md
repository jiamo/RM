# M1-SPEISER-MULTIPLE — the multiple-zero half of Speiser's transfer

Date: 2026-08-23
Module: `RiemannHypothesis/SpeiserMultiple.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

Everything in this file is unconditional.

* `analyticOrderAt_xiDerivFn_add_one` — at a zero `ρ` of `ζ` in the open critical strip,
  `ord_{ξ′}(ρ) + 1 = ord_ζ(ρ)`.  The proof is local: `ξ` is entire, inside the strip it vanishes
  exactly where `ζ` does and to the same order (`analyticOrderAt_xiFn_eq`, from
  M1-ZERO-MULTIPLICITY), and differentiating an analytic function drops the vanishing order by
  exactly one (`AnalyticAt.analyticOrderAt_deriv_add_one`).
* `xiDerivMultiplicity_add_one` — the same statement in terms of the `ℕ`-valued multiplicities,
  `m_{ξ′}(ρ) + 1 = m_ζ(ρ)`.
* `xiDerivFn_eq_zero_of_multiple` — hence a *multiple* nontrivial zero of `ζ` is a zero of `ξ′`,
  at the same point and therefore on the same side of the critical line.
* `xiDerivFn_ne_zero_of_simple` — the converse boundary: a *simple* nontrivial zero of `ζ` is not
  a zero of `ξ′`.  This is what shows that the local argument cannot reach the simple zeroes, and
  hence why the counting form of Speiser's theorem needs a global (argument-principle) input.
* `windowZerosOffLineMultiple_subset` and `ncard_windowZerosOffLineMultiple_le` — the set form and
  the counting form of the transfer for the multiple zeroes.
* `ncard_windowZerosOffLineMultiple_le_bad` — the number of multiple off-line zeroes of `ζ` in a
  window is at most the `ξ′` bad count `N_{ξ′} − N₀ˢ_{ξ′}` of that window.  This is exactly the
  inequality that the unproved `Prop` `SpeiserTransfer` asserts for *all* the off-line zeroes,
  and it is obtained here for the multiple ones with no `O(log T)` error term.
* `ncard_windowZerosOffLineMultiple_le_windowCount` — combining with the new unconditional
  `xiDerivWindowCountBad_le` of `RiemannHypothesis/EightyPercentRoute.lean`: for every `ε > 0` and
  all large `T`, at most `(0.13136 + ε) · N(T, 2T)` of the zeroes of `ζ` in the dyadic window are
  both multiple and off the critical line.

* `windowMultipleOffLineExcess`, `windowMultipleOffLineExcess_le_bad` and
  `windowMultipleOffLineExcess_le_windowCount` — the multiplicity-weighted form.  Since
  `m_{ξ′}(ρ) = m_ζ(ρ) − 1` exactly, the off-line `ξ′` zeroes can be counted *with* multiplicity
  (`sum_xiDerivMultiplicity_offLine_add_simpleOnLine_le`, which strengthens
  `ncard_xiDerivWindowZerosOffLine_add_simpleOnLine_le` and now implies it), and the two bounds
  above hold with each multiple off-line zero of `ζ` weighted by its excess multiplicity
  `m_ζ(ρ) − 1` instead of counted once.

## Relation to M1-EIGHTY-CRITICAL-ROUTE

That row records `SpeiserTransfer` as an unproved `Prop` and derives the 84 % / 70 % consequences
from it.  The present row proves, without hypothesis, the part of `SpeiserTransfer` that is local:
the part carried by the multiple zeroes.  It does **not** prove `SpeiserTransfer`, and none of the
conditional consequences on that row become unconditional.

## Scope — what is *not* claimed

* `SpeiserTransfer` is still unproved.  Its content is the transfer for the *simple* off-line
  zeroes, and `xiDerivFn_ne_zero_of_simple` shows that no local argument can supply it.
* The `13.136 %` bound here is for the zeroes that are *both* multiple *and* off the critical
  line.  The unconditional proportion of zeroes known to lie off the critical line is unchanged
  (M1-SIXTY-SEVEN-CRITICAL: at most 33 %).
* Nothing here bears on the Riemann Hypothesis.

## Gates

* `lake build RiemannHypothesis.SpeiserMultiple` — succeeds, no `sorry`.
* `bash scripts/audit.sh` — `OK`; the claims are pinned in `scripts/revalidation.lean` and the
  axioms are checked there.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-SPEISER-MULTIPLE

A second pass, made against the compiled module rather than against this note.

* **Is it vacuous?**  The counting statements are not: `windowZerosOffLineMultiple T₁ T₂` is a
  subset of a set that is known to be finite and the bound is a genuine numerical inequality.  It
  is however *conditionally empty* in a sense worth stating plainly: if RH and the simplicity
  conjecture hold the set is empty, so the theorem has no unconditional lower-bound content.  It
  is an upper bound, and it is the upper bound `SpeiserTransfer` would give, restricted to the
  multiple zeroes.  The pointwise statements `xiDerivMultiplicity_add_one` and
  `xiDerivFn_ne_zero_of_simple` have hypotheses (`riemannZeta s = 0`, `0 < Re s < 1`) that are
  satisfied by the first nontrivial zero at height `14.13…`, so they are not vacuous.
* **Is the order computation legitimate?**  `analyticOrderAt_xiDerivFn_add_one` uses
  `AnalyticAt.analyticOrderAt_deriv_add_one` from mathlib, which requires only analyticity at the
  point; `differentiable_xiFn` supplies it.  The rewrite by `xiFn s = 0` is justified by
  `xiFn_eq_zero_of_zeta`, which needs `0 < Re s < 1` — present as a hypothesis.  Finiteness of the
  order (needed to pass from `ℕ∞` to `ℕ`) comes from `analyticOrderAt_ne_top` applied to
  `xiFn_two_ne_zero`, so no `⊤` is silently coerced to `0`.
* **Does the counting step double-count?**  No: `ncard_xiDerivWindowZerosOffLine_add_simpleOnLine_le`
  adds the off-line `ξ′` zeroes to the simple on-line ones inside `N_{ξ′}`, and the two sets are
  disjoint by the `Re ρ = 1/2` predicate.  The finiteness side conditions are discharged by
  `xiDerivWindowZeros_finite`.
* **Does it depend on anything unproved?**  No.  In particular it does not use `SpeiserTransfer`;
  `#print axioms` on each theorem returns exactly `propext`, `Classical.choice`, `Quot.sound`.
* **Proof hygiene.**  No `sorry`, `axiom`, `native_decide` or `implemented_by`.
* **Is the weighted form really stronger?**  Yes, and not vacuously: on
  `windowZerosOffLineMultiple` every zero has `m_ζ(ρ) ≥ 2`, so its weight `m_ζ(ρ) − 1` is at
  least one and `windowMultipleOffLineExcess` dominates the plain cardinality.  The natural
  subtraction `m_ζ(ρ) − 1` is not a truncation hazard here for the same reason.
* **Duplication check.**  `analyticOrderAt_xiFn_eq` is *not* redeclared here; the module imports
  `RiemannHypothesis.ZeroMultiplicityBound` and reuses that lemma.
