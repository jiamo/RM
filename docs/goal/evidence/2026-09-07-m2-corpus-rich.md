# A thicker corpus, and the same ceiling

Date: 2026-09-07
Modules: `RiemannHypothesis/CorpusRich.lean`, `RiemannHypothesis/CorpusRichInstance.lean`

## Why

`M2-CORPUS-CEILING` and `M2-CORPUS-INSTANCE` prove that the Riemann hypothesis is not derivable
from the list of unconditional facts collected in `ZeroCorpus`, and that the zeroes of `ζ`
satisfy that list.  The force of such a negative result is proportional to the richness of the
list: a short list is easy to satisfy, so its independence result says little.  The list
collected so far had five facts — the mollifier proportion, Riemann–von Mangoldt, the Carlson
density theorem, the quadruple symmetry, the multiplicity bound, the zero-free region.  This row
adds four more, each already a theorem of the repository, and re-proves the ceiling against the
longer list.

## What is added

`RichZeroCorpus θ` extends `ZeroCorpus θ` by

* `simpleOnLine`, `simpleOnLine_nonneg`, `simpleOnLine_le_onLine`, `window_simpleOnLine` — a
  *fifth counting function*, the zeroes that are simple **and** on the critical line, subject to
  the same `1 − θ` proportion of a dyadic window.  Repository:
  `sixty_seven_percent_simple_on_critical_line`.
* `distinct_ratio` — Theorem C: at least `5/6 − ε` of the zeroes of a dyadic window, counted
  with multiplicity, are distinct.  Repository: `five_sixths_distinct`.  The plain corpus knew
  only `N_d ≤ N` and the `O(log T)` factor of `mult`.
* `localCount` — the local Riemann–von Mangoldt bound `N(T+1) − N(T) = O(log T)`.  Repository:
  `sum_zeroMultiplicity_zerosNearHeight_le`.  The global asymptotic of the field `rvm`, whose
  error term is `O(T + log² T)`, does not imply it.
* `strip` — no nontrivial zero at distance `1/2` or more from the critical line, at *every*
  height; the field `zeroFree` of the plain corpus is asymptotic.

## What is proved

* `rvmModel_unit_window_le` — the model count grows by at most `log T` over a unit window, the
  one new estimate the model needs (`log(1 + 1/T) ≤ 1/T` and `2π > 6`).
* `richModelCorpus` — the configuration of `modelCorpus`, with a positive proportion of its
  zeroes off the critical line, satisfies all four new facts.
* `rh_not_derivable_from_rich_corpus`, `rich_offLine_positive_proportion_consistent`,
  `rich_density_not_sufficient` — the earlier independence results, against the longer list.
* `rich_corpus_window_ceiling` — the ceiling is unchanged: a proportion `p` on the critical line
  is derivable from the enlarged list **iff** `p ≤ 1 − θ`.
* `windowCountSimpleOnLine_add`, `windowCount_unit_window_le`, `offAtSet_half_eq_empty` — the
  bookkeeping needed for `ζ`.
* `zetaRichCorpus : RichZeroCorpus 0.33` — the instance, every field discharged from a theorem
  of this repository.
* `rh_not_derivable_from_zeta_rich_corpus`, `zeta_rich_corpus_window_ceiling` — the consequences
  for `ζ`: the enlarged list, which `ζ` provably satisfies, entails `67 %` on the critical line
  and nothing more, and does not entail the conjecture.

## Scope

Exactly as in `M2-CORPUS-CEILING`: these are theorems about what a fixed list of inequalities
between counting functions can prove, not evidence about the Riemann hypothesis.  The statement
that is strengthened is the *negative* one, and it is strengthened in the only way available —
by making the list of facts longer.

## Adversarial revalidation: M2-CORPUS-RICH

* *Are the new fields really new, or consequences of the old ones?*  `localCount` is not implied by
  `rvm`, whose error term dwarfs a unit window; `distinct_ratio` is not implied by
  `distinct_le_total` and `mult`; `strip` is not implied by `zeroFree`, which only speaks of
  large `T`; and `simpleOnLine` is a new function, so no field of `ZeroCorpus` mentions it.
* *Is the instance real?*  Every field of `zetaRichCorpus` is discharged from a named theorem
  about `ζ`; the file adds the three missing bookkeeping lemmas rather than assuming them.
* *Is the ceiling theorem weaker than it looks?*  Its `←` direction is inherited from
  `corpus_window_ceiling` (a rich corpus is a corpus), and its `→` direction is proved against
  the *rich* models, which is the direction that gets harder as the list grows.
* *Axioms.*  `#print axioms` on `rh_not_derivable_from_zeta_rich_corpus` and
  `rich_corpus_window_ceiling` gives exactly `propext`, `Classical.choice`, `Quot.sound`.
