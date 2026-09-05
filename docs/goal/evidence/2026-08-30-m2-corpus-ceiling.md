# M2-CORPUS-CEILING — the ceiling of the whole corpus, as theorems

Date: 2026-08-30
File: `RiemannHypothesis/CorpusCeiling.lean`
Related: `RiemannHypothesis/MethodCeiling.lean` (the ceiling of a single counting route),
`RiemannHypothesis/SixtySevenPercent.lean`, `RiemannHypothesis/RvMCumulative.lean`,
`RiemannHypothesis/CarlsonDensityPowerSaving.lean`, `RiemannHypothesis/OffLineQuadruple.lean`,
`RiemannHypothesis/ZeroMultiplicityBound.lean`

## Claim

`MethodCeiling` computed the ceiling of *one* route.  This row does the same for the repository's
whole stock of unconditional facts about the distribution of the zeroes, taken together.

`ZeroCorpus θ` is the counting data of the zeroes — the cumulative counts over `(0, T]` of all
zeroes with multiplicity (`total`), of the distinct ones (`distinct`), of the on-line and the
off-line ones (`onLine`, `off`), and of the off-line ones at distance at least `δ` from the
critical line (`offAt δ`) — with one field for each fact:

| field | repository theorem |
| --- | --- |
| `window_onLine` | `sixty_seven_percent_on_critical_line` (`θ = 0.33`) |
| `rvm` | `exists_abs_windowCount_zero_sub_main_le` |
| `density` | `exists_ncard_zerosOffCriticalLine_le_rpow` |
| `off_even`, `offAt_even` | `ncard_upperOffLineNontrivialZeros_eq_two_mul` |
| `mult` | `zeroMultiplicity_le_log_abs_im`, `multCount_le` |
| `zeroFree` | the classical zero-free region |
| the shape fields | `windowCount_mono`, `windowCountOffLine_add_windowCountOnLine` |

Three theorems are proved about that system.

1. **Soundness** (`ZeroCorpus.windowOff_le`): in any corpus the off-line count of a dyadic window
   is eventually at most `θ` times its total count.
2. **The exact ceiling** (`corpus_window_ceiling`):

       (∀ Z : ZeroCorpus θ, eventually p·N(T,2T) ≤ N₀(T,2T)) ↔ p ≤ 1 − θ.

   The `←` direction is soundness; the `→` direction is a saturating witness, the family
   `modelCorpus θ r`, defined for every rate `r < θ`.  With the repository's own `θ = 0.33` the
   ceiling is exactly the `67 %` that `sixty_seven_percent_on_critical_line` already proves.  So
   the Riemann–von Mangoldt formula, the Carlson power saving, the quadruple symmetry, the
   multiplicity bound and the zero-free region contribute **nothing** to the proportion beyond
   the mollifier; only a new mollifier fact can move it.
3. **Non-derivability of the conjecture** (`rh_not_derivable_from_corpus`,
   `offLine_positive_proportion_consistent`, `density_not_sufficient`): the witness satisfies
   every field of the corpus and has a positive off-line count — in fact eventually at least
   `q·N(T,2T)` off-line zeroes for any prescribed `q < 0.33`.  Its off-line zeroes crowd towards
   the critical line as the ordinate grows, so for each fixed `δ > 0` the count `offAt δ` is
   **bounded in `T`**: the model satisfies not only the Carlson power saving but any density
   statement at a fixed `δ`, however strong, including one uniform in the height.

4. **What a full-strength density hypothesis would contribute** (`off_le_of_uniformDensity`,
   `uniformDensity_not_sufficient`): grant the density bound *uniformly in `δ`* — strictly
   stronger than the density hypothesis, and beyond any known method.  Because the off-line
   count of a height is attained at some positive distance (`off_attained`, from the finiteness
   of the zero set below a height), it then gives a power saving `N_off(T) = O(T^(1−c))` for the
   whole off-line count.  It still does not give the conjecture: `constOffCorpus` satisfies every
   field of the corpus and the uniform bound, with two zeroes off the critical line at distance
   `1/6`.

The last point is the precise form of the sentence "the density route does not converge to RH":
what defeats it is not the size of the exponent but the order of the quantifiers — every density
theorem fixes `δ` first, and the conjecture is the limit `δ → 0`.

## Scope

Nothing here is a statement about `ζ`.  As in `MethodCeiling`, these are theorems about what can
and cannot be deduced from a fixed list of inequalities between counting functions.  The value is
negative and precise: any route that uses only the listed facts stops at `1 − θ`, so progress
requires a new *fact*.  The result does not say that RH is false, nor that it is unprovable; it
says that the repository's present corpus, as abstracted here, has a model in which it fails.

The abstraction is by hand: each field is the statement of a named repository theorem transcribed
into the vocabulary of abstract counting functions, and the correspondence is recorded in the
table above rather than checked by Lean.  Building the instance `ZeroCorpus 0.33` from the `ζ`
counting functions themselves is the natural follow-up and is recorded as the open boundary of
this row.

## Adversarial revalidation: M2-CORPUS-CEILING

* `lake build RiemannHypothesis.CorpusCeiling` succeeds with no warning, and the file contains no
  `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `corpus_window_ceiling`, `rh_not_derivable_from_corpus`, `density_not_sufficient`,
  `offLine_positive_proportion_consistent`, `off_le_of_uniformDensity`,
  `uniformDensity_not_sufficient`, `ZeroCorpus.windowOff_le`, `modelCorpus` and
  `constOffCorpus`.
* The theorems are not vacuous: `ZeroCorpus θ` is inhabited for every `0 < r < θ ≤ 1` by
  `modelCorpus θ r`, whose every field is discharged, so both directions of the `↔` have content
  and the non-derivability statements are witnessed rather than argued.
* No statement about `ζ` is made or used: the module imports only Mathlib.  Two entries appear in
  `docs/goal/conditional-theorems.txt`, `rh_not_derivable_from_corpus <- RHCounts` and
  `off_le_of_uniformDensity <- UniformDensity`, both classified `DEFINITIONAL`: each is a
  property of the abstract corpus `Z` supplied as an argument, not an assumption about `ζ`.
* Caveat on the gates: in the environment in which this row was produced the pinned Mathlib
  differs from the one recorded in `lakefile.toml`, so the modules that predate this row do not
  all compile and `./scripts/audit.sh` cannot be run end to end.  The manifest line above was
  added by hand and should be regenerated with
  `lake env lean scripts/conditional_theorems.lean` once the tree builds again.
