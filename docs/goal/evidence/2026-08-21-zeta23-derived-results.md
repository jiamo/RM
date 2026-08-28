# Evidence: the results carried by the vendored `Zeta23` library (2026-08-21)

Rows: `M1-TWO-THIRDS` (new), `M1-HARDY`, `M1-PNT`, `M1-EXPLICIT`, `M2-SELBERG`, `M2-LEVINSON`,
`M2-CONREY` — all moved to `DONE_STRONG`.

## Why these rows moved

The repository vendors, under `vendor/zeta23` (Apache 2.0; see `vendor/zeta23/NOTICE`), the
`Zeta23` library: the formalization of *"More than two thirds of the zeros of the Riemann zeta
function are simple and on the critical line"*, together with a port of the prime number theorem
with error term from the *PrimeNumberTheoremAnd* project. The repository's own modules

* `RiemannHypothesis/Zeta23Bridge.lean`,
* `RiemannHypothesis/CriticalLine.lean`,
* `RiemannHypothesis/EightyPercent.lean`,
* `RiemannHypothesis/PrimeNumberTheorem.lean`,
* `RiemannHypothesis/ExplicitFormula.lean`,
* `RiemannHypothesis/PartialProved.lean`

restate those results in this repository's vocabulary and draw their consequences. The task-board
rows above were written before that material was present and still described the results as open;
this file records the audit that moves them, and nothing in the Lean sources was changed to do so.

**Provenance, stated plainly.** None of the deep analytic work behind these rows was carried out
in this repository: it comes from the vendored library, which is attributed in every module that
uses it. What this repository adds is the restatement in its own definitions, the derivations of
the classical corollaries below, and the audit (`#print axioms`, statement pins) that they are
sorry-free.

## What is proved (no `sorry`; axioms exactly `propext`, `Classical.choice`, `Quot.sound`)

Counting is over `nontrivialZeroSet = {ρ | ζ ρ = 0, 0 < re ρ < 1}` in the window `T₁ < im ρ ≤ T₂`:
`windowCount` counts with multiplicity, `windowCountDistinct` counts distinct points,
`windowCountOnLine` counts distinct points on the line `re ρ = 1/2`, and
`windowCountSimpleOnLine` counts the simple ones among those.

`M1-TWO-THIRDS` — `RiemannHypothesis/Zeta23Bridge.lean`, `RiemannHypothesis/EightyPercent.lean`:

* `two_thirds_on_critical_line`, `two_thirds_on_critical_line_cumulative`: for every `ε > 0` and
  all large `T`, `(2/3 − ε)·N(T, 2T) ≤ N₀*(T, 2T)` and the same over `(0, T]`;
* `two_thirds_simple_on_critical_line(_cumulative)`: the same with the zeroes on the line
  additionally *simple*;
* `five_sixths_distinct(_cumulative)`: at least five sixths of the zeroes are distinct;
* `montgomery_taylor_*`: the optimal-window forms, with the constant `mtConstant`;
* `dirichlet_*`: the same four statements for a primitive Dirichlet `L`-function;
* `eighty_percent_distinct`, `eighty_percent_simple_on_line_xiDeriv`: the `4/5` and `ξ'` forms.

`M1-HARDY` — `RiemannHypothesis/CriticalLine.lean`, `RiemannHypothesis/PartialProved.lean`:

* `tendsto_windowCount_atTop`, `tendsto_windowCountOnLine_atTop`,
  `tendsto_windowCountSimpleOnLine_atTop`: the three counts diverge;
* `infinite_criticalLineZeroSet`: **Hardy's theorem** — `ζ` has infinitely many zeroes on the
  critical line; `infinite_simpleCriticalLineZeroSet`: infinitely many of them are simple;
* `hardyTheorem : HardyTheorem`, discharging the `Prop` stated in `RiemannHypothesis/Partial.lean`
  (the exit criterion of the row).

`M2-SELBERG`, `M2-LEVINSON`, `M2-CONREY` — `RiemannHypothesis/CriticalLine.lean`,
`RiemannHypothesis/PartialProved.lean`:

* `selberg_positive_proportion`, `positiveProportionOnCriticalLine : PositiveProportionOnCriticalLine`;
* `levinson_one_third`, `oneThirdOnCriticalLine`;
* `conrey_two_fifths`, `twoFifthsOnCriticalLine : TwoFifthsOnCriticalLine`;
* `twoThirds_le_liminf_criticalZeroCount_div`, from which the three proportions follow.

`M1-PNT` — `RiemannHypothesis/PrimeNumberTheorem.lean`:

* `chebyshev_psi_sub_id_isBigO`: `ψ(x) − x = O(x·exp(−c(log x)^{1/10}))` for some `c > 0`;
* `chebyshev_psi_sub_id_isLittleO`, `chebyshev_psi_div_tendsto_one`, and
  `chebyshev_theta_div_tendsto_one`;
* `prime_number_theorem`: `π(⌊x⌋)/(x/log x) → 1`, closing the reduction of `M1-PNT-REDUCTION`.

`M1-EXPLICIT` — `RiemannHypothesis/ExplicitFormula.lean`:

* `smoothedChebyshev_eq_vonMangoldt_sum`: Perron's formula in smoothed form — the vertical
  contour integral of `(−ζ'/ζ)(s)·𝓜[ν_ε](s)·X^s` equals `∑ₙ Λ(n)·ν_ε(n/X)`;
* `smoothedChebyshev_sub_chebyshevPsi_bound`: the smoothed sum is within `C·ε·X·log X` of `ψ(X)`;
* `weil_explicit_formula`: the Riemann–von Mangoldt/Weil explicit formula in test-function form,
  including the absolute convergence of the sum over the zeroes.

## Commands run

```
lake build                                  # whole project, succeeds
bash scripts/audit.sh                       # OK
```

`#print axioms` was run on all twenty-one theorems named above (the checks are now part of
`scripts/audit.sh`); each reports exactly `[propext, Classical.choice, Quot.sound]`. A repository
wide search finds no `sorry` outside `Challenge.lean` — in particular none in `vendor/zeta23`,
whose only occurrences of the word are in prose comments describing what was *not* ported.

## What is *not* proved

* **The Riemann hypothesis is not proved.** No term of type `ZetaForm` exists anywhere in the
  repository, and `scripts/audit.sh` checks that none appears. A proportion bound of `2/3`, or
  `4/5` for distinctness, says nothing about the remaining zeroes.
* **The proportions are `liminf` statements** with an `ε` and an unspecified threshold `T₀`; no
  effective height is produced, and none of the counts is evaluated at a concrete `T`.
* **`M1-PNT` carries the vendored error term, not a sharper one**, and the reduction from `ψ` to
  `π` is this repository's (`M1-PNT-REDUCTION`).
* **Perron's formula is the smoothed form**, with a kernel `ν` subject to the stated hypotheses;
  the unsmoothed truncated Perron formula is not proved.

## Adversarial revalidation: M1-TWO-THIRDS

* **Claim mode.** Every statement is a `theorem` with no hypotheses beyond primitivity of the
  character in the Dirichlet case; the statements are pinned in full in `scripts/revalidation.lean`
  with the repository declarations as proof terms, so a later weakening would stop that file
  elaborating.
* **Vacuity check.** The counts are not vacuous: `tendsto_windowCount_atTop` shows the right-hand
  sides are eventually large, so the inequalities have content at infinitely many heights.
* **Definitional check.** `windowCount_eq`, `windowCountOnLine_eq`, `windowCountSimpleOnLine_eq`
  are `rfl`-level bridges to the vendored definitions, so the repository's counting functions are
  literally the ones the vendored theorems are about — the restatement cannot have drifted.
* **Sanity against the literature.** The published results are `2/3` on the line (simple), `5/6`
  distinct, and the Montgomery–Taylor optimal window; the constants pinned here agree.

## Adversarial revalidation: M1-HARDY

* **Claim mode.** `hardyTheorem : HardyTheorem` discharges exactly the `Prop` stated independently
  in `RiemannHypothesis/Partial.lean`, which unfolds to `Infinite {s | ζ s = 0 ∧ re s = 1/2}` —
  the row's exit criterion verbatim.
* **Vacuity check.** `Set.Infinite` is `¬ Finite`, and the proof derives a contradiction from
  finiteness using a *divergent* count, not from an inconsistent hypothesis: the finite cardinal is
  compared with `windowCountOnLine 0 T` for a `T` supplied by `tendsto_windowCountOnLine_atTop`.
* **Is the proof circular?** No: the divergence comes from the Riemann–von Mangoldt count of the
  vendored library and the proportion theorem, neither of which uses Hardy's theorem.
* **Is it really Hardy's theorem?** The statement is the classical one (infinitely many zeroes on
  the line). The *proof* is not Hardy's 1914 argument but a corollary of the proportion theorem;
  this is recorded in the module docstring and in the row's `latest_update`.

## Adversarial revalidation: M1-PNT

* **Claim mode.** `prime_number_theorem` is stated with Mathlib's `Nat.primeCounting` and the
  literal quotient `π(⌊x⌋)/(x/log x) → 1`; it is pinned in `scripts/revalidation.lean`.
* **Vacuity check.** A limit statement cannot be vacuous, and the limit is `1`, not `0`: a
  degenerate reading (e.g. `π(⌊x⌋)/x → 0`) would not elaborate against the pin.
* **Dependency check.** The analytic input is the vendored `MediumPNT`; the passage from `ψ` to
  `θ` to `π` is this repository's `M1-PNT-REDUCTION`, proved earlier by partial summation.
* **Sanity check.** The error term `exp(−c(log x)^{1/10})` is weaker than de la Vallée Poussin's
  `exp(−c√log x)`; the row claims only the asymptotic, which is implied.

## Adversarial revalidation: M1-EXPLICIT

* **Claim mode.** Both Perron statements carry their hypotheses on the smoothing kernel
  explicitly; `weil_explicit_formula` asserts a `Summable` conjunct *and* the identity, so it
  cannot be satisfied by a divergent rearrangement.
* **Vacuity check.** The kernel hypotheses are satisfiable (a standard bump function with
  `∫ ν(x)/x dx = 1` on `[1/2, 2]`), so the statements are not vacuous; the explicit formula holds
  for every `C²` compactly supported `k`, including `k = 0`, which is the degenerate case only.
* **Scope check.** The row's exit criterion asks for Perron's formula and the explicit formula;
  what is proved is the *smoothed* Perron formula together with a quantitative bound showing it
  computes `ψ(X)` in the limit, and the Weil test-function form of the explicit formula. This is
  recorded in the row's `latest_update` rather than being claimed as the unsmoothed identity.

## Adversarial revalidation: M2-SELBERG

* **Claim mode.** `positiveProportionOnCriticalLine` discharges the `Prop` of
  `RiemannHypothesis/Partial.lean` — the row's exit criterion — and `selberg_positive_proportion`
  exhibits the constant `1/3` explicitly.
* **Vacuity check.** The constant is `> 0` and the count it multiplies diverges, so the inequality
  is not satisfied trivially by both sides being zero at large heights.
* **Attribution.** The proof is *not* Selberg's mollifier argument; it is a corollary of the
  stronger two-thirds theorem. Both the module docstring and the row say so.

## Adversarial revalidation: M2-LEVINSON

* **Claim mode.** `levinson_one_third` is the dyadic-window inequality with constant `1/3 − ε` for
  every `ε > 0`, pinned in `scripts/revalidation.lean`.
* **Vacuity check.** As above, the right-hand side diverges, so the statement has content.
* **Attribution.** Obtained from the two-thirds theorem, not from Levinson's method; the row and
  the module docstring record this, and `M2-MOLLIFIER` remains open because the mollifier
  machinery itself is still not formalized here.

## Adversarial revalidation: M2-CONREY

* **Claim mode.** `twoFifthsOnCriticalLine` discharges the stated `Prop`; `conrey_two_fifths` is
  the explicit `2/5 − ε` dyadic form.
* **Vacuity check.** Same as the previous two rows.
* **Is `2/5` weaker than what is proved?** Yes — it is a consequence of the `2/3` bound. The row is
  closed because its exit criterion is met, not because Conrey's argument was formalized.
