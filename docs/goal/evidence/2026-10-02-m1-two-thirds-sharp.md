# The two-thirds theorem in absolute form, with the sharp constant

Date: 2026-10-02
Module: `RiemannHypothesis/Zeta23Sharp.lean`
Row: `M1-TWO-THIRDS-SHARP` (depends on `M1-TWO-THIRDS-ABSOLUTE`)

## Why

`M1-TWO-THIRDS-ABSOLUTE` turned the ratio form of the vendored two-thirds theorem into an
absolute count, but deliberately threw away half of the main term and then half again: it
proved `(T/8π) log T` zeroes on the critical line in `(T, 2T]`, where the same inputs give
`(2/3 − ε)(T/2π) log T`.  This row proves the sharp form.

## What is proved

With `windowLeadingTerm T = (T/2π)·log T`:

| theorem | statement |
|---|---|
| `windowCount_asymptotic` | `∀ ε > 0`, eventually `(1 − ε)(T/2π) log T ≤ N(T,2T) ≤ (1 + ε)(T/2π) log T` |
| `tendsto_windowCount_div` | `N(T,2T) / ((T/2π) log T) → 1` |
| `eventually_windowCountOnLine_ge_sharp` | `∀ ε > 0`, eventually `(2/3 − ε)(T/2π) log T ≤ N₀*(T,2T)` (distinct zeroes on the line) |
| `eventually_windowCountSimpleOnLine_ge_sharp` | the same for simple zeroes on the line |
| `eventually_windowCountDistinct_ge_sharp` | `∀ ε > 0`, eventually `(5/6 − ε)(T/2π) log T ≤ N_d(T,2T)` |

## Proof outline

1. `windowMainTerm T = (T/2π)(log T − c₀)`, `c₀ = log 2π + 1 − 2 log 2`.
2. `eventually_error_le`: for every `ε > 0`, eventually `(T/2π)|c₀| + |C| log T ≤ ε (T/2π) log T`
   (take `log T ≥ 2|c₀|/ε` and `T/2π ≥ 2|C|/ε`).
3. With `windowCount_sub_mainTerm_le` this gives `windowCount_asymptotic`, and the limit form.
4. `eventually_ge_of_ratio`: from a ratio theorem `(c − δ) N ≤ M` (with `0 < c ≤ 1`) and
   `N ≥ (1 − ε/2)(T/2π) log T`, choosing `δ = min(ε/2, c/2)` gives
   `(c − δ)(1 − ε/2) ≥ c − ε`, hence `M ≥ (c − ε)(T/2π) log T`.  Applied to Theorems A, B, C.

## Inputs (all unconditional theorems)

`windowCount_sub_mainTerm_le` (from `Zeta23.riemannVonMangoldt_zeta`),
`two_thirds_on_critical_line`, `two_thirds_simple_on_critical_line`, `five_sixths_distinct`.
No `Prop` of the repository is assumed.

## Adversarial revalidation: M1-TWO-THIRDS-SHARP

* `lake build RiemannHypothesis.Zeta23Sharp` succeeds with no warnings from the new module.
* No `sorry` in the module.
* `#print axioms` on all five theorems: `[propext, Classical.choice, Quot.sound]`.
* Non-vacuity: `tendsto_windowCount_div` pins the denominator to the classical size, so the
  ratio theorems cannot be satisfied by an empty or small `N`; the lower bounds are statements
  about counts of genuine zeroes of Mathlib's `riemannZeta` (see the 2026-09-06 evidence file
  for the reading of `windowCount` and friends against Mathlib).
* The four headline statements are pinned verbatim, with `windowLeadingTerm` unfolded, in
  `scripts/revalidation.lean`.

## Open boundary

None for the claims of this row.  (Explicit thresholds `T₀` and a re-proof of the vendored
analytic work remain outside its scope, as recorded on `M1-TWO-THIRDS-ABSOLUTE`.)  The Riemann
hypothesis itself is not touched by this row.
