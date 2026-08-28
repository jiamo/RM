# M2-RVM-CUMULATIVE (sharpened) — `N(T) = (T/2π)(log(T/2π) − 1) + O((log T)²)`

Date: 2026-08-25
File: `RiemannHypothesis/RvMCumulative.lean`
Predecessor: `docs/goal/evidence/2026-08-25-m2-rvm-cumulative.md` (same row, error `O(T)`)

## Claim

Counting the nontrivial zeroes of `ζ` **with** multiplicity and with ordinate in `(0, T]`
(`windowCount 0 T`):

* `exists_abs_windowCount_zero_sub_rvmMain_le` — the cumulative Riemann–von Mangoldt formula
  with the classical main term, constant included:
  `|N(0, T) − (T/2π)(log (T/2π) − 1)| ≤ A (log T)²` for all large `T`;
* `tendsto_windowCount_zero_sub_rvmMain_div_atTop` — its `o(T)` form:
  `(N(0, T) − (T/2π)(log (T/2π) − 1)) / T → 0`;
* `exists_abs_windowCount_zero_sub_main_le` — the previous, cruder statement
  `|N(0, T) − (T/2π) log T| ≤ A (T + (log T)²)`, now *derived* from the sharp one by putting the
  constant `log (2π) + 1` back into the error;
* `tendsto_windowCount_zero_div` — unchanged: `N(0, T)/(T log T) → 1/(2π)`.

The predecessor entry pinned down only the leading term `(T/2π) log T`, with an error of size
`T`; the secondary term `−(T/2π)(1 + log 2π)` was inside the error and was explicitly not
claimed. It is now part of the main term.

## Proof

Nothing new is needed beyond the pieces already in the module: the observation is that the
summed dyadic main term of `sum_dyadic_main_term` already carries the right constant.

With `T = 2^n s`, `b ≤ s < 2b` (`exists_dyadic_scale`), the telescope
`windowCount_eq_add_sum_dyadic` and the closed form `sum_dyadic_main_term` give

`N(0,T) − (T/2π)(log T − κ − 2 log 2)
   = N(0,s) + ∑_{j<n} (window error at 2^j s) + (s/2π)(κ − log s + 2 log 2)`,

where `κ = log(2π) − 2 log 2 + 1` is `rvmConst`. The identity
`log (T/2π) − 1 = log T − (κ + 2 log 2)` turns the left-hand side into the difference between
`N(0,T)` and the classical main term. Of the three terms on the right, the first is bounded by
the constant `N(0, 2b)`, the third by a constant depending only on `b`, and the middle one by
`n · C log T ≤ (C/log 2)(log T)²` since `n log 2 ≤ log T`. For `T ≥ 3` one has `(log T)² ≥ 1`, so
all three are absorbed into `A (log T)²`.

The `o(T)` form follows from `Real.tendsto_pow_log_div_mul_add_atTop` ((log T)²/T → 0), and the
crude form follows by writing `(T/2π) log T = (T/2π)(log (T/2π) − 1) + T·(log 2π + 1)/(2π)`.

## Scope — what is *not* claimed

* Zeroes are counted **with** multiplicity, and only those of positive ordinate are counted.
* The error term is `O((log T)²)`; the classical error is `O(log T)`. The loss is exactly the
  number of dyadic windows: each of the `O(log T)` windows contributes its own `O(log T)`.
  Removing it needs the argument principle run once on `(0, T]` rather than summed over windows.
* The finer terms of the classical formula — the constant `7/8` and the term `S(T)` — are not
  claimed.
* Nothing about the real parts of the zeroes is claimed, and nothing here bears on the Riemann
  hypothesis.

## Verification

* `lake build` — the whole project, clean.
* `bash scripts/audit.sh` — exit 0; the new statements are pinned in full in
  `scripts/revalidation.lean` and their axioms are checked.
* No `sorry` in `RiemannHypothesis/RvMCumulative.lean`.

## Adversarial revalidation: M2-RVM-CUMULATIVE

* `lake build` of the whole repository succeeds with `RiemannHypothesis/RvMCumulative.lean`
  imported by `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `exists_abs_windowCount_zero_sub_rvmMain_le` and
  `tendsto_windowCount_zero_sub_rvmMain_div_atTop`, as well as for the statements of the
  predecessor entry; the checks are in `scripts/audit.sh`.
* Both new statements are pinned in full in `scripts/revalidation.lean`.
* The statements are not vacuous: `A` is required positive, the bound holds for all `T ≥ T₁`,
  and the sharp statement is strictly stronger than the crude one, which is now derived from it.
  The `o(T)` form has a *fixed* limit `0` for a quantity of typical size `(log T)²`, so it is not
  satisfiable by a degenerate count.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`. The only
  external input remains the vendored `Zeta23.RvM.riemannVonMangoldt`.
* Direction check: the sharp bound is two-sided (an absolute value), and the constant of the
  main term is *not* free — the identity `log (T/2π) − 1 = log T − (κ + 2 log 2)` ties it to the
  vendored constant `κ`, so an error in it would break the bound at every large `T`.
