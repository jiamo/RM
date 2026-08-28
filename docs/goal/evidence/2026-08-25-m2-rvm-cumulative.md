# M2-RVM-CUMULATIVE — `N(T) ~ (T/2π) log T`

Date: 2026-08-25
File: `RiemannHypothesis/RvMCumulative.lean`
Predecessor: `docs/goal/evidence/2026-08-24-m2-bohr-landau.md` (`N(0,T) ≫ T log T`)

## Claim

Counting the nontrivial zeroes of `ζ` **with** multiplicity and with ordinate in `(0, T]`
(`windowCount 0 T`):

* `exists_abs_windowCount_sub_main_le` — the vendored Riemann–von Mangoldt formula on the
  dyadic window, restated in the repository's notation:
  `|N(T, 2T) − (T/2π)(log T − κ)| ≤ C log T` with `κ = log(2π) − 2 log 2 + 1` (`rvmConst`);
* `exists_abs_windowCount_zero_sub_main_le` — the cumulative estimate
  `|N(0, T) − (T/2π) log T| ≤ A (T + (log T)²)` for all large `T`;
* `tendsto_windowCount_zero_div` — hence `N(0, T)/(T log T) → 1/(2π)`.

Before this row the repository had only the one-sided divergence `N(0, T) ≫ T log T`
(`exists_mul_le_windowCount_zero`) with an unspecified constant. The constant is now pinned:
the count is asymptotically `(T/2π) log T`.

## Proof

The vendored library proves Riemann–von Mangoldt only on a dyadic window. The cumulative form
is obtained by summing the windows.

* `Zeta23_ell1_eq` — `Zeta23.ell1 T = log(T/2π) + 2 log 2 − 1 = log T − κ` for `T > 0`, which
  puts the vendored main term into the shape used here; `Zeta23.zetaZeroConfig_N` and
  `windowCount_eq` (from `RiemannHypothesis/Zeta23Bridge.lean`) identify the two zero counts.
* `windowCount_eq_add_sum_dyadic` — induction on `n`, using the additivity `windowCount_add`
  of `RiemannHypothesis/PartialProved.lean`, gives
  `N(0, 2^n s) = N(0, s) + ∑_{j<n} N(2^j s, 2^(j+1) s)`.
* `exists_dyadic_scale` — every `T ≥ 2b` is `2^n s` with `b ≤ s < 2b` and `n log 2 ≤ log T`; so
  there are at most `O(log T)` blocks, each carrying an error `O(log T)`, for a total
  `O((log T)²)`.
* `sum_range_two_pow_real` and `sum_range_mul_two_pow_real` — the two geometric sums
  `∑_{j<n} 2^j = 2^n − 1` and `∑_{j<n} j 2^j = (n − 2)2^n + 2`.
* `sum_dyadic_main_term` — with those, the summed main term
  `∑_{j<n} (2^j s/2π)(log s + j log 2 − κ)` equals
  `(2^n s/2π)(log s + n log 2) − (2^n s/2π)(κ + 2 log 2) + (s/2π)(κ − log s + 2 log 2)`, i.e.
  `(T/2π) log T` plus terms bounded by a constant multiple of `T`.
* Assembling: `N(0, T)` differs from `(T/2π) log T` by the `O(T)` secondary terms, the
  `O((log T)²)` accumulated window errors, and the fixed constant `N(0, 2b)`, all of which are
  `O(T + (log T)²)`.
* `tendsto_windowCount_zero_div` — dividing by `T log T`, the error is at most
  `A/log T + A (log T)/T → 0`, and `tendsto_iff_dist_tendsto_zero` with `squeeze_zero'` finishes.

## Scope — what is *not* claimed

* Zeroes are counted **with** multiplicity (that is what `windowCount` is), and only those of
  positive ordinate are counted, so this is `N(T)` in the classical normalisation.
* The error term is `O(T + (log T)²)`, i.e. `O(T)`, which is weaker than the classical
  `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)`. Only the leading term `(T/2π) log T` is pinned
  down; the secondary term `−(T/2π)(1 + log 2π)` is inside the error here. Sharpening to
  `O(log T)` would need the argument-principle count run once on `(0, T]` rather than summed
  over dyadic windows.
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
  `exists_abs_windowCount_sub_main_le`, `windowCount_eq_add_sum_dyadic`, `sum_dyadic_main_term`,
  `exists_abs_windowCount_zero_sub_main_le` and `tendsto_windowCount_zero_div`; the checks are in
  `scripts/audit.sh`.
* All five statements are pinned in full in `scripts/revalidation.lean`.
* The statements are not vacuous. `tendsto_windowCount_zero_div` fixes a *finite nonzero* limit
  `1/(2π)`, so it is not satisfiable by a degenerate count: it implies both
  `N(0,T) ≫ T log T` and `N(0,T) ≪ T log T`, and the upper half is new here (the predecessor row
  gave only the lower bound). The `∃ T₁` quantifier ranges over all sufficiently large `T` and
  `A` is required positive.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`. The only
  external input is the vendored `Zeta23.RvM.riemannVonMangoldt`, which is itself proved in
  `vendor/zeta23` and is already the input of the `M2-BOHR-LANDAU` lower bound.
* Direction check: the main term uses the *two-sided* window bound, not just the lower bound of
  the predecessor row; the accumulated error is genuinely tracked (`abs_le_of_two_sided_bounds`
  reconstructs an absolute-value bound from two explicit linear inequalities) rather than
  absorbed into an unquantified constant.
