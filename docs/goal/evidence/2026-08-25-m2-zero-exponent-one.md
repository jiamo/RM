# M2-ZERO-EXPONENT — the exponent of convergence of the nontrivial zeroes is *exactly* `1`

Date: 2026-08-25
File: `RiemannHypothesis/ZeroExponentOne.lean`
Predecessor: `docs/goal/evidence/2026-08-24-m2-zero-exponent.md` (the upper half, `≤ 1`)

## Claim

Counting the nontrivial zeroes of `ζ` without multiplicity:

* `not_summable_inv_norm` — `∑_ρ 1/‖ρ‖` diverges;
* `not_summable_rpow_neg` — `∑_ρ ‖ρ‖^(-e)` diverges for every `0 < e ≤ 1`;
* `not_summable_rpow_neg_of_nonpos` — and for every `e ≤ 0`;
* `sInf_exponent_summable_eq_one` —
  `sInf {e | Summable (fun ρ => ‖ρ‖^(-e))} = 1`,

which, with `summable_inv_norm_rpow` of the predecessor (every `e > 1` converges), says that the
exponent of convergence of the zero set is exactly `1`.

## Proof

The open boundary of the predecessor row was the lower bound `N(T) ≫ T log T`. It is now
available in the repository, so the divergence half is short.

* `exists_mul_le_windowCountDistinct_zero` — `N_d(0, T) ≫ T log T` for the number of *distinct*
  nontrivial zeroes of ordinate in `(0, T]`. This combines `exists_mul_le_windowCount_zero`
  (`M2-BOHR-LANDAU`; the Riemann–von Mangoldt lower bound with multiplicity, from the dyadic
  window `(T/2, T]` of the vendored `Zeta23` library) with `five_sixths_distinct_cumulative`
  (Theorem C of that library: at least five sixths of the zeroes are distinct points), used with
  `ε = 1/6`, which leaves the factor `2/3`.
* `norm_le_of_mem_windowZeros` — a zero of ordinate in `(0, T]` lies in the open strip, so
  `‖ρ‖ ≤ |re ρ| + |im ρ| ≤ 1 + T`; hence `mul_rpow_le_sum_rpow_neg_windowZeros`: the partial sum
  of `‖ρ‖^(-e)` over that window is at least `N_d(0, T) · (1 + T)^(-e)`.
* For `0 < e ≤ 1` and `T ≥ 1` one has `(1 + T)^(-e) ≥ (1 + T)⁻¹` and `T/(1+T) ≥ 1/2`, so the
  partial sum is at least `(c/2) log T`, which tends to infinity
  (`tendsto_sum_rpow_neg_windowZeros_atTop`). A summable family has all its finite partial sums
  bounded by its sum, so no such `e` is admissible.
* For `e ≤ 0` the terms are bounded below by `δ^(-e) > 0`, where `δ ≤ ‖ρ‖` uniformly
  (`exists_pos_le_norm_of_nontrivialZero`), while the zero set is infinite
  (`infinite_nontrivialZeroSet`), so the terms do not tend to `0` along the cofinite filter.
* Consequently the set of admissible exponents is exactly `Ioi 1`, whose infimum is `1`.

## Scope — what is *not* claimed

* Zeroes are counted **without multiplicity**, exactly as in the predecessor.
* No asymptotic for `∑_{0 < γ ≤ T} 1/‖ρ‖` is claimed; only that it tends to infinity, and only
  the lower bound `≫ log T` is extracted, with no explicit constant.
* The Hadamard product for `ξ`, for which the summability of `‖ρ‖^(-(1+e))` is the analytic
  input, is still not constructed here.
* Nothing about the real parts of the zeroes is claimed, and nothing here bears on the Riemann
  hypothesis.

## Verification

* `lake build` — the whole project, clean.
* `bash scripts/audit.sh` — exit 0; the new statements are pinned in full in
  `scripts/revalidation.lean` and their axioms are checked (`propext`, `Classical.choice`,
  `Quot.sound` only).
* No `sorry` in `RiemannHypothesis/ZeroExponentOne.lean`.

## Adversarial revalidation: M2-ZERO-EXPONENT

* `lake build` of the whole repository succeeds with `RiemannHypothesis/ZeroExponentOne.lean`
  imported by `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `exists_mul_le_windowCountDistinct_zero`, `tendsto_sum_rpow_neg_windowZeros_atTop`,
  `not_summable_rpow_neg`, `not_summable_rpow_neg_of_nonpos`, `not_summable_inv_norm` and
  `sInf_exponent_summable_eq_one`; the checks are in `scripts/audit.sh`.
* All six statements are pinned in full in `scripts/revalidation.lean`.
* The statements are not vacuous. `not_summable_inv_norm` is a divergence claim about an index
  set known to be infinite (`M2-ZERO-INFINITE`), and it is *not* provable from the upper bound
  of the predecessor row; conversely `sInf_exponent_summable_eq_one` uses both halves, so
  neither half alone would elaborate the pin. The `sInf` is over a nonempty set bounded below
  (it is `Ioi 1`), so it is not the junk value `sInf ∅ = 0`.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
* Direction check: the lower bound `N(T) ≫ T log T` is the input, and it is proved
  (`M2-BOHR-LANDAU`, from the vendored Riemann–von Mangoldt formula), not assumed; the passage
  from zeroes with multiplicity to distinct zeroes uses Theorem C of the vendored library, also
  proved.
