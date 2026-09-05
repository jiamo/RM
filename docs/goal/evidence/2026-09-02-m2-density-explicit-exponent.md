# M2-DENSITY / M2-DENSITY-POWER-SAVING — the saving made explicit: `N(σ, T) = O(T^{1−(σ−1/2)²/64})`

Date: 2026-09-02
Files: `RiemannHypothesis/CarlsonPowerSaving.lean`,
`RiemannHypothesis/CarlsonDensityPowerSaving.lean`

## Claim

```lean
theorem ncard_zerosRightOf_le_rpow_explicit {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - (σ - 1 / 2) ^ 2 / 64)
```

together with the two-sided form

```lean
theorem ncard_zerosOffCriticalLine_le_rpow_explicit {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ C * T ^ (1 - δ ^ 2 / 64)
```

The existential statements of `M2-DENSITY-POWER-SAVING` now also *name* the saving they
produce: `exists_ncard_zerosRightOf_high_le_rpow` and `exists_ncard_zerosRightOf_le_rpow`
carry the extra conjunct `(σ − 1/2)²/64 ≤ c`.

Zeroes are counted without multiplicity.

## What changed

Nothing in the mathematics: the same Carlson chain as on 2026-08-29, with the constants
tracked instead of discarded.  Every existential exponent in the chain has been given an
explicit value or bound in terms of `θ = σ₀ − 1/2`.

* `exists_integral_normSq_mollified_partialSum_sub_one_le_rpow` — the Montgomery–Vaughan half.
  Its exponent is `γ = α (3/2 − σ₀)` with `α = (1 + 1/(3/2 − σ₀))/2`, and a one-line
  computation gives the identity `γ = 1 − θ/2`, which the statement now records.
* `exists_integral_normSq_zeta_sub_partialSum_le_rpow` — the Euler–Maclaurin half.  Its
  exponent is `β = 2α(1 − σ₀)`; writing `u = 3/2 − σ₀` one has `β = u + 1/2 − 1/(2u) ≤ u`
  because `u ≤ 1`, i.e. `β ≤ 1 − θ`, which the statement now records.
* `exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow` — the combination.  Previously
  the mollifier exponent was chosen as `(1 − max(γ, β))/4`, a quantity for which only an upper
  bound was available.  It is now *defined* to be `θ/8`, which still satisfies both
  constraints `γ' + γ ≤ 1 − 3θ/8 < 1` and `2γ' + β ≤ 1 − 3θ/4 < 1`, so the mean-square saving
  is `c ≥ 3θ/8`.  The statement records `γ' = θ/8` and `3θ/8 ≤ c`.
* `exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow` — the circle averages.
  Here `σ₀ = min (3 − R) (3/4)`, so `θ = min (5/2 − R) (1/4)` exactly; the statement records
  this together with `3θ/8 ≤ c` and `γ' = θ/8`.
* `exists_ncard_zerosRightOf_high_le_rpow` — the counting.  The Jensen geometry uses
  `κ = (σ − 1/2)/4` and `R = 3 − σ + 2κ`, so `5/2 − R = (σ − 1/2)/2 < 1/4` and hence
  `θ = (σ − 1/2)/2`.  The saving produced by the three-way balancing is
  `c' = min (min (min (γ'θ) c / 2) γ') (1/2)`, and with `γ' = θ/8` each entry is at least
  `θ²/16`: `γ'θ/2 = θ²/16`, `c/2 ≥ 3θ/16 ≥ θ²/16` and `γ' = θ/8 ≥ θ²/16` for `θ ≤ 2`.  Thus
  `c' ≥ θ²/16 = (σ − 1/2)²/64`.

The two explicit statements then follow from `T^{1−c} ≤ T^{1−c'}` for `T ≥ 1` and `c ≥ c'`.

## Verification

`lake build` succeeds for the whole repository; no `sorry`; `#print axioms` on the two
explicit statements gives exactly `propext, Classical.choice, Quot.sound` (checked in
`scripts/audit.sh`); both are pinned in `scripts/revalidation.lean` under
`M2-DENSITY-POWER-SAVING`, alongside the strengthened existential forms.

## Scope

The saving `(σ − 1/2)²/64` is an explicit function of `σ` and degrades continuously to `0` as
`σ ↓ 1/2`, which is what the previous round's `Scope` section flagged as missing.  It is still
weaker than the classical results:

* Carlson's own density theorem gives `N(σ, T) = O(T^{4σ(1−σ)} log T)`, a saving of
  `4(σ − 1/2)²`.  The shape in `σ − 1/2` is the same as here; the constant is `256` times
  worse.
* The exit criterion originally scoped on `M2-DENSITY`, a saving *linear* in `σ − 1/2` (the
  Selberg/Ingham shape `N(σ, T) = O(T^{1−c(σ−1/2)})`), is **not** proved here and is not
  reachable by this route.  A linear saving needs either the sharp mean value theorem
  (Montgomery–Vaughan's generalized Hilbert inequality) or the fourth moment (approximate
  functional equation together with divisor correlation sums); neither is in mathlib nor in
  this repository — the same gap that `M2-MEANVALUE` records.

The constant `C(σ)` remains inexplicit, no statement is uniform in `σ`, nothing is claimed at
`σ = 1/2`, zeroes are counted without multiplicity, no zero is located, and the Riemann
hypothesis is neither proved nor disproved.

## Adversarial revalidation: M2-DENSITY / M2-DENSITY-POWER-SAVING

The claims are pinned in `scripts/revalidation.lean` under the heading
`M2-DENSITY-POWER-SAVING`: the statements are written out in full there and the repository's
declarations are supplied as the proof terms, so a weakened, renamed or extra-hypothesis
version stops that file from elaborating.  In particular the pinned form of
`ncard_zerosRightOf_le_rpow_explicit` names the exponent `1 − (σ − 1/2)²/64` literally, so the
saving cannot silently shrink.  `scripts/audit.sh` runs that file, rebuilds everything, checks
that no `sorry` occurs outside `Challenge.lean`, and prints the axioms of both explicit
statements in addition to the existential ones.

A reader checking whether the row overclaims should note the two negative statements above:
the exponent proved is quadratic in `σ − 1/2`, not linear, and the constant is not effective.
