# M2-DENSITY-POWER-SAVING — `N(σ, T) = O(T^{1−c})`

Date: 2026-08-29
Files: `RiemannHypothesis/CarlsonPowerSaving.lean`,
`RiemannHypothesis/CarlsonDensityPowerSaving.lean`

## Claim

```lean
theorem exists_ncard_zerosRightOf_le_rpow {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - c)
```

together with the two-sided form

```lean
theorem exists_ncard_zerosOffCriticalLine_le_rpow {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ C * T ^ (1 - c)
```

Zeroes are counted without multiplicity.  This strengthens the `o(T)` of
`M1-ALMOST-ALL-STRIP` to a genuine power saving.

## Proof

The Carlson argument of `M1-ALMOST-ALL-STRIP` is repeated with every `ε` replaced by an
explicit power, and with the mollifier length allowed to grow with the height.

*The arithmetic input with a rate.*  `exists_sum_Ioc_divisorCount_sq_le_rpow`:
for `σ ≥ σ₀ > 1/2`, `∑_{y < m ≤ M} d(m)² m^{−2σ} ≤ D y^{−(σ₀−1/2)}`.  Splitting off `m^{−a}`
with `a = σ₀ + 1/2 ∈ (1, 2σ₀)` leaves `m^{−(σ₀−1/2)} ≤ y^{−(σ₀−1/2)}` and a convergent series.

*The polynomial half.*  `exists_integral_normSq_mollified_partialSum_sub_one_le_rpow`:
`∫₀^b ‖M_y P_K − 1‖² ≤ C (b y^{−(σ₀−1/2)} + y b^{γ})` at the Carlson truncation length
`K = ⌈b^α⌉`, with `γ = α (3/2 − σ₀) < 1`.

*The tail half.*  `exists_integral_normSq_zeta_sub_partialSum_le_rpow`:
`∫_a^b ‖ζ − P_K‖² ≤ E b^{β}` with `β = 2α(1 − σ₀) < 1`.

*The combination.*  `exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow`: from
`‖ζ M_y − 1‖² ≤ 2‖M_y P_K − 1‖² + 2y² ‖ζ − P_K‖²` and `y ≤ 4 b^{γ'}` with `γ'` small enough
that `γ' + γ < 1` and `2γ' + β < 1`, one gets
`∫_a^b ‖ζ M_y − 1‖² ≤ C (b y^{−(σ₀−1/2)} + b^{1−c})`.

*The circle averages.*  `exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow`
transports this to circles of radius `R < 5/2` about `3 + i u` by Fubini, as in
`M2-MOLLIFIED-ZETA-MEAN-SQUARE`; the shifted endpoints `b + R sin θ ∈ [b − 5/2, b + 5/2]` cost
at most a factor two in each term.

*The counting.*  `exists_ncard_zerosRightOf_high_le_rpow` feeds this into the Jensen counting
inequality of `M1-ALMOST-ALL-STRIP`,

`κ N log(R/r) ≤ (λ/2) ∫_4^T A(u) du + (1/(2λ) + 2/y)(T − 4)`,

with `y = ⌈T^{γ'}⌉` and `λ = T^{c'}`.  Each of the three terms is `T^{1−c'}` as soon as
`c' ≤ min (γ'θ/2) (c/2) γ'`, where `θ = σ₀ − 1/2`.  The finitely many zeroes of ordinate below
`5` are absorbed into the constant, and the bounded range `1 ≤ T ≤ T₀` follows from
monotonicity of the count in the height.

## Verification

`lake build` succeeds; no `sorry`; `#print axioms` on the statements above gives exactly
`propext, Classical.choice, Quot.sound` (checked in `scripts/audit.sh`); the two density
statements and the quantitative mean square are pinned in `scripts/revalidation.lean`.

## Scope

The exponent `c` is not explicit and is far from Carlson's `1 − 4σ(1 − σ)`; only the existence
of *some* power saving is claimed, and no dependence of `c` on `σ` is exhibited — in
particular the statement does not degenerate gracefully as `σ` decreases to `1/2`, since `c`
is produced by a chain of minima.  Zeroes are counted without multiplicity.  Nothing is
claimed on the critical line itself.  No zero is located, and the Riemann hypothesis is
neither proved nor disproved.

## Adversarial revalidation: M2-DENSITY-POWER-SAVING

The claims of this row are pinned in `scripts/revalidation.lean` under the heading
`M2-DENSITY-POWER-SAVING`: the statements are written out in full there and the repository's
declarations are supplied as the proof terms, so a weakened, renamed or extra-hypothesis
version stops that file from elaborating.  `scripts/audit.sh` runs it, rebuilds everything,
checks that no `sorry` occurs outside `Challenge.lean` and prints the axioms of
`exists_ncard_zerosRightOf_le_rpow`, `exists_ncard_zerosOffCriticalLine_le_rpow`,
`exists_ncard_zerosRightOf_high_le_rpow`,
`exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow` and
`exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow`.

## Update (2026-09-02)

The `Scope` paragraph above is superseded on one point: the exponent *is* now explicit.  Every
exponent in the chain has been tracked in `θ = σ₀ − 1/2`, and the saving is
`c ≥ (σ − 1/2)²/64`, stated outright by `ncard_zerosRightOf_le_rpow_explicit` and
`ncard_zerosOffCriticalLine_le_rpow_explicit`.  See
`docs/goal/evidence/2026-09-02-m2-density-explicit-exponent.md`.  The remaining limitations —
the inexplicit constant `C(σ)`, the quadratic (rather than linear) shape in `σ − 1/2`, and the
gap to Carlson's constant — are unchanged.
