# M2-BOHR-LANDAU — the zero-density theorem `N(σ, T) = O_σ(T)`

Date: 2026-08-25
Files: `RiemannHypothesis/StripMeanSquareUniform.lean`,
`RiemannHypothesis/ZetaCircleAverage.lean`, `RiemannHypothesis/BohrLandau.lean`

## Claim

For every fixed `σ > 1/2` the number of zeroes of `ζ` with real part at least `σ` and ordinate
in `(0, T]` is `O_σ(T)`; consequently, since the total number of zeroes of ordinate in `(0, T]`
is of order `T log T`, **almost all zeroes of `ζ` lie within `δ` of the critical line**, for
every fixed `δ > 0`.

Nothing below is conditional.

### The uniform mean square (`RiemannHypothesis/StripMeanSquareUniform.lean`)

* `exists_integral_normSq_riemannZeta_le_uniform` — for `1/2 < σ₀ < 1` there is a single
  `C > 0` with `∫_1^T ‖ζ(σ + i t)‖² dt ≤ C T` for **every** abscissa `σ ≥ σ₀` and every `T ≥ 1`.
  There is no upper bound on `σ`: the same constant covers the whole half-plane `re s ≥ σ₀`.
* `integral_normSq_riemannZeta_le_uniform_Icc` — the same on a general interval `[a, b] ⊆ [1, ∞)`.

Uniformity in `σ` is exactly what the previous mean-square rows did not supply, and it is what a
circle average needs: a circle of radius `R` about `3 + i y` meets every abscissa between `3 − R`
and `3 + R` at once. The proof runs the Euler–Maclaurin balance of `M1-STRIP-MEAN-SQUARE` with
the order `m` fixed once and for all by `σ₀` rather than by `σ`, using that the off-diagonal sum
of the mean value theorem is antitone in `σ` (`offDiagSum_antitone`) and the crude bound
`‖ζ(s)‖ ≤ 2` for `re s ≥ 2` (`norm_riemannZeta_le_two_of_two_le_re`) to cover `σ ≥ 2`.

### The circle averages (`RiemannHypothesis/ZetaCircleAverage.lean`)

* `circleAverage_log_norm_riemannZeta_le_circleAverage_normSq` — since `log x ≤ x²/2`, the circle
  average of `log ‖ζ‖` is at most the circle average of `‖ζ‖²/2`.
* `integrable_uncurry_circleIntegrandSq` — the integrand `(θ, y) ↦ ‖ζ(circleMap (3 + i y) R θ)‖²/2`
  is continuous, hence integrable, on `[0, 2π] × [a, b]` for `4 ≤ a`: the pole of `ζ` at `1` is
  outside every such circle when `R < 5/2` (`circleMap_ne_one`, `one_notMem_closedBall_of_le`).
* `exists_integral_circleAverage_normSq_riemannZeta_le` — Tonelli and Fubini over the box then
  turn the vertical integral of the circle averages into a vertical integral of the mean square
  along the shifted lines, which the uniform bound above controls:
  `∫_a^b circleAverage (‖ζ‖²/2) (3 + i y) R dy ≤ C b`, for `0 < R < 5/2` and `4 ≤ a ≤ b`.
  `intervalIntegrable_circleAverage_normSq_riemannZeta` records the integrability separately.

### The density theorem (`RiemannHypothesis/BohrLandau.lean`)

With `zerosRightOf σ T = {ρ | ζ ρ = 0 ∧ σ ≤ re ρ ∧ 0 < im ρ ≤ T}` and
`zerosOffCriticalLine δ T = {ρ | ζ ρ = 0 ∧ δ ≤ |re ρ − 1/2| ∧ 0 < im ρ ≤ T}`:

* `card_filter_le_circleAverage` — the core Jensen estimate. Fix `κ > 0` and `0 < r < R < 5/2`
  with `(3 − σ)² + κ² ≤ r²`. Every zero with `re ρ ≥ σ` and `|im ρ − y| ≤ κ` lies in the closed
  disc of radius `r` about `3 + i y`, so the Jensen counting inequality of `M2-ZERO-COUNT-LOCAL`
  bounds their number by `(circleAverage (‖ζ‖²/2) (3 + i y) R + log 2) / log (R/r)`, using
  `‖ζ(3 + i y)‖ ≥ 1/2`.
* `exists_ncard_zerosRightOf_high_le`, `exists_ncard_zerosRightOf_le` — integrating a window
  indicator in `y` (`le_integral_window_indicator`) turns the local count into the global one:
  for `1/2 < σ < 1` there is `C > 0` with `#(zerosRightOf σ T) ≤ C T` for every `T ≥ 1`. The
  choice is `κ = (σ − 1/2)/4`, `r = 3 − σ + κ`, `R = 3 − σ + 2κ`, so that `3 − R = σ − 2κ > 1/2`
  and the uniform mean square applies. The zeroes of ordinate below `5` are absorbed into the
  constant, being finite in number.
* `exists_ncard_zerosOffCriticalLine_le` — the two-sided form, obtained by reflecting in the
  critical line: `riemannZeta_one_sub_conj_eq_zero` says that `ρ ↦ 1 − conj ρ` maps zeroes of the
  strip to zeroes of the same ordinate, so the left half is a bijective image of the right half.
* `exists_mul_le_windowCount_zero` — the Riemann–von Mangoldt **lower** bound
  `N(0, T) ≥ c · T log T` for all large `T`, with multiplicity. It is read off the dyadic window
  `(T/2, T]` of the vendored `Zeta23.RvM.riemannVonMangoldt`: the main term of that window is
  `(T/(4π)) log T` up to `O(T)`, which dominates the `O(log T)` error.
* `tendsto_zerosOffCriticalLine_div_windowCount` — dividing, `#(zerosOffCriticalLine δ T)/N(0, T)
  → 0` as `T → ∞`, at the rate `O_δ(1 / log T)`.

## Scope — what is *not* claimed

* Zeroes are counted **without multiplicity** in `zerosRightOf` and `zerosOffCriticalLine`, while
  the denominator `windowCount 0 T` counts **with multiplicity**; the ratio statement is
  therefore conservative, not inflated.
* The bound is `O(T)`, not the `o(T)` of Carlson's density theorem
  `N(σ, T) = O(T^{4σ(1−σ)} log T)`. In particular the `Prop`
  `AlmostAllZerosNearCriticalLine` of `RiemannHypothesis/Partial.lean`, which normalizes the
  count by `T` rather than by `N(0, T)`, is **not** proved here; the row `M1-ALMOST-ALL-STRIP`
  stays open and records that the missing input is a mollified mean square.
* The constants are not explicit and blow up as `σ ↓ 1/2`, as they must.
* No zero-free region, no location of any individual zero, and nothing about the Riemann
  hypothesis itself follows.

## Adversarial revalidation: M2-BOHR-LANDAU

* `lake build` of the whole repository succeeds; `RiemannHypothesis.StripMeanSquareUniform`,
  `RiemannHypothesis.ZetaCircleAverage` and `RiemannHypothesis.BohrLandau` are imported by
  `RiemannHypothesis.lean`, so they are among its targets, and none of the three contains a
  `sorry`.
* `#print axioms` for `exists_integral_normSq_riemannZeta_le_uniform`,
  `integral_normSq_riemannZeta_le_uniform_Icc`,
  `exists_integral_circleAverage_normSq_riemannZeta_le`, `card_filter_le_circleAverage`,
  `exists_ncard_zerosRightOf_le`, `exists_ncard_zerosOffCriticalLine_le`,
  `exists_mul_le_windowCount_zero` and `tendsto_zerosOffCriticalLine_div_windowCount` reports
  exactly `[propext, Classical.choice, Quot.sound]`; the checks are in `scripts/audit.sh`.
* The claims are pinned in `scripts/revalidation.lean`, written out in full — including the
  counting sets, unfolded to their defining predicates, so that a change to `zerosRightOf` or
  `zerosOffCriticalLine` cannot silently weaken them — with the repository's declarations as
  the proof terms.
* The statements are not vacuous. The hypotheses are `1/2 < σ < 1` (respectively `0 < δ < 1/2`)
  and `1 ≤ T`, all satisfiable; the counted sets are genuinely inhabited for some parameters
  (`M2-ZERO-EXISTS` and `M2-ZERO-INFINITE` show the strip contains infinitely many zeroes), and
  the denominator `windowCount 0 T` tends to infinity (`tendsto_windowCount_atTop`), so the
  limit statement is not the limit of an eventually-undefined quotient made trivial by a zero
  denominator.
* The lower bound `exists_mul_le_windowCount_zero` is unconditional: it is derived from
  `Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts`, whose hypothesis `gammaFacts` is a proved
  term of the vendored library, not an assumption of this repository.
* Every statement is unconditional; none takes an unproved `Prop` of this repository as a
  hypothesis, and the modules add no row to `docs/goal/conditional-theorems.txt`.
