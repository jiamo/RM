# M1-ALMOST-ALL-STRIP — Carlson's density theorem in its `o(T)` form

Date: 2026-08-29
Files: `RiemannHypothesis/MollifiedZetaMeanSquare.lean`, `RiemannHypothesis/MollifiedZetaCircle.lean`,
`RiemannHypothesis/CarlsonDensity.lean`

## Claim

The proposition the row is measured against,

```lean
def AlmostAllZerosNearCriticalLine : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun T : ℝ => (ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
        δ ≤ |s.re - 1 / 2|} : ℝ) / T) atTop (𝓝 0)
```

is proved, as `RiemannHypothesis.almostAllZerosNearCriticalLine`.  The quantitative statements
behind it are

```lean
theorem exists_ncard_zerosRightOf_le_eps {σ ε : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ((zerosRightOf σ T).ncard : ℝ) ≤ ε * T

theorem tendsto_ncard_zerosRightOf_div_atTop {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Tendsto (fun T : ℝ => ((zerosRightOf σ T).ncard : ℝ) / T) atTop (𝓝 0)

theorem tendsto_ncard_zerosOffCriticalLine_div_atTop {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLine δ T).ncard : ℝ) / T) atTop (𝓝 0)
```

with `zerosRightOf σ T = {ρ | ζ ρ = 0 ∧ σ ≤ re ρ ∧ 0 < im ρ ∧ im ρ ≤ T}`.  This is strictly
stronger than the Bohr–Landau `O(T)` of `M2-BOHR-LANDAU`, which is what the row previously had.

## Proof

The geometry is the one of Bohr–Landau.  Fix `1/2 < σ < 1`, put `κ = (σ − 1/2)/4`,
`r = 3 − σ + κ`, `R = 3 − σ + 2κ`, so `0 < r < R < 5/2`; a zero with `re ρ ≥ σ` and
`|im ρ − u| ≤ κ` lies in the closed disc of radius `r` about `3 + i u`, and the Jensen counting
inequality of `M2-ZERO-COUNT-LOCAL` bounds the number of such zeroes by
`(circleAverage (log ‖·‖) (3 + i u) R − log ‖·(3 + i u)‖) / log (R/r)`.

What changes is the function counted: not `ζ` but the mollified function `F_y = ζ M_y`, with
`M_y(s) = ∑_{n ≤ y} μ(n) n^{−s}`.  Since `M_y` is entire, `F_y` vanishes wherever `ζ` does, so
the counting inequality applies verbatim, and two things improve:

1. *At the centre.*  `‖F_y(s) − 1‖ ≤ 1/y` for `re s ≥ 3` (`norm_mollifiedZeta_sub_one_le`,
   from the mollifier identity in the half plane of absolute convergence together with
   `|c_y(m)| ≤ d(m) ≤ m`), so `−log ‖F_y(3 + i u)‖ ≤ 2/y` instead of the `log 2` available
   for `ζ`.
2. *On the circle.*  `log ‖z‖ ≤ (λ/2) ‖z − 1‖² + 1/(2λ)` for every `λ > 0`
   (`circleAverage_log_norm_mollifiedZeta_le`), whose additive constant `1/(2λ)` can be made
   as small as one likes, at the price of a large multiple of the mean square of `F_y − 1`.

The mean square of `F_y − 1` is the analytic input, and it is small — this is the whole point
of the mollifier.  `RiemannHypothesis/MollifiedZetaMeanSquare.lean` proves that for every
`σ₀ > 1/2` and every `ε > 0` there is a length `y` and a height `b₀` with
`∫_a^b ‖ζ M_y − 1‖² dt ≤ ε b` for all `1 ≤ a ≤ b`, `b ≥ b₀`, uniformly for `σ₀ ≤ σ ≤ 6`.  Its
two halves are `ζ M_y − 1 = (M_y P_K − 1) + M_y (ζ − P_K)` with the truncation length
`K = ⌈b^α⌉`, `α = (1 + 1/(3/2 − σ₀))/2 > 1`:

* the Dirichlet polynomial half uses the *Montgomery–Vaughan shape* of the mean value theorem
  (`M2-MEANVALUE-MV`), whose error sits inside the sum; this is essential, because the
  polynomial has length `yK ≈ b^α` with `α > 1`, and the elementary error `8 N (1 + log N)`
  would swamp the saving;
* the tail half uses Euler–Maclaurin of order `m` for `ζ − P_K`, with `m` chosen from `α`.

`RiemannHypothesis/MollifiedZetaCircle.lean` transports the bound from vertical lines to the
circle averages the counting inequality consumes (Tonelli plus the parametrization of the
circle, exactly as in the unmollified case).  Integrating the counting inequality over the
ordinate `u` of the centre and using the window indicator gives

`κ · N(σ; 5, T) · log (R/r) ≤ (λ ε / 2 + 1/(2λ) + 2/y) T + O(1)`,

and the right-hand side is at most `η T` for any prescribed `η > 0`: choose `y` large, then
`λ` large, then `ε` small.  Finitely many zeroes of ordinate below `5` are absorbed into the
`O(1)`.  The two-sided count follows from the reflection `ρ ↦ 1 − conj ρ`.

## Verification

* `lake build` succeeds; no `sorry` outside `Challenge.lean`.
* `#print axioms` on `exists_ncard_zerosRightOf_le_eps`, `tendsto_ncard_zerosRightOf_div_atTop`,
  `tendsto_ncard_zerosOffCriticalLine_div_atTop` and `almostAllZerosNearCriticalLine` gives
  exactly `propext, Classical.choice, Quot.sound`; the checks are in `scripts/audit.sh`.
* All four statements are written out and pinned in `scripts/revalidation.lean`.

## Scope

Zeroes are counted without multiplicity — exactly as the proposition of
`RiemannHypothesis/Partial.lean` does.  The constants are not explicit and degenerate as
`σ ↓ 1/2`, as they must.  The bound is `o(T)`; the power saving
`N(σ, T) = O(T^(4σ(1−σ)) log T)` of Carlson's quantitative form is **not** claimed here — it
needs the mollifier length to grow with `T`, and it is tracked on `M2-DENSITY`.  No zero is
located, and the Riemann hypothesis is neither proved nor disproved.

## Adversarial revalidation: M1-ALMOST-ALL-STRIP

Second pass, looking for the ways this row could be wrong.

1. *Is the statement the intended one, or a weaker relative?*  The pinned `example` in
   `scripts/revalidation.lean` writes the proposition out in full — the set, the normalization
   by `T`, the filter — without mentioning `AlmostAllZerosNearCriticalLine`, and it is closed
   by `RiemannHypothesis.almostAllZerosNearCriticalLine`.  So the name cannot have drifted from
   the statement.  The normalization is by `T` and not by the Riemann–von Mangoldt count
   `N(0, T) ≍ T log T`; dividing by the larger `N(0, T)` would have been the weaker claim of
   `M2-BOHR-LANDAU`, and it is not what is proved here.
2. *Is it vacuous?*  No: the set is the set of zeroes at distance `≥ δ` from the critical line,
   which is exactly the set the Riemann hypothesis asserts to be empty; nothing in the proof
   assumes it is.  The `δ ≥ 1/2` branch of the final proof *is* vacuous (no zero of positive
   ordinate has `|re − 1/2| ≥ 1/2`), but it is a side branch: the substance is the `δ < 1/2`
   branch, which goes through the density estimate.
3. *Is anything conditional?*  No hypothesis of any statement in the chain mentions an unproved
   `Prop` of this repository, and the row is absent from
   `docs/goal/conditional-theorems.txt`; the audit script rechecks this boundary.
4. *Does the counting argument secretly need `ζ M_y ≠ 0`?*  It needs `F_y(3 + i u) ≠ 0`, at the
   centre of the circle, where `re = 3` and the Euler product applies — not in the strip.  This
   is `mollifiedZeta_ne_zero`, which is proved from `‖F_y − 1‖ ≤ 1/y ≤ 1/4 < 1`.
5. *Could the mollified mean square be small for a trivial reason?*  It could not be small for
   `ζ` itself: `∫_a^b ‖ζ − 1‖²` is of order `b`, not `o(b)`.  Smallness uses the vanishing of
   the coefficients `c_y(m) = ∑_{d ∣ m, d ≤ y} μ(d)` for `2 ≤ m ≤ y`
   (`Mollifier.detectCoeff_eq_zero_of_le`), i.e. genuinely uses Möbius cancellation.
6. *Where is the theorem still weaker than the literature?*  The bound has no power saving;
   see the Scope section.  That gap is recorded on `M2-DENSITY` and is not claimed anywhere.
