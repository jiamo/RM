# M2-LINDELOF-DENSITY — Backlund's criterion, from the Lindelöf hypothesis to the zeroes

Date: 2026-08-27
File: `RiemannHypothesis/LindelofDensity.lean`

## Claim

The Lindelöf hypothesis is recorded as a `Prop`,

```lean
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε
```

and the counting set is

```lean
def zerosRightOfWindow (σ T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
```

What is proved:

* **unconditional** (`card_filter_le_log_max`) — if `0 < κ`, `0 < r < R < 5/2`,
  `(3 − σ)² + κ² ≤ r²`, `1 ≤ M`, `y ≥ 4`, and `‖ζ‖ ≤ M` on the circle of radius `R` about
  `3 + i y`, then any finite set `S` of zeroes of `ζ` with real part at least `σ` satisfies

      #{ρ ∈ S : |im ρ − y| ≤ κ} · log (R/r) ≤ log M + log 2;

* **unconditional** (`card_le_sum_card_filter`) — a finite set of points with ordinates in
  `(T, T+1]` is covered by the `m` windows of half-height `κ` centred at `T + κ(2j+1)`,
  `j < m`, whenever `1/(2κ) ≤ m`;

* **conditional** (`exists_ncard_zerosRightOfWindow_le`) — under `LindelofHypothesis`, for
  `1/2 < σ < 1` and every `ε > 0` there is `A > 0` with

      #(zerosRightOfWindow σ T (T+1)) ≤ A + ε log T   for every T ≥ 5;

* **conditional** (`tendsto_ncard_zerosRightOfWindow_div_log`) — hence

      #(zerosRightOfWindow σ T (T+1)) / log T → 0   as T → ∞;

* **conditional** (`tendsto_ncard_zerosOffCriticalLineWindow_div_log`) — the two-sided form: for
  `0 < δ < 1/2`,

      #{ρ : ζ(ρ) = 0, |re ρ − 1/2| ≥ δ, T < im ρ ≤ T+1} / log T → 0   as T → ∞;

* **unconditional** (`exists_ncard_zerosRightOfWindow_le_log`) — there is an absolute `C > 0`
  with

      #(zerosRightOfWindow σ T (T+1)) ≤ C log T   for every σ and every T ≥ 25.

## Proof

The geometry is the one already used for the Bohr–Landau theorem in
`RiemannHypothesis/BohrLandau.lean`: with `κ = (σ − 1/2)/4`, `r = 3 − σ + κ` and
`R = 3 − σ + 2κ` one has `0 < r < R < 5/2` and `3 − R = σ/2 + 1/4 > 1/2`, so the closed disc of
radius `R` about `3 + i y` avoids the pole of `ζ` (for `y ≥ 4`) and lies in the half-plane where
the Lindelöf bound is assumed, while `(3 − σ)² + κ² ≤ r²` puts every zero with `re ρ ≥ σ` and
`|im ρ − y| ≤ κ` inside the concentric disc of radius `r`.

Jensen's counting inequality (`card_mul_log_le_circleAverage_sub_log`, proved in
`RiemannHypothesis/JensenDiscCount.lean` from Mathlib's `MeromorphicOn.circleAverage_log_norm`)
bounds the number of those zeroes by
`(circleAverage (log ‖ζ‖) (3 + i y) R − log ‖ζ(3 + i y)‖)/log (R/r)`.  Two replacements finish
the unconditional estimate: `‖ζ(3 + i y)‖ ≥ 1/2` (`half_le_norm_riemannZeta_of_three_le_re`)
handles the centre, and `circleAverage_mono_on_of_le_circle` — applicable because `log ‖ζ‖` is
circle integrable, `ζ` being meromorphic on the sphere — replaces the circle average by `log M`.
The hypothesis `1 ≤ M` is what makes the inequality `log ‖ζ(z)‖ ≤ log M` true also at a zero on
the circle, where the left-hand side is `Real.log 0 = 0`.

Under the Lindelöf hypothesis with parameter `ε` and constant `C`, every point `z` of that circle
has `re z ≥ 3 − R > 1/2` and `2 ≤ y − R ≤ im z ≤ y + 3` once `y ≥ 5`, so
`‖ζ(z)‖ ≤ C (y+3)^ε`; enlarging `C` to `max C 1` makes the bound at least `1`, and
`log (C (y+3)^ε) = log C + ε log (y+3)`.

Finally a window of unit height is covered by `m = ⌈1/(2κ)⌉` discs: the zero of ordinate `im ρ`
belongs to the disc of index `⌈(im ρ − T)/(2κ)⌉ − 1`, which lies in `range m` because
`0 < (im ρ − T)/(2κ) ≤ 1/(2κ) ≤ m`.  Summing the `m` disc estimates and using
`log (y_j + 3) ≤ log 2 + log T` (valid since `y_j + 3 ≤ T + 4.25 ≤ 2T` for `T ≥ 5`) gives the
quantitative bound with `ε` replaced by `ε log(R/r)/(2m)` chosen in advance, and the limit
statement follows by taking `T ≥ exp(2A/δ)`.

The two-sided form is the one-sided one plus the reflection `ρ ↦ 1 − conj ρ`, which by
`riemannZeta_one_sub_conj_eq_zero` (`RiemannHypothesis/BohrLandau.lean`) sends zeroes of the
window to zeroes of the same window and exchanges the two sides of the critical line; hence
`zerosOffCriticalLineWindow δ T (T+1) ⊆ A ∪ refl '' A` with
`A = zerosRightOfWindow (1/2 + δ) T (T+1)`, and `Set.ncard_union_le` together with
`Set.ncard_image_le` gives the factor `2`.

The unconditional comparison is a subset argument: for `T ≥ 25` every element of
`zerosRightOfWindow σ T (T+1)` has positive ordinate, hence lies in the critical strip
(`mem_strip_of_zero_of_im_pos`) and has `|im ρ − T| ≤ 1`, so it belongs to `zerosNearHeight T`,
whose count is at most `41 log T` by `ncard_zerosNearHeight_le` of
`RiemannHypothesis/ZeroCountLocal.lean`.  Finiteness of `zerosNearHeight T`, needed for
`Set.ncard_le_ncard`, comes from `finite_setOf_zeros` applied to `ξ` on the disc of radius `20`
about `4 + i T`.

## Verification

* `lake build RiemannHypothesis.LindelofDensity` succeeds; the module contains no `sorry`.
* `#print axioms` for `card_filter_le_log_max`, `card_filter_le_of_lindelof`,
  `card_le_sum_card_filter`, `exists_ncard_zerosRightOfWindow_le`,
  `tendsto_ncard_zerosRightOfWindow_div_log`, `ncard_zerosOffCriticalLineWindow_le`,
  `tendsto_ncard_zerosOffCriticalLineWindow_div_log` and
  `exists_ncard_zerosRightOfWindow_le_log` reports exactly
  `[propext, Classical.choice, Quot.sound]` (checked in `scripts/audit.sh`).
* The statements are pinned verbatim in `scripts/revalidation.lean`, including the two
  definitional pins for `LindelofHypothesis` and `zerosRightOfWindow`.
* The two conditional theorems appear in `docs/goal/conditional-theorems.txt`, which
  `scripts/audit.sh` diffs against the environment.

## Adversarial revalidation: M2-LINDELOF-DENSITY

* **Is anything unconditional claimed that is not?**  No.  The unconditional statements are
  `card_filter_le_log_max`, `card_le_sum_card_filter` and
  `exists_ncard_zerosRightOfWindow_le_log`; the first two are pure estimates: the first needs an
  upper bound `M` supplied from outside, the second is a covering statement about ordinates.
  The third is the `O(log T)` bound, which is a restriction of an already proved unconditional
  theorem of `RiemannHypothesis/ZeroCountLocal.lean` and claims nothing new.  The theorems that
  do improve on it carry `LindelofHypothesis` as an explicit hypothesis and are listed in the
  conditional manifest.
* **Is the hypothesis vacuous or self-defeating?**  `LindelofHypothesis` is the classical
  statement, restricted to `im s ≥ 2` (so that the pole at `s = 1` is irrelevant) and to
  `re s ≥ 1/2`.  It is not provably false — for `re s ≥ 2` the bound holds with `C = ζ(2)` —
  and it is not proved here; it is a genuine open hypothesis, weaker than the Riemann
  hypothesis.  So the theorems are neither vacuous nor circular, but they are also not
  unconditional progress on the zeroes.
* **Is the conclusion stronger than what is known unconditionally?**  Yes, and only just: the
  unconditional bound for the same count is `O(log T)` (the local Riemann–von Mangoldt bound,
  `RiemannHypothesis/ZeroCountLocal.lean`), and the conclusion here is `o(log T)`.  The saving
  is exactly the content of Backlund's criterion.  That comparison is no longer left to prose:
  `exists_ncard_zerosRightOfWindow_le_log` proves the `O(log T)` bound for the very same set
  `zerosRightOfWindow σ T (T+1)`, so the two statements can be read side by side.
* **Does anything here bear on the Riemann hypothesis?**  No.  The Lindelöf hypothesis follows
  from the Riemann hypothesis classically, so a theorem conditional on it says nothing new
  under RH, and it says nothing at all unconditionally.
* **Multiplicities.**  Zeroes are counted without multiplicity: `zerosRightOfWindow` is a set of
  points and `Set.ncard` counts points.  Jensen's inequality would tolerate multiplicities, so
  this is a weakening, recorded rather than hidden.
* **Constants.**  Not optimized.  `A` depends on `σ` and `ε` through `⌈1/(2κ)⌉`, `log(R/r)` and
  the Lindelöf constant `C(ε)`; no attempt is made to track the dependence, which is legitimate
  because the conclusion is a limit statement.
