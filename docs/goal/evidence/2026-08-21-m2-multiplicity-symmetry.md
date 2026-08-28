# Evidence: the symmetries preserve multiplicities, so the counts with multiplicity are even and divisible by four (2026-08-21)

Row: `M2-MULTIPLICITY-SYMMETRY` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroMultiplicitySymmetry.lean`, with
`zeroMultiplicity ρ = (analyticOrderAt riemannZeta ρ).toNat` as in `Zeta23Bridge`:

* `analyticAt_conj_conj`, `analyticOrderAt_conj_conj` : for any `f : ℂ → ℂ` and any `z₀`, the
  function `z ↦ conj (f (conj z))` is analytic at `conj z₀` whenever `f` is analytic at `z₀`, and
  **its vanishing order at `conj z₀` equals the order of `f` at `z₀`** (all three cases: not
  analytic, order `⊤`, order a natural number);
* `analyticAt_riemannZeta`, `analyticAt_completedRiemannZeta` : `ζ` is analytic away from `1` and
  `Λ` away from `{0, 1}`;
* `analyticOrderAt_completedRiemannZeta_eq` : inside the critical strip `ζ` and `Λ` vanish to the
  same order;
* `zeroMultiplicity_conj`, `zeroMultiplicity_one_sub`, `zeroMultiplicity_criticalReflect` :
  **the multiplicity of a zero in the critical strip is unchanged by `s ↦ conj s`, by
  `s ↦ 1 - s`, and by the reflection `s ↦ 1 - conj s` in the critical line**;
* `multCount T = ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ` and
  `offLineMultCount T = ∑ᶠ ρ ∈ offLineNontrivialZeros T, zeroMultiplicity ρ` : the counting
  functions *with* multiplicity;
* `multCount_eq_two_mul`, `even_multCount` : **`N(T)` counted with multiplicity is even**;
* `offLineMultCount_eq_four_mul`, `four_dvd_offLineMultCount` : **the off-line count with
  multiplicity is four times the count of the upper-left off-line zeroes, hence divisible by
  four**.

This removes the caveat recorded on the rows `M2-ZERO-SYMMETRY-COUNT` and
`M2-OFF-LINE-QUADRUPLE`, whose parity and divisibility statements counted distinct zeroes only.

## The argument

* *Conjugation.* Vanishing order is a local, germ-level invariant. If `f` is analytic at `z₀` and
  `f z = (z - z₀)^n • g z` near `z₀` with `g z₀ ≠ 0`, then near `conj z₀`
  `conj (f (conj z)) = (z - conj z₀)^n • conj (g (conj z))`, and the new witness is again analytic
  and nonzero at the point. Analyticity of `z ↦ conj (h (conj z))` comes from
  `DifferentiableAt.conj_conj` on a neighbourhood on which `h` is analytic, followed by
  `DifferentiableOn.analyticAt`. The `⊤` case and the non-analytic case are transferred the same
  way. Applied to `ζ`, the repository's `riemannZeta_conj_of_mem_strip` says `ζ` agrees with
  `z ↦ conj (ζ (conj z))` on the (open) critical strip, so the two orders coincide.
* *Reflection.* `Λ(1 - s) = Λ(s)` (Mathlib's `completedRiemannZeta_one_sub`) means
  `Λ ∘ (1 - ·) = Λ`, and `analyticOrderAt_comp_of_deriv_ne_zero` (the inner map has derivative
  `-1 ≠ 0`) turns this into `order Λ (1 - ρ) = order Λ ρ`. Inside the strip
  `ζ = Λ · (Γ_ℝ)⁻¹` with `(Γ_ℝ)⁻¹` entire (`differentiable_Gammaℝ_inv`) and nonzero
  (`Gammaℝ_ne_zero_of_re_pos`), so `order ζ = order Λ` there by `analyticOrderAt_mul`. Composing
  the two symmetries gives the statement for `criticalReflect`.
* *Counting.* The set decompositions of `ZeroSymmetryCount` and `OffLineQuadruple` are reused
  verbatim; `finsum_mem_union` replaces `Set.ncard_union_eq` and `finsum_mem_image` replaces
  `Set.ncard_image_of_injective`, with `finsum_mem_congr` and the three multiplicity lemmas
  showing that the reindexed summands are unchanged.

## Commands run

```
lake build RiemannHypothesis.ZeroMultiplicitySymmetry
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for each result reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Nothing about whether off-line zeroes exist.** As before, the Riemann hypothesis is neither
  proved nor disproved; `four_dvd_offLineMultCount` would hold trivially if `N_off ≡ 0`.
* **No zero is shown to be simple.** The multiplicities are only shown to match across the
  symmetries; the simplicity results of the repository come from the vendored `Zeta23` library.
* **No location and no rate.** Nothing here constrains the real parts of the zeroes or the growth
  of `N(T)`.

## Adversarial revalidation: M2-MULTIPLICITY-SYMMETRY

Second, independent pass.

* **Claim mode.** Every result is a `theorem` of this repository, pinned in full in
  `scripts/revalidation.lean` (including `rfl`-pins of `multCount` and `offLineMultCount`, so the
  counting functions cannot be redefined into something trivial), and axiom-checked in
  `scripts/audit.sh`.
* **Vacuity check.** `analyticOrderAt_conj_conj` is a statement about *arbitrary* functions
  `f : ℂ → ℂ` with no hypotheses, so it cannot be vacuous; it is proved in all three cases rather
  than by excluding degenerate ones. `zeroMultiplicity_conj` and `zeroMultiplicity_one_sub` are
  asserted for every point of the open strip, not only for zeroes, so they are not vacuous even
  if a zero were missing; at a non-zero of `ζ` both sides are `0`, which is the correct value.
* **Is `zeroMultiplicity` a junk value?** `analyticOrderAt` returns `0` both at a non-zero and at
  a point of non-analyticity, and `toNat` sends `⊤` to `0`. Neither degeneracy is used: `ζ` is
  analytic on the whole strip (`analyticAt_riemannZeta`), and where `ζ` vanishes the order is a
  genuine positive natural number, since `ζ` is not identically zero. The transfer statements are
  equalities, so they hold in the degenerate cases too rather than relying on them.
* **Direction check.** The reflection argument goes through `Λ`, not `ζ`, because `ζ` itself has
  no functional equation of the form `ζ(1-s) = ζ(s)`; the `Γ_ℝ` factor is where the strip
  hypothesis `0 < re s` is genuinely needed (`Γ_ℝ` vanishes nowhere but has poles at the
  nonpositive even integers, which the strip avoids).
* **Is it circular?** No: the inputs are Mathlib's `completedRiemannZeta_one_sub`,
  `differentiable_Gammaℝ_inv`, `analyticOrderAt_comp_of_deriv_ne_zero` and the repository's
  `riemannZeta_conj_of_mem_strip` (`M0-SYMMETRY`) and set decompositions
  (`M2-ZERO-SYMMETRY-COUNT`, `M2-OFF-LINE-QUADRUPLE`); none of them uses this row.
* **Sanity check against the literature.** That `ρ`, `conj ρ`, `1-ρ`, `1-conj ρ` are zeroes of the
  same multiplicity is the standard consequence of the functional equation and the reality of the
  Dirichlet coefficients; classical statements of `N(T)` count with multiplicity and are indeed
  even in the symmetric range `|im ρ| ≤ T`. What is new here is only the machine-checked proof.
