# M2-WEIL-TESTFUNCTIONS — convolution squares are positive test functions

Date: 2026-08-22
Module: `RiemannHypothesis/WeilTestFunctions.lean` (imported by `RiemannHypothesis.lean`)

## Why this row exists

`RiemannHypothesis/WeilPositivity.lean` states Weil's criterion on the class
`IsPositiveTestFunction k` — `k` is `C²` with compact support and its transform
`h(r) = ∫ k(u) e^{i r u} du` is a nonnegative real for every real `r`.  Nothing there showed
that the class contains anything but `0`, so both the criterion and the proved forward
implication `weilFunctional_nonneg_of_zetaForm` were, on the face of it, possibly vacuous.
This row removes that doubt by the classical construction `k = g ⋆ g^*`.

## What is proved

* `starReflect g x = conj (g (-x))` and `weilSquare g = g ⋆[mul ℂ ℂ, volume] starReflect g`,
  together with the stability lemmas `continuous_starReflect`, `hasCompactSupport_starReflect`,
  `contDiff_starReflect`, `integrable_starReflect`.
* `testTransform_ofReal` — the transform of the explicit formula is mathlib's Fourier integral:
  `testTransform k (r : ℂ) = 𝓕 k (−r / 2π)` for real `r`.  This is the bridge that lets the
  Fourier-analytic API of mathlib act on the vocabulary of `RiemannHypothesis.ExplicitFormula`.
* `fourier_starReflect` — `𝓕 (g^*) ξ = conj (𝓕 g ξ)` on the real axis.
* `testTransform_weilSquare` — for integrable `g`,
  `testTransform (weilSquare g) r = ‖𝓕 g (−r / 2π)‖²`, a nonnegative real.  It combines the
  convolution theorem `Real.fourier_mul_convolution_eq` with the previous item.
* `isPositiveTestFunction_weilSquare` — **for `g` of class `C²` with compact support,
  `weilSquare g` is a positive test function.**  Smoothness of the convolution comes from
  `HasCompactSupport.contDiff_convolution_right`, compact support from
  `HasCompactSupport.convolution`, and positivity of the transform from the previous item.
* `weilSquare_zero` — `weilSquare g 0 = ∫ ‖g t‖²`, the `L²` norm of `g`.
* `exists_isPositiveTestFunction_ne_zero` — **the class contains a nonzero function.**  Take
  `g` the (complexified) `C^∞` bump function with radii `1 < 2`; then `∫ ‖g‖² > 0` because the
  integrand is continuous, nonnegative, compactly supported and positive at `0`, so
  `weilSquare g 0 ≠ 0`.

## Scope and claim mode

* Nothing here proves the Riemann hypothesis, and nothing here proves the converse direction
  of Weil's criterion.  What is closed is exactly the nonvacuity gap: the class on which the
  criterion is stated is now known to be rich (it contains every convolution square) and in
  particular nonempty modulo `0`.
* `WeilPositivityCriterion` remains a `Prop` with no inhabitant in the repository; the open
  boundary of `M2-WEIL-POSITIVITY` has been narrowed to the converse implication only.
* No `sorry`; `#print axioms` on each result listed above yields exactly `propext`,
  `Classical.choice`, `Quot.sound` (checked in `scripts/audit.sh`).

## Adversarial revalidation: M2-WEIL-TESTFUNCTIONS

Each exit criterion is pinned in `scripts/revalidation.lean` (section
`M2-WEIL-TESTFUNCTIONS`) by an `example` whose statement is written out in full and whose
proof is the repository's declaration, so a weakening or renaming breaks the audit:

* `starReflect` and `weilSquare` are pinned definitionally (`rfl`), so the construction cannot
  be silently replaced by a different one;
* `testTransform_ofReal k r : testTransform k r = 𝓕 k (-(r / (2 * π)))`;
* `fourier_starReflect g ξ : 𝓕 (starReflect g) ξ = conj (𝓕 g ξ)`;
* `testTransform_weilSquare hg r : testTransform (weilSquare g) r = ‖𝓕 g (-(r / (2 * π)))‖²`;
* `weilSquare_zero g : weilSquare g 0 = ∫ t, ‖g t‖²`;
* `isPositiveTestFunction_weilSquare hg2 hgc : IsPositiveTestFunction (weilSquare g)`;
* `exists_isPositiveTestFunction_ne_zero : ∃ k, IsPositiveTestFunction k ∧ k ≠ 0`.

Checks run: `lake build`, `lake build RiemannHypothesis.WeilTestFunctions`,
`./scripts/audit.sh` (no `sorry` outside `Challenge.lean`, axioms exactly `propext`,
`Classical.choice`, `Quot.sound`, no `Float`), `python3 scripts/goal_state.py validate`.

Counter-check on the claim: the witness statement is `∃ k, IsPositiveTestFunction k ∧ k ≠ 0`,
an existence claim about the *unmodified* class `IsPositiveTestFunction` of
`RiemannHypothesis/WeilPositivity.lean` (whose definition is itself pinned in the
`M2-WEIL-POSITIVITY` material), so it cannot be met by weakening the class.  No term of type
`WeilPositivityCriterion` or `ZetaForm` is produced anywhere.
