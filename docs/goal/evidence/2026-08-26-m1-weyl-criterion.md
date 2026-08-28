# M1-WEYL-CRITERION — Weyl's criterion, and equidistribution of `α n²`

Date: 2026-08-26
File: `RiemannHypothesis/WeylCriterion.lean`

## Claim

Write `𝕋 = AddCircle 1 = ℝ/ℤ` with its Haar probability measure `haarAddCircle`, and for a real
sequence `x : ℕ → ℝ`

* `EquidistributedMod1 x` : for every `f ∈ C(𝕋, ℂ)`, `(1/N) ∑_{n<N} f(x n) → ∫ f`;
* `WeylSumsVanish x` : for every nonzero integer `m`, `‖∑_{n<N} e(m x n)‖ / N → 0`.

The module proves

* `integral_fourier_eq_zero` — `∫ fourier m = 0` for `m ≠ 0`;
* `equidistributedMod1_of_weylSumsVanish` and `weylSumsVanish_of_equidistributedMod1`, hence
  **Weyl's criterion** `equidistributedMod1_iff_weylSumsVanish` : `EquidistributedMod1 x ↔
  WeylSumsVanish x`;
* `not_equidistributedMod1_const_zero` — a constant sequence is not equidistributed, so the
  notion is not vacuous;
* `equidistributedMod1_quadratic` — **for every irrational `α`, the sequence `α n²` is
  equidistributed modulo one**.

## Proof

The set of `f ∈ C(𝕋, ℂ)` whose averages along `x` converge to `∫ f` is a `ℂ`-submodule
(`weylTest`): both the average and the integral are linear in `f`, integrability of a continuous
function against a probability measure being immediate.  It is closed (`isClosed_weylTest`): an
average and an integral are each `1`-Lipschitz for the uniform norm (`dist_avg_le`,
`dist_integral_le`), so a three-epsilon argument passes the property to uniform limits.

It contains every character.  For `m = 0`, `fourier 0 = 1` and both sides are `1`.  For `m ≠ 0`
the average is exactly `(1/N) ∑_{n<N} e(m x n)` (`fourier_coe_eq_e2pi`), which the hypothesis
sends to `0`, and the mean of the character is `0`: pulling the integral back to `[0,1]`
(`AddCircle.intervalIntegral_preimage`, `volume_eq_smul_haarAddCircle`) it is
`∫₀¹ exp(2πi m t) dt = (e^{2πim} − 1)/(2πim) = 0`.

Since the span of the characters is dense in `C(𝕋, ℂ)` — Stone–Weierstrass, in the form
`span_fourier_closure_eq_top` — a closed submodule containing them is everything, which is the
criterion.  The converse direction is the special case `f = fourier m`.

For the application, `M1-WEYL-EQUIDISTRIBUTION` gives exactly `WeylSumsVanish` for the sequence
`α n²` when `α` is irrational: the frequency `m` sum is the quadratic Weyl sum of the irrational
number `mα`.

## Why this row exists

`M1-WEYL-EQUIDISTRIBUTION` closes with a family of exponential-sum estimates and records in its
open boundary that the criterion turning them into a distribution statement is not formalized —
mathlib has no Weyl criterion.  This row supplies it, and thereby the classical theorem of Weyl
on the fractional parts of `α n²`.

## Scope, and what is *not* claimed

* Equidistribution is formulated against **continuous test functions** (the Riesz/portmanteau
  form).  The equivalent statement about counting `n < N` with fractional part in a subinterval
  is not derived: that needs an approximation of indicator functions from above and below, which
  is not formalized here.
* No rate is claimed, in either the criterion or the application; the input estimates carry none.
* Only the quadratic case is applied.  Weyl's theorem for a general polynomial with an irrational
  leading coefficient needs the A process iterated, which is not proved.
* Nothing about `ζ` is claimed, and nothing here bears on the Riemann hypothesis.

## Adversarial revalidation: M1-WEYL-CRITERION

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylCriterion`
  succeeds, the file contains no `sorry`, and it triggers no linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the four main
  statements (checked in `scripts/audit.sh`).
* The statements are pinned in `scripts/revalidation.lean` with the definitions
  `EquidistributedMod1` and `WeylSumsVanish` **written out in full**, so neither definition can be
  weakened without breaking the audit.
* The definitions are not vacuous or trivially satisfiable: `not_equidistributedMod1_const_zero`
  proves that the constant sequence `0` is *not* equidistributed (its Weyl sums at frequency `1`
  have quotient constantly `1`), so `EquidistributedMod1` is a genuine restriction, and the
  criterion is an equivalence, not a one-sided implication.
* The irrationality hypothesis in the application is load-bearing: for `α = 0` the sequence is
  constantly `0`, which the previous item shows is not equidistributed.
* No unproved `Prop` of this repository occurs as a hypothesis.  The manifest
  `docs/goal/conditional-theorems.txt` does record the entries
  `equidistributedMod1_of_weylSumsVanish <- WeylSumsVanish` and
  `weylSumsVanish_of_equidistributedMod1 <- EquidistributedMod1`, but those two `Prop`s are the
  *definitions* the criterion relates, not conjectures: each is proved outright for the quadratic
  sequence in `equidistributedMod1_quadratic`, which is unconditional.
