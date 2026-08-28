# M1-VAN-DER-CORPUT — the derivative tests for exponential integrals

Date: 2026-08-26
File: `RiemannHypothesis/VanDerCorput.lean`

## Claim

For a real phase `F` and `expI F x = e^{i F(x)}`:

* **first-derivative test** (`norm_integral_expI_le_of_abs_deriv_ge`) — if on `[a,b]` the second
  derivative `F''` has a constant sign (equivalently `F'` is monotone) and `|F'| ≥ m > 0`, then

      ‖∫_a^b e^{i F(x)} dx‖ ≤ 4/m ;

* **second-derivative test** (`norm_integral_expI_le_of_deriv_two_ge`) — if `F'' ≥ r > 0` on
  `[a,b]`, then

      ‖∫_a^b e^{i F(x)} dx‖ ≤ 12/√r .

Neither bound depends on the length `b − a` of the range: that is the whole content.  The second
test assumes no lower bound on `|F'|`, which may vanish — it can do so only once.

The worked instance is the exponential integral of `ζ`-theory, `x^{-it} = e^{-i t log x}`:

    ‖∫_A^B x^{-it} dx‖ ≤ 4B/t          (norm_integral_expI_logPhase_le)
    ‖∫_A^B x^{-it} dx‖ ≤ 12B/√t        (norm_integral_expI_logPhase_le_sqrt)

for `0 < A ≤ B`, `t > 0`.

## Proof

The first test is integration by parts against the amplitude `G = 1/F'`.  Since
`e^{iF} = G · (e^{iF})' / i`,

    i ∫_a^b e^{iF} = [G e^{iF}]_a^b − ∫_a^b G' e^{iF} .

The two boundary terms are at most `1/m` each because `|G| ≤ 1/m`; and `G' = −F''/(F')²` has a
constant sign, so `∫ |G'| = |G(b) − G(a)| ≤ 2/m`.  Total `4/m`.

The second test splits `[a,b]` at `u = sup {x : F'(x) ≤ 0}` (taken with `a` adjoined, so that no
existence argument is needed): with `δ = 1/√r`, every `y ≤ u − 2δ` has `F'(y) ≤ −√r` and every
`y ≥ u + 2δ` has `F'(y) ≥ √r`, because `F'` grows at rate at least `r`.  The two outer pieces are
handled by the first test (`4/√r` each) and the middle piece, of length at most `4δ = 4/√r`, by
the trivial bound.  Total `12/√r`.

The constants `4` and `12` are what these proofs give; the classical write-ups have `4` and `8`,
and no attempt was made to optimize.

## Why this row exists

These are the analytic engine of the two things the repository is missing and that the board
cites most often:

* the **approximate functional equation** for `ζ` on the critical line, whose proof evaluates
  exponential integrals by stationary phase and whose error terms are exactly first- and
  second-derivative-test bounds; and
* the **Weyl bound** `ζ(1/2+it) ≪ t^{1/6+ε}`, which is the derivative test for *sums* — Poisson
  summation converts the sums into precisely the integrals bounded here.

Neither test is in Mathlib.

## Scope, and what is *not* claimed

* Only the tests for **integrals** are proved.  The tests for **sums** (Kusmin–Landau, and the
  van der Corput `A`/`B` processes) are not, and they are what a bound for `ζ` needs.
* No consequence for `ζ` is drawn in this file: no subconvexity bound, no approximate functional
  equation, no density estimate.  The row is infrastructure.
* The third-derivative test, needed for the exponent pair `(1/6, 2/3)`, is not proved.

## Adversarial revalidation: M1-VAN-DER-CORPUT

* The module is imported by `RiemannHypothesis.lean`, `lake build` succeeds, and the file
  contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the two tests and
  the two corollaries.
* The statements are not vacuous: the hypotheses are satisfiable (the two `logPhase` corollaries
  are instances with `F(x) = −t log x`, `F''(x) = t/x² > 0`), and the conclusions are finite
  bounds that improve on the trivial bound `b − a` for long ranges.
* The statements are unconditional: no unproved `Prop` of this repository occurs as a hypothesis,
  so `docs/goal/conditional-theorems.txt` is unchanged.
* The bounds are of the classical shape and are not stronger than the classical ones: `4/m`
  against the classical `4/m`, and `12/√r` against the classical `8/√r`.
