# M1-ZETA-RECTANGLE-COUNT — the rectangle count and the argument principle, for `ζ` itself

Date: 2026-08-24
File: `RiemannHypothesis/ZetaRectangleCount.lean`

## Claim

`RiemannHypothesis.RectangleZeroCount` and `RiemannHypothesis.RectangleArgumentPrinciple` state
the rectangle machinery for an arbitrary function of a complex variable. This row attaches it to
the object of the repository. Write `R` for the closed rectangle with corners `z` and `w`.

* `rectZeros_xiFn_eq` — `rectZeros xiFn z w = Rectangle z w ∩ nontrivialZeroSet`: the zeroes of
  `ξ` in a rectangle are exactly the nontrivial zeroes of `ζ` in it, so `rectZeroCount xiFn`
  counts nontrivial zeroes and nothing else.
* `rectZeros_xiFn_finite` — that set is finite, for *every* rectangle and with no side
  hypothesis. The general lemma `rectZeros_finite` needs a point of the rectangle at which the
  function does not vanish, which a bare rectangle need not supply; here the finiteness comes
  from `finite_nontrivialZeros` at the height `max |z.im| |w.im|`.
* `rectZeros_riemannZeta_eq_xiFn`, `rectZeroCount_riemannZeta_eq_xiFn`,
  `rectZeros_riemannZeta_finite` — for a rectangle in the open strip `0 < re s < 1`, `ζ` and `ξ`
  have the same zeroes with the same multiplicities (`analyticOrderAt_xiFn_eq`), hence the same
  count.
* `analyticOnNhd_riemannZeta_rectangle` — `ζ` is analytic on a neighbourhood of such a
  rectangle: lying in the strip, it avoids the pole at `s = 1`.
* `zeta_rectangle_argument_principle` — for a rectangle in the open strip carrying no zero of
  `ζ` on its border, `(1/2πi) ∮_{∂R} ζ′/ζ = rectZeroCount riemannZeta z w`; and
  `zeta_rectangleIntegral'_logDeriv_eq_zero` for the zero-free case.
* `integral_rectZeroCount_riemannZeta_eq_finsum`,
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum` — Littlewood's identity in
  counting form for `ζ`: integrating over `σ ∈ [z.re, w.re]` the number of zeroes of `ζ` to the
  right of `re s = σ` gives `∑_ρ m_ρ (re ρ − z.re)`, in the second statement with the count
  replaced by the contour integral of `ζ′/ζ`.

## Proof

Nothing analytic is new here: the analytic content is the argument principle of
`RectangleArgumentPrinciple` (which rests on the vendored `Zeta23` contour machinery) and the
layer-cake identity of `RectangleZeroCount`. What is proved is the dictionary — that the zeroes
being counted are the nontrivial zeroes of `ζ`, that the multiplicities of `ζ` and `ξ` agree
inside the strip, that the finiteness hypothesis can be discharged unconditionally for `ξ`, and
that the analyticity hypothesis can be discharged for `ζ` on a rectangle in the strip.

## Scope — what is *not* claimed

Littlewood's lemma proper — rewriting the contour integral of `ζ′/ζ` as an integral of `log ζ`
over the border — is not proved, here or anywhere in the repository; that remains the open
boundary of `M1-RECTANGLE-ARGUMENT-PRINCIPLE`. No bound on the number of zeroes in a rectangle
is obtained from these statements: they are identities, and every quantitative zero count in
the repository still comes from the Jensen route of `RiemannHypothesis.ZeroCount`. In
particular nothing here bears on `M1-ALMOST-ALL-STRIP` beyond providing the counting tool it
was waiting for.

## Adversarial revalidation: M1-ZETA-RECTANGLE-COUNT

* `lake build RiemannHypothesis.ZetaRectangleCount` succeeds inside a full `lake build` of the
  repository; the module contains no `sorry`.
* `#print axioms` for `zeta_rectangle_argument_principle`,
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum`,
  `rectZeroCount_riemannZeta_eq_xiFn` and `rectZeros_xiFn_finite` reports exactly
  `[propext, Classical.choice, Quot.sound]`.
* The claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statements are not vacuous: the hypotheses `0 < z.re`, `w.re < 1`, `z.re ≤ w.re`,
  `z.im ≤ w.im` describe a non-degenerate family of rectangles inside the strip, and
  `rectZeros_xiFn_eq` identifies the counted set with `Rectangle z w ∩ nontrivialZeroSet`, which
  is non-empty for suitable corners because `nontrivialZeroSet` is infinite
  (`infinite_nontrivialZeroSet`). The border hypothesis of the argument principle is a genuine
  restriction, not a disguised contradiction: it is satisfied whenever the border misses the
  countable set of nontrivial zeroes.
* Every statement is unconditional; none takes an unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.

## Amendment (2026-08-24): one statement of this row was vacuous, and is superseded

The vacuity check above was carried out for the argument principle, whose border hypothesis is
indeed a genuine restriction. It was *not* carried out for the contour-integral form of
Littlewood's identity, and that statement turns out to be vacuous as it stands:

* `RiemannHypothesis.rectZeros_eq_empty_of_forall_leftCorner_border` (proved in
  `RiemannHypothesis/RectangleArgumentPrinciple.lean`) shows that the hypothesis
  `∀ σ ∈ Icc z.re w.re, ∀ s ∈ RectangleBorder (leftCorner σ z) w, f s ≠ 0` — zero-freeness on
  the border of *every* truncation — forces `rectZeros f z w = ∅`. Indeed a zero `ρ` inside the
  rectangle lies on the *left* edge of the rectangle truncated at `σ = re ρ`, and that left edge
  is part of the truncated border. So both sides of
  `integral_rectangleIntegral'_logDeriv_eq_finsum` and of its `ζ` specialization
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum` are zero whenever the hypotheses
  hold: the statements are true, but carry no content.
* Both statements are kept — earlier work refers to them — with a warning in their docstrings,
  and are superseded by
  `integral_rectangleIntegral'_logDeriv_eq_finsum_of_border` and
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border`, which assume
  zero-freeness only on the border of the rectangle itself, exactly as the argument principle
  does. These are not vacuous: the hypothesis is satisfied by any rectangle whose border misses
  the zeroes, and the right-hand side is then a nonzero sum as soon as the rectangle contains a
  zero.
* The proof of the corrected form: `rectangleBorder_leftCorner_subset` shows that the border of
  the rectangle truncated at `σ` is contained in the border of the whole rectangle together with
  the line `re s = σ` — the bottom, top and right edges shrink into the corresponding outer
  edges, and only the new left edge is new. Hence the truncated border is zero-free for every
  `σ` outside the image of the (finite) zero set under `re`, a null set, and the argument
  principle applies for almost every `σ`; `intervalIntegral.integral_congr_ae` then reduces the
  claim to the layer-cake identity `integral_rectZeroCount_eq_finsum`.
* The corrected statements are pinned in `scripts/revalidation.lean` and their axioms are
  checked in `scripts/audit.sh`; both report exactly `[propext, Classical.choice, Quot.sound]`.

## Addendum (2026-08-25): Littlewood's lemma for `ζ`

`RiemannHypothesis/Littlewood.lean` proves Littlewood's lemma for an arbitrary function of a
complex variable (row `M1-RECTANGLE-ARGUMENT-PRINCIPLE`, evidence
`docs/goal/evidence/2026-08-25-m1-littlewood.md`). `RiemannHypothesis/ZetaLittlewood.lean`
attaches it to `ζ`, discharging its hypotheses through
`analyticOnNhd_riemannZeta_rectangle`:

* `zeta_littlewood_lemma` — for a rectangle inside the open critical strip on whose border `ζ`
  does not vanish, `2π ∑_ρ m_ρ (re ρ − z.re)` equals the integral over the height of
  `log ‖ζ‖` on the left side minus `log ‖ζ‖` on the right side, plus the two horizontal argument
  terms and the right-hand vertical argument term.
* `zeta_littlewood_lemma_arg` — the same with the horizontal terms written as increments of
  genuine continuous arguments of `ζ` along the bottom and the top side.
* `rectZeros_riemannZeta_eq_inter`, `zeta_littlewood_lemma_nontrivialZeros` — the set summed
  over is `Rectangle z w ∩ nontrivialZeroSet`, so the sum is over the nontrivial zeroes of `ζ`
  in the rectangle and nothing else.

Nothing analytic is new here; the content is the dictionary of this row applied to the general
lemma. The statements are unconditional, contain no `sorry`, report exactly
`[propext, Classical.choice, Quot.sound]` under `#print axioms` (checked in `scripts/audit.sh`),
and are pinned in `scripts/revalidation.lean`. They are identities, not bounds: no zero-density
estimate follows without upper and lower bounds for `log ‖ζ‖` on the two vertical sides.
