# M1-RECTANGLE-ARGUMENT-PRINCIPLE — the argument half, and Littlewood's lemma

Date: 2026-08-25
Files: `RiemannHypothesis/ArgumentSegment.lean`, `RiemannHypothesis/Littlewood.lean`

## Claim

This closes the open boundary of the row: "Littlewood's lemma proper — rewriting the contour
integral of `f′/f` as boundary data — is not proved. … Missing are the argument (imaginary)
half, which is where a branch of `log` is needed, and the Fubini step that assembles the four
sides after integrating in `σ` across the rectangle."

Both are now proved, for an arbitrary function of a complex variable.

### The argument half (`RiemannHypothesis/ArgumentSegment.lean`)

* `exp_integral_logDeriv_comp` — for `g : ℝ → ℂ` differentiable and nonvanishing on the segment
  joining `a` and `b`, with continuous `g′/g`, `exp (∫_a^b g′/g) = g b / g a`. The proof is the
  standard one: the primitive `F u = ∫_a^u g′/g` makes `u ↦ g u · exp (−F u)` have derivative
  zero on the segment, so it is constant (`constant_of_has_deriv_right_zero`).
* `exists_continuousOn_arg` — hence `θ u = arg (g a) + im (F u)` is a **continuous branch of the
  argument** of `g` along the segment: `g u = ‖g u‖ · exp (i θ u)` for every `u`, and each
  increment `θ v − θ u` is `im (∫_u^v g′/g)`. No branch cut is chosen and no monodromy is
  assumed away — the logarithm is built by integration.
* `exists_continuousOn_arg_horizontal`, `exp_HIntegral_logDeriv`, `exp_VIntegral_logDeriv` — the
  same for a horizontal, respectively a vertical, side of a rectangle, in the vocabulary of the
  vendored `Zeta23` contour integrals `HIntegral` and `VIntegral`.
* `exp_rectangleIntegral_logDeriv_eq_one`, `exists_int_rectangleIntegral_logDeriv`,
  `exists_int_rectangleIntegral'_logDeriv` — around the four sides the ratios telescope, so
  `exp (∮_{∂R} f′/f) = 1`, i.e. the **winding number `(1/2πi) ∮_{∂R} f′/f` is an integer**,
  assuming only that `f` is analytic and nonvanishing *on the border*: nothing is assumed about
  the inside of the rectangle, where `f` may have zeroes, poles, or fail to be defined. Together
  with `im_rectangleIntegral'_logDeriv_eq_zero` (the modulus half, `RectangleLogModulus.lean`)
  this upgrades "the normalized contour integral is real" to "it is an integer".

### The Fubini step and Littlewood's lemma (`RiemannHypothesis/Littlewood.lean`)

* `integrableOn_logDeriv_prod_rectangle` — `(σ, t) ↦ f′/f (σ + i t)` is integrable on the
  rectangle, for `f` analytic on a neighbourhood of it and not identically zero there, *even
  though it blows up at the zeroes inside*: near a zero `ρ` of order `m` the
  logarithmic derivative is `m/(s − ρ)` plus a bounded term, and `1/‖s − ρ‖` is integrable in two
  real dimensions (`RiemannHypothesis/LogDerivIntegrable.lean`).
* `integral_integral_re_logDeriv_eq_integral_log_norm_of_border` — the **Fubini step**: the
  double integral of `re (f′/f)` over the rectangle may be computed in either order. Integrating
  first in `σ` gives the increment of `log ‖f‖` along a horizontal line, which is legitimate for
  all but the finitely many heights that meet a zero — a null set. Hence
  `∫_σ ∫_t re (f′/f) = ∫_t (log ‖f (w.re + i t)‖ − log ‖f (z.re + i t)‖)`.
* `littlewood_lemma` — **Littlewood's lemma**:

  `2π ∑_ρ ord_ρ(f) (re ρ − z.re)`
    `= ∫_{z.im}^{w.im} (log ‖f (z.re + i t)‖ − log ‖f (w.re + i t)‖) dt`
    `+ ∫_{z.re}^{w.re} im (∫ f′/f along the bottom from σ to w.re) dσ`
    `− ∫_{z.re}^{w.re} im (∫ f′/f along the top from σ to w.re) dσ`
    `+ (w.re − z.re) · im (∫ f′/f up the right side)`,

  for `f` analytic on a neighbourhood of the closed rectangle and nonvanishing on its border,
  the sum being over the zeroes inside, with multiplicity.
* `littlewood_lemma_arg` — the same with the two horizontal terms written as increments
  `θb w.re − θb σ`, `θt w.re − θt σ` of *genuine continuous arguments* `θb`, `θt` of `f` along
  the bottom and the top side, produced by `exists_continuousOn_arg_horizontal`.

## Proof

The counting identity `integral_rectangleIntegral'_logDeriv_eq_finsum_of_border` already says
that the `σ`-integral of the normalized contour integrals of `f′/f` over the truncated rectangles
is `∑_ρ ord_ρ (re ρ − z.re)`. For a fixed `σ` avoiding the finitely many abscissae of zeroes,
the real part of that normalized contour integral is, by `re_rectangleIntegral'_eq_im_div` and
`im_VIntegral_eq_integral_re`, `1/(2π)` times

`im H(σ, w.re, z.im) − im H(σ, w.re, w.im) + im V(w.re, z.im, w.im) − ∫_t re (f′/f) (σ + i t)`.

Integrating in `σ` and using the Fubini step on the last term gives the lemma; the three other
terms are interval-integrable because their integrands are continuous in `σ`
(`continuousOn_im_HIntegral_logDeriv`, and `intervalIntegrable_integral_re_logDeriv` for the
fourth). The vertical term is constant in `σ`, which is where the factor `w.re − z.re` comes
from.

## Scope — what is *not* claimed

Littlewood's lemma is an identity: no bound on the number of zeroes in a rectangle follows from
it without an upper bound for `log ‖f‖` on the right edge and a lower bound on the left edge.
Nothing here is specialized to `ζ` or `ξ`; that specialization, and any zero-density consequence,
is separate work. Nothing here bears on the Riemann hypothesis itself.

## Adversarial revalidation: M1-RECTANGLE-ARGUMENT-PRINCIPLE

* `lake build` of the whole repository succeeds, `RiemannHypothesis.ArgumentSegment` and
  `RiemannHypothesis.Littlewood` among its targets; both modules are imported by
  `RiemannHypothesis.lean` and contain no `sorry`.
* `#print axioms` for `exists_continuousOn_arg`, `exists_continuousOn_arg_horizontal`,
  `exists_int_rectangleIntegral'_logDeriv`, `integrableOn_logDeriv_prod_rectangle`,
  `integral_integral_re_logDeriv_eq_integral_log_norm_of_border`, `littlewood_lemma` and
  `littlewood_lemma_arg` reports exactly `[propext, Classical.choice, Quot.sound]`; the checks
  are in `scripts/audit.sh`.
* The claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statements are not vacuous. The hypotheses are `z.re ≤ w.re`, `z.im ≤ w.im`, analyticity
  on a neighbourhood of the closed rectangle and nonvanishing on the border; they are satisfied,
  for instance, by any polynomial whose zeroes avoid the border, and then the left-hand side
  `2π ∑_ρ ord_ρ (re ρ − z.re)` is a nonzero number as soon as a zero lies strictly to the right
  of the left edge. Zeroes *inside* the rectangle are allowed — that is the whole point, and it
  is what forces the integrability argument of `LogDerivIntegrable.lean`.
* Every statement is unconditional; none takes an unproved `Prop` of this repository as a
  hypothesis, and the modules add no row to `docs/goal/conditional-theorems.txt`.
