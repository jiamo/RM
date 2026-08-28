# M1-LITTLEWOOD-BOUNDS — bounding the terms of Littlewood's lemma for `ζ`

Date: 2026-08-25
Files: `RiemannHypothesis/LittlewoodZetaBound.lean`, `RiemannHypothesis/ArgumentSegment.lean`,
`RiemannHypothesis/ZeroCountLocal.lean`

## Claim

`M1-ZETA-RECTANGLE-COUNT` closed with Littlewood's lemma for `ζ` as an *identity*: for a
rectangle inside the open critical strip on whose border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − σ) = ∫ (log ‖ζ‖ left − log ‖ζ‖ right) + (bottom arg) − (top arg)
  + (width) · (right arg)`.

This row bounds the terms of that identity, so that the obstruction to a zero-density estimate
is a single explicitly written quantity rather than "the identity is not a bound".  What is
proved is unconditional; what is *not* proved is any bound for the two horizontal argument
terms, and that is recorded as the open boundary of the row.

### Littlewood's lemma outside the strip

* `analyticOnNhd_riemannZeta_rectangle_of_im_pos` — `ζ` is analytic on a neighbourhood of every
  rectangle lying strictly above the real axis.  The only singularity of `ζ` is the pole at
  `s = 1`, whose imaginary part is `0`, so the hypothesis "the rectangle lies in the open strip"
  used by `zeta_littlewood_lemma` may be replaced by "the rectangle lies above the axis".
* `zeta_littlewood_lemma_above` — Littlewood's lemma for `ζ` on such a rectangle.  This is what
  allows the right side of the rectangle to be placed at the abscissa `3`, where `ζ` is close
  to `1`; inside the strip there is no abscissa at which `ζ` can be controlled.

### The right side: `re s = 3`

* `norm_riemannZeta_sub_one_le_half_of_three_le_re` (extracted from the existing proof of
  `half_le_norm_riemannZeta_of_three_le_re`, which is now derived from it) — for `re s ≥ 3`,
  `‖ζ(s) − 1‖ ≤ 1/2`.
* `half_le_re_riemannZeta_of_three_le_re` — hence `re ζ ≥ 1/2` on that half-plane.
* `exists_cos_eq_zero_of_pi_le`, `abs_sub_lt_pi_of_forall_cos_ne_zero` — a continuous real
  function on an interval whose cosine never vanishes moves by less than `π`: otherwise the
  intermediate value theorem puts a point of `π/2 + πℤ` in its interval of values.
* `exists_continuousOn_arg_vertical` (new, in `ArgumentSegment.lean`, the vertical counterpart
  of `exists_continuousOn_arg_horizontal`) — a continuous branch `θ` of the argument along a
  vertical side, with `θ d − θ c = im (VIntegral (f′/f) σ c d)`.
* `abs_im_VIntegral_logDeriv_riemannZeta_lt_pi` — combining the three: the argument of `ζ` moves
  by **less than `π`** along *any* vertical segment of the line `re s = 3`.  Since
  `ζ = ‖ζ‖ exp(i θ)` and `re ζ ≥ 1/2 > 0`, the cosine of the continuous branch never vanishes.
* `abs_log_norm_riemannZeta_le_log_two_of_three_le_re`,
  `abs_integral_log_norm_riemannZeta_three_le` — on `re s = 3` one has `1/2 ≤ ‖ζ‖ ≤ 2`, so the
  right-hand log-modulus term is at most `log 2` per unit of height.

### The left side: the first moment of `log⁺ ‖ζ‖`

* `continuous_posLog` — `log⁺ = max 0 ∘ log` is continuous (it vanishes on `[−1, 1]`, where
  `log` is discontinuous).
* `posLog_le_half_sq` — `log⁺ x ≤ x²/2`, from `log x ≤ x − 1`.
* `continuousOn_riemannZeta_line` — `t ↦ ζ(σ + i t)` is continuous on `[1, ∞)` for every `σ`.
* `integral_posLog_norm_riemannZeta_le` — hence, from the uniform mean square
  `integral_normSq_riemannZeta_le_uniform_Icc` of `M1-STRIP-MEAN-SQUARE`, for every `σ₀ > 1/2`
  there is a `C` with `∫_a^b log⁺ ‖ζ(σ + i t)‖ dt ≤ C · b` for all `σ ≥ σ₀` and `1 ≤ a ≤ b`.

### The resulting inequality

* `zeta_littlewood_bound` — for `σ < 1` and `1 ≤ T₁ ≤ T₂`, on the rectangle `[σ, 3] × [T₁, T₂]`
  with no zero of `ζ` on its border,

  `2π ∑_ρ m_ρ (re ρ − σ) ≤ ∫_{T₁}^{T₂} log⁺ ‖ζ(σ + i t)‖ dt + log 2 · (T₂ − T₁)
    + (bottom argument term) − (top argument term) + (3 − σ) π`.

  The zero-freeness on the border makes both log-moduli continuous on the two vertical sides,
  so the identity's single integral splits; `log ≤ log⁺` handles the left side, the `log 2`
  bound the right one, and the `π` bound the vertical argument term.
* `exists_zeta_littlewood_bound` — the uniform form: for `σ₀ > 1/2` a single constant `C` gives
  `2π ∑_ρ m_ρ (re ρ − σ) ≤ C · T₂ + (bottom argument term) − (top argument term)` for every
  `σ ∈ [σ₀, 1)` and every such rectangle above height `1`.

## What this does *not* give

No zero-density theorem.  The sum on the left is `∫_σ^3 N(α; T₁, T₂) dα` by
`integral_rectZeroCount_eq_finsum`, so a bound of the form `O(T₂)` for the right-hand side would
give `N(σ; T₁, T₂) = O(T₂)` — but the two horizontal argument terms are not bounded here, and
bounding them by `O(log T₂)` is precisely the classical estimate `S(t) = O(log t)`, which needs
the partial-fraction expansion of `ζ′/ζ` (Hadamard/Borel–Carathéodory) and is not formalized in
this repository.  Note also that the `O(T)` density bound itself is already available
unconditionally by a different route (`M2-BOHR-LANDAU`, via Jensen's counting inequality on
discs); the value of this row is that it makes the Littlewood route quantitative up to the one
missing ingredient.

## Adversarial revalidation: M1-LITTLEWOOD-BOUNDS

* **Is the main inequality vacuous?**  No.  Its hypotheses are `σ < 1`, `1 ≤ T₁ ≤ T₂` and
  zero-freeness of `ζ` on the border of `[σ, 3] × [T₁, T₂]`; the right side of that border lies
  on `re s = 3`, where `‖ζ‖ ≥ 1/2`, and the remaining three sides carry no zero for all but
  countably many choices of `σ`, `T₁`, `T₂`.  The conclusion is an inequality between real
  numbers, all of them finite.
* **Is the constant hidden inside an unbounded term?**  The two horizontal terms are written out
  in full in the statement, as `∫_σ^3 im (HIntegral (ζ′/ζ) u 3 T)` for `T = T₁, T₂`; they are
  not absorbed into `C`, and the docstring says so.
* **Does the vertical argument bound use a branch cut?**  No.  The branch is produced by
  `exists_continuousOn_arg_vertical`, which integrates `ζ′/ζ`; the bound comes from the
  connectedness of the interval and the non-vanishing of `cos θ`, not from a choice of `arg`.
* **Is `Real.log 0 = 0` exploited?**  No: on both vertical sides `ζ` is nonvanishing (on the
  left by hypothesis, on the right because `‖ζ‖ ≥ 1/2`), so `log ‖ζ‖` is the genuine logarithm
  of a positive continuous function there.  `log⁺` is used only as an upper bound for `log`.
* **Axioms.**  `propext`, `Classical.choice`, `Quot.sound` only; checked in `scripts/audit.sh`.
* **Pinned.**  Every claim above is pinned in full in `scripts/revalidation.lean`.
