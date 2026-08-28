# M1-BACKLUND-ARGUMENT — `S(t) = O(log t)` and the Littlewood route to a density bound

Date: 2026-08-25
Files: `RiemannHypothesis/ArgumentBacklund.lean`, `RiemannHypothesis/ZeroCountRadii.lean`,
`RiemannHypothesis/BacklundZeta.lean`, `RiemannHypothesis/ZetaDensityLittlewood.lean`
Predecessor: `docs/goal/evidence/2026-08-25-m1-littlewood-bounds.md`

## Claim

The two horizontal argument terms that `M1-LITTLEWOOD-BOUNDS` left explicit on the right-hand
side of Littlewood's lemma for `ζ` are bounded, by Backlund's classical argument, and the
resulting inequality yields a zero-density estimate:

* `abs_sub_le_of_ncard_cos_eq_zero` — if the cosine of a continuous function vanishes at no more
  than `n` points of `(a, b]`, the function moves by at most `(n + 1) π`;
* `ncard_setOf_zeros_le_radii` — Jensen's counting inequality with an arbitrary ratio of radii,
  in maximum-modulus form;
* `norm_riemannZeta_le_sq_of_tenth_le_re` — `‖ζ(s)‖ ≤ 80 (im s)²` for `re s ≥ 1/10`,
  `|im s| ≥ 3`;
* `zetaRefl`, `zetaRefl_horizontal` — the reflected function `z ↦ (ζ(z) + ζ(z − 2iT))/2`, which
  is analytic near `3 + iT` and computes `re ζ` on the line `im s = T`;
* `exists_ncard_re_riemannZeta_eq_zero_le` — **Backlund's count**: `x ↦ re ζ(x + iT)` has
  `O(log T)` zeroes on `[1/2, 3]`;
* `exists_abs_im_HIntegral_logDeriv_riemannZeta_le` — **`S(t) = O(log t)`** in the form needed
  here: `|im (HIntegral (ζ′/ζ) u 3 T)| ≤ C log T`, uniformly in `u ∈ [1/2, 3]`, whenever `ζ`
  does not vanish on the segment;
* `exists_zeta_littlewood_bound_total` — Littlewood's lemma for `ζ` with **every** term bounded:
  `2π ∑_ρ m_ρ (re ρ − σ) ≤ C T₂`;
* `exists_rectZeroCount_riemannZeta_le` — the density consequence: for `1/2 < σ₀ < σ < 1` the
  number of zeroes of `ζ`, with multiplicity, in `[σ, 3] × [T₁, T₂]` is at most `C T₂`.

## Proof

* Let `θ` be a continuous branch of the argument of `ζ` along the horizontal segment from
  `u + iT` to `3 + iT` (`exists_continuousOn_arg_horizontal`, available because `ζ` is analytic
  and non-vanishing there).  Since `ζ = ‖ζ‖ e^{iθ}`, `cos θ` vanishes exactly where `re ζ` does,
  so `abs_sub_le_of_ncard_cos_eq_zero` bounds the total variation of `θ` — which is
  `im (HIntegral (ζ′/ζ) u 3 T)` — by `(n + 1) π` with `n` the number of zeroes of `re ζ` on the
  segment.
* Those zeroes are counted by Jensen's inequality applied to the reflected function
  `zetaRefl T z = (ζ(z) + ζ(z − 2iT))/2`.  It is analytic on the closed ball of radius `14/5`
  about `3 + iT` (that ball stays in `re s ≥ 1/5` and away from the pole `s = 1`), it equals
  `re ζ` on the line `im s = T` because `ζ(s̄) = conj ζ(s)`, its value at the centre is
  `re ζ(3 + iT) ≥ 1/2`, and it is `O(T²)` on the sphere by the crude convexity bound
  `norm_riemannZeta_le_sq_of_tenth_le_re`.  Jensen with radii `14/5 > 5/2` then gives
  `n = O(log T)`.
* Substituting the two `O(log T)` bounds into `exists_zeta_littlewood_bound` (which already
  bounds every other term by `C T₂`) gives `exists_zeta_littlewood_bound_total`; note
  `log T₂ ≤ T₂` for `T₂ ≥ 6`, so the argument terms are absorbed into the linear bound.
* Finally, the layer-cake identity `integral_rectZeroCount_eq_finsum` turns the weighted sum
  `∑_ρ m_ρ (re ρ − σ₀)` into an integral of the counting function; every zero in
  `[σ, 3] × [T₁, T₂]` contributes at least `σ − σ₀ > 0`, so the count is at most
  `C T₂ / (2π (σ − σ₀))`.

## Scope — what is *not* claimed

* The density bound is `N(σ; T₁, T₂) = O(T₂)` with the constant depending on `σ₀`; it is the
  Bohr–Landau strength, **not** Carlson's `O(T^{4σ(1−σ)} log T)`, and it does not by itself give
  the `o(T)` that `M1-ALMOST-ALL-STRIP` asks for.  It is an independent second route to the
  bound already obtained in `M2-BOHR-LANDAU`.
* Both statements keep the hypothesis that `ζ` does not vanish on the border of the rectangle,
  which is what makes Littlewood's lemma applicable.
* `S(t) = O(log t)` is proved only in the integral form above, along segments ending at the
  abscissa `3` and with `ζ` non-vanishing on the segment; no statement about a global branch of
  `arg ζ`, and no `Ω`-result, is claimed.
* Nothing here bears on the Riemann hypothesis.

## Verification

* `lake build` — the whole project, clean; both modules are imported by `RiemannHypothesis.lean`.
* `bash scripts/audit.sh` — exit 0; all the statements above are pinned in full in
  `scripts/revalidation.lean` (section `M1-BACKLUND-ARGUMENT`) and their axioms are checked.
* No `sorry` in either module.

## Adversarial revalidation: M1-BACKLUND-ARGUMENT

* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `exists_abs_im_HIntegral_logDeriv_riemannZeta_le`, `exists_zeta_littlewood_bound_total` and
  `exists_rectZeroCount_riemannZeta_le`.
* The statements are not vacuous.  The hypothesis "`ζ` does not vanish on the border" excludes
  only countably many choices of the three parameters `σ₀, T₁, T₂`, since the zeroes of `ζ` are
  isolated; and the conclusion of `exists_rectZeroCount_riemannZeta_le` is a bound on a
  non-negative integer count by `C T₂`, which is a genuine restriction because the count is
  known to be positive for suitable rectangles.
* The constants are quantified in the right order: `C` is chosen before `σ`, `T₁`, `T₂` in
  `exists_zeta_littlewood_bound_total`, so the bound is uniform, not a pointwise triviality.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the modules add no row to `docs/goal/conditional-theorems.txt`.
* No claim of a zero-density exponent better than `O(T)` is made anywhere in the two modules,
  and no `ZetaForm` term is produced.
