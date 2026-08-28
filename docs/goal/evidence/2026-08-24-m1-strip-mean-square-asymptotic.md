# M1-STRIP-MEAN-SQUARE-ASYMPTOTIC — the asymptotic mean square of `ζ` for `3/5 < σ < 1`

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquareAsymptotic.lean`
Related: `docs/goal/evidence/2026-08-24-m1-strip-mean-square-trapezoid.md` (the upper bound),
`docs/goal/evidence/2026-08-24-m1-strip-mean-square-bernoulli.md` (the upper bound for `σ > 4/7`)

## Claim

For a fixed `σ` with `3/5 < σ < 1` there are constants `C, c > 0` with

    |∫₀ᵀ ‖ζ(σ + i t)‖² dt − (∑_{n ≥ 1} n^(-2σ)) · T| ≤ C · T^(1−c)   for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_asymptotic`; equivalently, in limit form,

    (1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt → ζ(2σ)      as T → ∞,

`RiemannHypothesis.tendsto_integral_normSq_riemannZeta_div`, whose limit is written as the real
series `∑ (n+1)^(-2σ)`; that series is identified with `ζ(2σ)` by
`RiemannHypothesis.ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta`.

## Proof

Two ingredients are added to those of the upper bound.

* `abs_integral_normSq_dirichletPoly_sub_diag_le` — a **two-sided** mean value theorem for
  Dirichlet polynomials: the mean square of `∑_{n ≤ N} a_n n^(-s)` differs from the diagonal
  term `T ∑_{n ≤ N} ‖a_n‖² n^(-2σ)` by at most `offDiagSum a N σ`. The existing
  `integral_normSq_dirichletPoly_le_diag_add_offDiag` is only an upper bound, because it
  estimates `re z ≤ ‖z‖`; here `|re z| ≤ ‖z‖` is used instead.
* The length of the Dirichlet polynomial is taken slightly *longer* than the one optimizing the
  upper bound: `N ≍ T^e` with `2/(1+σ) < e < 1/(2−2σ)`, an interval which is non-empty exactly
  when `σ > 3/5`. The midpoint is `meanSquareExponent σ`, and `meanSquareExponent_gt`,
  `meanSquareExponent_lt` place it in the interval. Every error term is then a fixed power of
  `T` below `T`: the four savings `g₁, …, g₄` in the proof, of which `c` is a positive minimum.

The limit form follows from the power saving: `|I(T)/T − S| = |I(T) − S·T|/T ≤ C T^(-c) → 0`.

The identification of the constant uses Mathlib's Dirichlet series for `ζ` in the half-plane of
absolute convergence, applied at the real point `2σ > 1`.

## Scope — what is *not* claimed

* The range is `3/5 < σ < 1`, the range of the *trapezoidal* upper bound; the improvement of the
  upper bound to `σ > 4/7` (`M1-STRIP-MEAN-SQUARE`) is not transferred to the asymptotic here,
  because the comparison step is written against the trapezoidal error estimate.
* Nothing is claimed on the critical line `σ = 1/2`: the Hardy–Littlewood asymptotic
  `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ∼ T log T` needs the approximate functional equation, which is not
  formalized here.
* No secondary term, and no consequence for the zeroes.

## Adversarial revalidation: M1-STRIP-MEAN-SQUARE-ASYMPTOTIC

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `abs_integral_normSq_dirichletPoly_sub_diag_le`,
  `exists_integral_normSq_riemannZeta_asymptotic` and
  `tendsto_integral_normSq_riemannZeta_div`; the checks are in `scripts/audit.sh`.
* The claims, and the identification of the constant with `ζ(2σ)`, are pinned in
  `scripts/revalidation.lean`.
* The statement is not vacuous: the main term `(∑ n^(-2σ)) T` is positive and of order `T`,
  while the error is `O(T^(1−c))` with `c > 0` produced explicitly by the proof, so the
  statement is strictly stronger than the upper bound of the same range.
* The statement is unconditional: it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
