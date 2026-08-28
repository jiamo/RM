# M1-STRIP-MEAN-SQUARE-ASYMPTOTIC — the Bohr–Landau asymptotic mean square for every `1/2 < σ < 1`

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquareAsymptoticHalf.lean`
Related: `docs/goal/evidence/2026-08-24-m1-strip-mean-square-asymptotic.md` (the asymptotic for
`σ > 3/5`), `docs/goal/evidence/2026-08-24-m1-strip-mean-square-bohr-landau.md` (the upper bound
for every `σ > 1/2`, and the Euler–Maclaurin expansion of arbitrary order)

## Claim

For a fixed `σ` with `1/2 < σ < 1` there are constants `C, c > 0` with

    |∫₀ᵀ ‖ζ(σ + i t)‖² dt − (∑_{n ≥ 1} n^(-2σ)) · T| ≤ C · T^(1−c)   for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_asymptotic_half`; equivalently, in limit
form,

    (1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt → ζ(2σ)      as T → ∞,

`RiemannHypothesis.tendsto_integral_normSq_riemannZeta_div_half`, whose limit is written as the
real series `∑ (n+1)^(-2σ)`; that series is identified with `ζ(2σ)` by
`RiemannHypothesis.ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta`.

This is the theorem of Bohr and Landau in its full range: the earlier row proved the same
statement only for `σ > 3/5`.

## Proof

The two halves already in the repository are combined.

* From the asymptotic for `σ > 3/5`: the **two-sided** mean value theorem for Dirichlet
  polynomials `abs_integral_normSq_dirichletPoly_sub_diag_le`, the comparison
  `abs_integral_normSq_riemannZeta_sub_dirichletPoly_le`, the mean square
  `integral_normSq_dirichletPoly_one_le` and the off-diagonal estimate `offDiagSum_one_le`.
* From the upper bound for `σ > 1/2`: the Euler–Maclaurin expansion of arbitrary order `m`,
  `exists_norm_riemannZeta_sub_dirichletPoly_le_em`, whose error is
  `O_m((σ + |t| + m)^m N^(1−σ−m))` once `σ + |t| ≤ N`.

Two new pieces are proved here.

* `integral_normSq_error_em_le`: squaring the order `m` bound pointwise and integrating gives

      ∫₀ᵀ ‖ζ − ∑_{n ≤ N} n^(-s)‖² ≤ 3 (N+1)^(2−2σ) (π/2)/(1−σ)²
                                    + 3 C² N^(−2σ) T
                                    + 3 C² (σ+T+m)^(2m) N^(2−2σ−2m) T,

  the pole term being integrated by `integral_inv_sq_shift_le`.
* The balance. The Dirichlet polynomial is taken of length `N = ⌈T^e⌉ + 1` with

      m/(σ + m − 1) < e < 1/(2 − 2σ),

  an interval which is non-empty exactly when `m (2σ − 1) > 1 − σ`, hence for some `m` as soon
  as `σ > 1/2`; and every such `e` exceeds `1`, so `N ≥ σ + T` and the order `m` expansion
  applies on the whole range of `t`. `emOrder σ = ⌈(1−σ)/(2σ−1)⌉ + 1` is such an `m`,
  `meanSquareExponentHalf σ` is the midpoint of the interval, `emOrder_spec`,
  `meanSquareExponentHalf_gt`, `meanSquareExponentHalf_lt`, `one_lt_meanSquareExponentHalf`
  place them, and `exists_emOrder_meanSquareExponent` packages the two so that the main proof
  never unfolds either definition.

  The four power savings are then

      g₁ = 1 − e(2 − 2σ),  g₂ = 2σe,  g₃ = e(2m + 2σ − 2) − 2m,  g₄ = e(2σ − 1),

  all positive — `g₁` by `e < 1/(2−2σ)` and `g₃` by `e > m/(σ+m−1)` — and `c` is half of their
  minimum: the off-diagonal term, the mean square of the error, and the tail of the Dirichlet
  series are `O(T^(1−2c))`, `O(T^(1−2c))` and `O(T^(1−2c))` respectively.

The limit form follows from the power saving: `|I(T)/T − S| = |I(T) − S·T|/T ≤ C T^(−c) → 0`.

## Scope — what is *not* claimed

* Nothing is claimed on the critical line `σ = 1/2`: the Hardy–Littlewood asymptotic
  `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ∼ T log T` needs the approximate functional equation, which is not
  formalized here. The constants produced here blow up as `σ` decreases to `1/2`, as they must.
* No second order term, and no explicit value of the saving `c`.
* Higher moments are not addressed, and no consequence for the zeroes is drawn.

## Adversarial revalidation: M1-STRIP-MEAN-SQUARE-ASYMPTOTIC

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `integral_normSq_error_em_le`, `exists_emOrder_meanSquareExponent`,
  `exists_integral_normSq_riemannZeta_asymptotic_half` and
  `tendsto_integral_normSq_riemannZeta_div_half`; the checks are in `scripts/audit.sh`.
* The four claims are pinned in `scripts/revalidation.lean`, as are the `σ > 3/5` statements
  they supersede, which are left unchanged.
* The statement is not vacuous: the main term `(∑ n^(-2σ)) T` is positive and of order `T`,
  while the error is `O(T^(1−c))` with `c > 0` produced explicitly by the proof, so the
  statement is strictly stronger than the upper bound `exists_integral_normSq_riemannZeta_le_half`
  of the same range.
* The statement is unconditional: it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
