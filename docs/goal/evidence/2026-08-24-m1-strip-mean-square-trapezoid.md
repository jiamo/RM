# M1-STRIP-MEAN-SQUARE — the trapezoidal refinement: the mean square of `ζ` for `σ > 3/5`

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquareTrapezoid.lean`
Predecessor: `docs/goal/evidence/2026-08-24-m1-strip-mean-square.md` (the same bound for `σ > 2/3`)

## Claim

For a fixed `σ` with `3/5 < σ < 1` there is a constant `C > 0` such that

    ∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T      for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_le_three_fifths`.

This strictly extends the range `2/3 < σ < 1` of
`RiemannHypothesis.exists_integral_normSq_riemannZeta_le`; the earlier statement is kept
unchanged, and the two consequences (first moment, large values) are recorded in the wider
range as well.

## Proof

The only ingredient that is improved is the Euler–Maclaurin approximation of `ζ`. The previous
proof uses the *zeroth order* expansion, whose tail is `O(‖s‖ N^(-σ))`. This file adds the
*first order* (trapezoidal) correction.

* `trapTerm n s` — the error of the trapezoid rule for `x ↦ x^(-s)` on `[n+1, n+2]`, i.e.
  `((n+1)^(-s) + (n+2)^(-s))/2 − ∫_{n+1}^{n+2} x^(-s) dx`.
* `trapGreen a x = ((x − a)² − (x − a))/2` — the Green's function of the trapezoid rule.
  `trapPrimitive` is the primitive `P f' − (x − a − 1/2) f` of `P f'' − f` for `f = x^(-s)`,
  and `hasDerivAt_trapPrimitive` verifies this by differentiation.
* `trapTerm_eq_integral` — consequently
  `trapTerm n s = −∫_{n+1}^{n+2} P(x) · s (s+1) x^(-s-2) dx`. This is the exactness of the
  trapezoid rule on affine functions made quantitative: the error is controlled by the *second*
  derivative of `x ↦ x^(-s)`.
* `norm_trapGreen_le`, `norm_trapTerm_le` — `‖P‖ ≤ 1/8` on the unit interval gives
  `‖trapTerm n s‖ ≤ (1/8) ‖s‖ ‖s+1‖ (n+1)^(-(2 + re s))`, so the tail over `n ≥ N` is
  `O(‖s‖² N^(-1-σ))`: one power of `N` better than before.
* `summable_trapTerm`, `tsum_cpow_telescope`, `tsum_eulerTerm_eq_trapTerm`,
  `riemannZeta_eq_trapApprox` — summing the trapezoid errors and telescoping the integrals gives
  the representation
  `ζ(s) = ∑_{n ≤ N} n^(-s) + (N+1)^(1-s)/(s−1) + (N+1)^(-s)/2 + ∑_{n ≥ N} trapTerm n s`
  for `0 < re s < 1`.
* `norm_riemannZeta_sub_dirichletPoly_le_trap` — on the line `s = σ + i t` this reads
  `‖ζ(s) − ∑_{n ≤ N} n^(-s)‖ ≤ (N+1)^(1−σ)/‖s−1‖ + (N+1)^(-σ)/2
      + (σ+|t|)(1+σ+|t|) N^(-(1+σ))/(8(1+σ))`.
* `normSq_riemannZeta_le_pointwise_trap`, `integral_normSq_riemannZeta_le_aux_trap` — squaring
  (four terms now, so with the factor `4` in place of `3`) and integrating; the pole term is
  handled by `integral_inv_sq_shift_le` exactly as before.
* The balance: the trapezoidal tail contributes `O(T⁴ N^(-(2+2σ)))` to the mean square, which is
  `O(1)` as soon as `N ≥ T^(2/(1+σ))`, while the off-diagonal term of the mean value theorem for
  Dirichlet polynomials still needs `N^(2−2σ) = O(T^(1−ε))`. With `N := ⌈T^(2/(1+σ))⌉₊` the
  second condition reads `(4 − 4σ)/(1 + σ) < 1`, i.e. `σ > 3/5`, and
  `exists_rpow_mul_one_add_log_le` absorbs the logarithm. The `O(1)` bound on the trapezoidal
  contribution is isolated in the arithmetic lemma `trap_error_factor_le`.

The two consequences of the mean square are re-derived verbatim in the new range:

* `exists_integral_norm_riemannZeta_le_three_fifths` — the first moment `∫₀ᵀ ‖ζ(σ + i t)‖ dt`
  is `O_σ(T)`, from `x ≤ (1 + x²)/2`.
* `exists_volume_norm_riemannZeta_ge_le_three_fifths` — the large values estimate: the set of
  `t ∈ (0, T]` with `‖ζ(σ + i t)‖ ≥ V` has Lebesgue measure at most `C_σ T / V²`, by Chebyshev's
  inequality.

## Scope — what is *not* claimed

* `3/5` is the balance point of the *first order* expansion, exactly as `2/3` is that of the
  zeroth order one. The general pattern is `σ > (k+2)/(2k+3)` for `k` Bernoulli terms:
  `k = 0` gives `2/3`, `k = 1` gives `3/5`, and only `k → ∞` gives the classical theorem of Bohr
  and Landau, valid for every `σ > 1/2`. The higher corrections are *not* formalized here, so
  the row remains `DONE_WEAK`.
* No asymptotic is claimed, only an upper bound of the correct order; the Hardy–Littlewood
  asymptotic on the critical line is a different problem, needing the approximate functional
  equation.
* Nothing about the zeroes is deduced. The zero-density application (`M1-ALMOST-ALL-STRIP`) is
  still not carried out.

## Adversarial revalidation

* `lake build RiemannHypothesis.StripMeanSquareTrapezoid` succeeds inside a full `lake build` of
  the repository; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_trapTerm_le`, `norm_riemannZeta_sub_dirichletPoly_le_trap`,
  `exists_integral_normSq_riemannZeta_le_three_fifths`,
  `exists_integral_norm_riemannZeta_le_three_fifths` and
  `exists_volume_norm_riemannZeta_ge_le_three_fifths`; the five checks are in
  `scripts/audit.sh`.
* The five claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statement is not vacuous, and it is a strict improvement: `(3/5, 1)` contains `(2/3, 1)`
  properly, and for `σ ∈ (3/5, 2/3]` no bound of this strength was available in the repository
  before — the growth bound of `M1-STRIP-GROWTH` gives only `O(T^(3−2σ) log² T)`.
* The statement is unconditional; it takes no unproved `Prop` of this repository as a hypothesis,
  and the module adds no row to `docs/goal/conditional-theorems.txt`.
