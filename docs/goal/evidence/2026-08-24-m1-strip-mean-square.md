# M1-STRIP-MEAN-SQUARE — the mean square of `ζ` on a vertical line inside the critical strip

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquare.lean`

## Claim

For a fixed `σ` with `2/3 < σ < 1` there is a constant `C > 0` such that

    ∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T      for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_le`.

This is the first mean-square bound of the repository *inside* the critical strip.
`M1-MEAN-SQUARE` covers only the half-plane of absolute convergence `σ > 1`, where the mean
square converges to `ζ(2σ)`; there the Dirichlet series of `ζ` may be integrated term by term,
and inside the strip it may not.

## Proof

The route is the classical one: replace `ζ` by a Dirichlet polynomial and apply the mean value
theorem for Dirichlet polynomials of `RiemannHypothesis.DirichletPolyMeanSquare`.

* `sum_Icc_rpow_neg_le` — `∑_{n ≤ M} n^(-q) ≤ 1 + M^(1-q)/(1-q)` for `0 ≤ q < 1`, by comparison
  with the integral (`AntitoneOn.sum_le_integral_Ico`).
* `sum_rpow_neg_div_abs_sub_le` — the inner off-diagonal estimate: for `1 ≤ m ≤ N`,
  `∑_{n ≤ N, n ≠ m} n^(-σ)/|n − m| ≤ (6 + 2/(1−σ)) · m^(-σ) · (1 + log N)`.
* `offDiagSum_one_le` — summing over `m`, the off-diagonal term of the mean value theorem for
  the truncated zeta sum `∑_{n ≤ N} n^(-s)` is `O_σ(N^(2−2σ) (1 + log N))`.
* `integral_normSq_dirichletPoly_one_le` — with the diagonal term `T ∑_{n ≤ N} n^(-2σ) ≤ ζ(2σ) T`
  this gives `∫₀ᵀ ‖∑_{n ≤ N} n^(-σ-i t)‖² dt = O_σ(T + N^(2−2σ) (1 + log N))`.
* `norm_riemannZeta_sub_dirichletPoly_le` — the Euler–Maclaurin representation of
  `RiemannHypothesis.EulerMaclaurin` bounds the difference between `ζ(σ + i t)` and the
  truncated sum by `(N+1)^(1−σ)/‖s−1‖ + (σ + |t|) N^(-σ)/σ`.
* `integral_inv_sq_shift_le` — `∫₀ᵀ dt/((1−σ)² + t²) ≤ (π/2)/(1−σ)²`, uniformly in `T`, so the
  first error term contributes `O(N^(2−2σ))` and not `O(N^(2−2σ) T)`.
* `integral_normSq_riemannZeta_le_aux` — assembling the pointwise inequality
  `‖ζ‖² ≤ 3(‖P‖² + E₁² + E₂²)` and integrating.
* Finally `N := ⌈T^(1/σ)⌉₊` balances the two error terms, and
  `exists_rpow_mul_one_add_log_le` (`T^a (1 + log T) = O(T)` for `a < 1`) absorbs the logarithm.

Two consequences are recorded in the same file:

* `exists_integral_norm_riemannZeta_le` — the first moment `∫₀ᵀ ‖ζ(σ + i t)‖ dt` is `O_σ(T)`,
  from `x ≤ (1 + x²)/2`.
* `exists_volume_norm_riemannZeta_ge_le` — the large values estimate: the set of `t ∈ (0, T]`
  at which `‖ζ(σ + i t)‖ ≥ V` has Lebesgue measure at most `C_σ T / V²`, by Chebyshev's
  inequality. This is the shape in which a mean square enters the zero-density estimates.

## Scope — what is *not* claimed

* The exponent `2/3` is what the **zeroth order** Euler–Maclaurin expansion gives, and it is the
  exact balance point: the tail of the expansion is `O(‖s‖ N^(-σ))`, whose mean square over
  `[0, T]` is `O(T³ N^(-2σ))`, so `N ≥ T^(1/σ)` is forced, while the off-diagonal term needs
  `N^(2−2σ) = O(T^(1−ε))`; both hold simultaneously exactly when `(2−2σ)/σ < 1`, i.e. `σ > 2/3`.
* The classical theorem of Bohr and Landau covers every `σ > 1/2`; reaching it needs the
  higher-order Euler–Maclaurin expansion (`k` Bernoulli terms give `σ > (k+2)/(2k+3)`), which is
  not formalized in this repository. That is the open boundary of this row.
* No asymptotic is claimed, only an upper bound of the correct order: the Hardy–Littlewood
  asymptotic `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ~ T log T` on the critical line is a different problem,
  needing the approximate functional equation.
* Nothing about the zeroes is deduced here. The zero-density application of the mean square
  (`M1-ALMOST-ALL-STRIP`) is not carried out.

## Adversarial revalidation: M1-STRIP-MEAN-SQUARE

* `lake build RiemannHypothesis.StripMeanSquare` succeeds inside a full `lake build` of the
  repository; the module contains no `sorry`.
* `#print axioms RiemannHypothesis.exists_integral_normSq_riemannZeta_le` reports exactly
  `[propext, Classical.choice, Quot.sound]`, and likewise for `offDiagSum_one_le`,
  `norm_riemannZeta_sub_dirichletPoly_le`, `integral_normSq_dirichletPoly_one_le`,
  `exists_integral_norm_riemannZeta_le` and `exists_volume_norm_riemannZeta_ge_le`; the six
  checks are in `scripts/audit.sh`.
* The claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statement is not vacuous: the hypotheses `2/3 < σ < 1` describe a non-empty open interval
  and the conclusion is asserted for *every* `T ≥ 1`. The bound is a genuine restriction and not
  an artefact of a large constant: the integrand is continuous
  (`continuous_normSq_riemannZeta_line_of_lt_one`) and the growth bound of `M1-STRIP-GROWTH`
  gives, by itself, only `∫₀ᵀ ‖ζ(σ + i t)‖² dt = O(T^(3−2σ) log² T)`, which for `σ < 1` is a
  strictly larger power of `T` than the `O(T)` proved here.
* The statement is unconditional; it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
