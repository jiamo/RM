# M1-STRIP-MEAN-SQUARE — the second Bernoulli correction: the mean square of `ζ` for `σ > 4/7`

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquareBernoulli.lean`
Predecessors: `docs/goal/evidence/2026-08-24-m1-strip-mean-square.md` (`σ > 2/3`),
`docs/goal/evidence/2026-08-24-m1-strip-mean-square-trapezoid.md` (`σ > 3/5`)

## Claim

For a fixed `σ` with `4/7 < σ < 1` there is a constant `C > 0` such that

    ∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T      for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_le_four_sevenths`, together with the
first moment `exists_integral_norm_riemannZeta_le_four_sevenths` and the large values estimate
`exists_volume_norm_riemannZeta_ge_le_four_sevenths` in the same range.

Since `4/7 < 3/5 < 2/3`, this strictly extends both earlier ranges; the earlier statements are
kept unchanged and stay pinned.

## Proof

The only ingredient that is improved is the Euler–Maclaurin approximation of `ζ`: the
trapezoidal expansion is carried one Bernoulli term further, so that the remainder is governed
by the *third* derivative of `x ↦ x^(-s)`.

* `bern3Green a z = B₃(z − a)/6` with `B₃(u) = u(u − 1/2)(u − 1)`, together with its first two
  derivatives `bern3GreenD`, `bern3GreenDD`; `bernPrimitive = Q f'' − Q' f' + Q'' f` and
  `hasDerivAt_bernPrimitive` verify `H' = Q f''' + f` by differentiation, since `Q''' = 1`.
* `integral_bernIntegrand` — the fundamental theorem of calculus for `H` on `[a, a+1]` gives
  `∫ (Q f''' + f) = (f(a) + f(a+1))/2 + (s/12)((a+1)^(-s-1) − a^(-s-1))`, which is the
  Euler–Maclaurin identity with the `B₂ = 1/6` term made explicit.
* `bernTerm n s := trapTerm n s − (s (n+1)^(-s-1) − s (n+2)^(-s-1))/12` is the trapezoidal error
  with that term removed, and `bernTerm_eq_integral` identifies it with `∫ Q f'''`.
* `norm_bern3Green_le` (`‖Q‖ ≤ 1/48` on the unit interval, from `|u(u−1/2)(u−1)| ≤ 1/8`) and
  `norm_bernTerm_le` give `‖bernTerm n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ (n+1)^(-(3 + re s))/48`, so the tail
  over `n ≥ N` is `O(‖s‖³ N^(-2-σ))`: one power of `N` better than the trapezoidal expansion.
* `summable_bernTerm`, `tsum_bern_correction` (the telescoping of the `B₂` terms, obtained from
  `tsum_cpow_telescope` applied at `s + 1`), `tsum_trapTerm_eq_bernTerm` and
  `riemannZeta_eq_bernApprox` give the representation
  `ζ(s) = ∑_{n ≤ N} n^(-s) + (N+1)^(1-s)/(s−1) + (N+1)^(-s)/2 + s (N+1)^(-s-1)/12
        + ∑_{n ≥ N} bernTerm n s`
  for `0 < re s`, `s ≠ 1`.
* `norm_riemannZeta_sub_dirichletPoly_le_bern` — on the line `s = σ + i t` this reads
  `‖ζ(s) − ∑_{n ≤ N} n^(-s)‖ ≤ (N+1)^(1−σ)/‖s−1‖ + (N+1)^(-σ)/2 + (σ+|t|) N^(-(1+σ))/12
      + (σ+|t|)(1+σ+|t|)(2+σ+|t|) N^(-(2+σ))/(48(2+σ))`.
* `normSq_riemannZeta_le_pointwise_bern`, `integral_normSq_riemannZeta_le_aux_bern` — squaring
  (five terms now, so with the factor `5`) and integrating; the pole term is handled by
  `integral_inv_sq_shift_le` exactly as before.
* The balance: with `N := ⌈T^(3/(2+σ))⌉₊` the new tail contributes `O(T⁶ N^(-(4+2σ))) = O(1)`
  (the exponent identity `3(4+2σ)/(2+σ) = 6` is exact) and the explicit `B₂` term contributes
  `O(T² N^(-(2+2σ))) = O(1)`; these two `O(1)` bounds are isolated in the arithmetic lemmas
  `bern_error_factor_le` and `bern_b2_factor_le`. The off-diagonal term of the mean value
  theorem for Dirichlet polynomials still needs `N^(2−2σ) = O(T^(1−ε))`, which now reads
  `(6 − 6σ)/(2 + σ) < 1`, i.e. `σ > 4/7`; `exists_rpow_mul_one_add_log_le` absorbs the logarithm.

The two consequences are re-derived verbatim in the new range from the mean square, by
`x ≤ (1 + x²)/2` and by Chebyshev's inequality respectively.

## Scope — what is *not* claimed

* `4/7` is the balance point of the *second order* expansion, as `3/5` is that of the first and
  `2/3` that of the zeroth: `k` Bernoulli terms give `σ > (k+2)/(2k+3)`, and only `k → ∞` gives
  the classical theorem of Bohr and Landau, valid for every `σ > 1/2`. The corrections beyond
  `k = 2` are *not* formalized, so the row remains `DONE_WEAK`.
* An upper bound of the correct order, not an asymptotic; the asymptotic in the narrower range
  `σ > 3/5` is `M1-STRIP-MEAN-SQUARE-ASYMPTOTIC`.
* Nothing about the zeroes is deduced; `M1-ALMOST-ALL-STRIP` is untouched.

## Adversarial revalidation: M1-STRIP-MEAN-SQUARE

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_bernTerm_le`, `norm_riemannZeta_sub_dirichletPoly_le_bern`, `riemannZeta_eq_bernApprox`,
  `exists_integral_normSq_riemannZeta_le_four_sevenths`,
  `exists_integral_norm_riemannZeta_le_four_sevenths` and
  `exists_volume_norm_riemannZeta_ge_le_four_sevenths`; the checks are in `scripts/audit.sh`.
* All six claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statement is not vacuous and is a strict improvement: `(4/7, 1) ⊋ (3/5, 1)`, and for
  `σ ∈ (4/7, 3/5]` no bound of this strength existed in the repository before.
* The statement is unconditional: it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
* The sanity check that the constant is of the right shape: the proof never uses `σ > 4/7`
  except through `(6 − 6σ)/(2 + σ) < 1`, and the two `O(1)` lemmas are proved with explicit
  numerical constants (`576/(2304(2+σ)²) ≤ 1` and `4/144 ≤ 1`), so no hidden circularity or
  vacuity can enter through them.
