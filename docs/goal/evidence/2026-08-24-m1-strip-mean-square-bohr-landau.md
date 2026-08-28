# M1-STRIP-MEAN-SQUARE — the Bohr–Landau mean square: `∫₀ᵀ |ζ(σ+it)|² = O(T)` for every `σ > 1/2`

Date: 2026-08-24
File: `RiemannHypothesis/StripMeanSquareBohrLandau.lean`
Predecessors: `docs/goal/evidence/2026-08-24-m1-strip-mean-square.md` (`σ > 2/3`),
`docs/goal/evidence/2026-08-24-m1-strip-mean-square-trapezoid.md` (`σ > 3/5`),
`docs/goal/evidence/2026-08-24-m1-strip-mean-square-bernoulli.md` (`σ > 4/7`)

## Claim

For every fixed `σ` with `1/2 < σ < 1` there is a constant `C > 0` such that

    ∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T      for every T ≥ 1,

`RiemannHypothesis.exists_integral_normSq_riemannZeta_le_half`, together with the first moment
`exists_integral_norm_riemannZeta_le_half` and the large values estimate
`exists_volume_norm_riemannZeta_ge_le_half` in the same range.

This closes the family `2/3 → 3/5 → 4/7 → ⋯ → 1/2`: the open boundary of the earlier rows was
exactly that only `k → ∞` Bernoulli corrections reach `1/2`, and the general order expansion is
now formalized.

## Proof

The new content is the Euler–Maclaurin expansion of *arbitrary* order `m`, obtained by
iterating one integration by parts rather than by writing out a fixed number of Bernoulli
corrections by hand.

* `bq m u = bernoulliFun m u / m !` — the scaled Bernoulli polynomials, with
  `hasDerivAt_bq : (bq (m+1))' = bq m`, `bq_zero_eq`, `bq_one_eq`, `bq_endpoints`
  (`bq m 1 = bq m 0` for `m ≠ 1`), `continuous_bq` and `exists_bq_bound`.
* `poch m s = ∏_{i<m} (s+i)` with `norm_poch_le : ‖poch m s‖ ≤ (‖s‖+m)^m`, and
  `dfun m s x = (-1)^m · poch m s · x^(-s-m)`, the `m`-th derivative of `x ↦ x^(-s)`
  (`hasDerivAt_dfun`, `norm_dfun`).
* `emTerm m a s = ∫_a^{a+1} bq m (x-a) · dfun m s x dx` is the Euler–Maclaurin remainder of
  order `m` on one unit interval. `emTerm_add_emTerm_succ` is the integration by parts step:
  it expresses `emTerm m a s + emTerm (m+1) a s` as the explicit boundary term
  `bq (m+1) 0 · (dfun m s (a+1) − dfun m s a)`, using `bq_endpoints` and `hasDerivAt_bq`.
  `emTerm_zero_eq` and `emTerm_one_eq_trapTerm` identify the orders `0` and `1` with the
  integral itself and with the trapezoidal error of `StripMeanSquareTrapezoid`.
* `emTail m N s = ∑'_n emTerm m (n+N+1) s`, with `summable_emTerm_shift` and
  `norm_emTail_le : ‖emTail m N s‖ ≤ C_m ‖poch m s‖ N^(1-σ-m)/(σ+m-1)`. Summing the
  integration by parts step telescopes to the recursion
  `emTail_succ : emTail m N s = -(bq (m+1) 0) · dfun m s (N+1) − emTail (m+1) N s`.
* `norm_dfun_shift_le` bounds the explicit term of the recursion by `(1+m)^m N^(-σ)` uniformly
  in `t`, provided `‖s‖ ≤ N`; `exists_norm_emTail_one_le` then iterates the recursion by
  `Nat.le_induction` from order `1` to order `m`, and
  `exists_norm_riemannZeta_sub_dirichletPoly_le_em` combines this with
  `riemannZeta_eq_trapApprox` to give, for `0 < σ < 1` and `1 ≤ m`, a constant `C > 0` with

      ‖ζ(s) − ∑_{n ≤ N} n^(-s)‖
        ≤ (N+1)^(1-σ)/‖s−1‖ + C (N^(-σ) + (σ+|t|+m)^m N^(1-σ-m))

  whenever `1 ≤ N` and `σ + |t| ≤ N`. An *arbitrary* power of `N` is gained in the last term.
* `normSq_riemannZeta_le_pointwise_em` squares this (three terms, hence the factor `3`, with
  `(A+B)² ≤ 2(A²+B²)` for the two error terms), and
  `integral_normSq_riemannZeta_le_aux_em` integrates it over `t ∈ [0,T]`, the pole term being
  handled by `integral_inv_sq_shift_le` as in the earlier modules.
* The balance, in `exists_integral_normSq_riemannZeta_le_half`. Given `1/2 < σ < 1` put

      m := ⌈(1−σ)/(2σ−1)⌉₊ + 1,   e := m/(σ+m−1),   N := ⌈T^e⌉₊ + ⌈T⌉₊ + 1.

  Then `m ≥ 1`, `e ≥ 1`, `T^e ≤ N ≤ 5T^e`, `σ + T ≤ N`, and two exponent facts hold:
  `a := e(2−2σ) < 1` (this is exactly the choice of `m`, i.e. `σ > (m+1)/(2m+1)`), and
  `e(2σ+2m−2) = 2m` identically. Consequently
  - the off-diagonal term of `integral_normSq_dirichletPoly_one_le` contributes
    `N^(2−2σ)(1+log N) = O(T^a (1 + log T)) = O(T)` by `exists_rpow_mul_one_add_log_le`;
  - the pole term contributes `(N+1)^(2−2σ) = O(T^a) = O(T)`;
  - the error term contributes `(σ+T+m)^{2m} N^{2−2σ−2m} T ≤ (2+m)^{2m} T^{2m} · T^{−2m} · T`,
    i.e. `O(T)`, the cancellation `T^{2m} · T^{−2m} = 1` being the identity
    `e(2σ+2m−2) = 2m`;
  - the remaining error term is `N^{−2σ} T ≤ T`.

The two consequences are re-derived from the mean square exactly as in the earlier modules, by
`x ≤ (1+x²)/2` and by Chebyshev's inequality.

## Scope — what is *not* claimed

* An upper bound of the correct order of magnitude, not an asymptotic. The asymptotic
  `∫₀ᵀ |ζ|² ∼ ζ(2σ) T` is proved only in the narrower range `σ > 3/5`
  (`M1-STRIP-MEAN-SQUARE-ASYMPTOTIC`); extending it to every `σ > 1/2` would need the
  off-diagonal estimate with a power saving, which is not done here.
* Nothing is claimed on the line `σ = 1/2` itself, where the mean square is `∼ T log T`; the
  constant `C` produced here blows up as `σ ↓ 1/2` (through `1/(1−σ)²`, through `m → ∞` and
  through `(2+m)^{2m}`), as it must.
* Nothing about the zeroes is deduced. `M1-ALMOST-ALL-STRIP` (a density theorem) is untouched:
  it needs the mean square of `ζ` against a mollifier, not of `ζ` alone.
* The Riemann hypothesis is not approached by this. The mean square bound is a classical
  unconditional estimate.

## Adversarial revalidation: M1-STRIP-MEAN-SQUARE

* `lake build` of the whole repository succeeds with the module imported by
  `RiemannHypothesis.lean`; the module contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for `emTail_succ`,
  `exists_norm_riemannZeta_sub_dirichletPoly_le_em`,
  `exists_integral_normSq_riemannZeta_le_half`, `exists_integral_norm_riemannZeta_le_half` and
  `exists_volume_norm_riemannZeta_ge_le_half`; the checks are in `scripts/audit.sh`.
* All five claims are pinned in `scripts/revalidation.lean`, written out in full with the
  repository's declarations as the proof terms.
* The statement is not vacuous and is a strict improvement: `(1/2, 1) ⊋ (4/7, 1) ⊋ (3/5, 1) ⊋
  (2/3, 1)`, and for `σ ∈ (1/2, 4/7]` no bound of this strength existed in the repository
  before. The earlier statements are kept unchanged and stay pinned.
* The statement is unconditional: it takes no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
* Non-circularity: the only inputs are `riemannZeta_eq_trapApprox` (the trapezoidal
  Euler–Maclaurin representation), the mean value theorem for Dirichlet polynomials
  `integral_normSq_dirichletPoly_one_le`, and elementary calculus. None of them mentions the
  zeroes of `ζ`.
* Sanity check on the balance: `σ > 1/2` is used only to make `m` finite, i.e. only through
  `(1−σ)/(2σ−1) < ∞`; and the two exponent identities `a < 1` and `e(2σ+2m−2) = 2m` are proved
  as explicit real inequalities/equalities rather than assumed.
