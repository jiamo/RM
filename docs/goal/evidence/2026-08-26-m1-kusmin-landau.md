# M1-KUSMIN-LANDAU — the first-derivative test for exponential *sums*

Date: 2026-08-26
File: `RiemannHypothesis/KusminLandau.lean`

## Claim

Write `e(θ) = exp(2πiθ)` (`e2pi`).

* **discrete form** (`norm_sum_e2pi_le`) — if the consecutive differences
  `d i = u(i+1) − u(i)` of a real sequence are monotone (in either direction) and lie in
  `[λ, 1−λ]` for every `i < K`, with `λ > 0`, then

      ‖∑_{j ≤ K} e(u j)‖ ≤ 1 + 2/λ ;

* **differentiable form** (`norm_sum_e2pi_le_of_deriv`) — if `f` has derivative `f'` on
  `[c, c+K]`, `f'` is monotone or antitone there, and `λ ≤ f' ≤ 1 − λ`, then

      ‖∑_{j ≤ K} e(f(c+j))‖ ≤ 1 + 2/λ ;

* **the form actually used** (`norm_sum_e2pi_le_of_deriv_sub_int`) — the same conclusion when
  `f'` lies in `[k + λ, k + 1 − λ]` for an arbitrary integer `k`, i.e. when `f'` stays at
  distance at least `λ` from every integer.

None of the three bounds depends on the number `K` of terms: that is the whole content, exactly
as in `RiemannHypothesis.VanDerCorput` for integrals.

## Proof

Summation by parts against the amplitude `g i = 1/(e(d i) − 1)`.  Because
`e(u(i+1)) − e(u i) = e(u i)(e(d i) − 1)`, every term of the sum is
`e(u i) = g i · (e(u(i+1)) − e(u i))`, and Abel summation
(`Finset.sum_range_by_parts`) turns `∑_{j ≤ K} e(u j)` into

    e(u K) + g(K−1)·(e(u K) − e(u 0)) − ∑_{i < K−1} (g(i+1) − g i)·(e(u(i+1)) − e(u 0)).

Three inputs finish it.

1. `|e(u j)| = 1`, hence every difference `e(u j) − e(u l)` has modulus at most `2`.
2. `|e(θ) − 1| = 2 sin(πθ)` on `(0,1)`, and Jordan's inequality gives `sin(πθ) ≥ 2λ` on
   `[λ, 1−λ]` (`two_mul_le_sin_pi_mul`), so `‖g i‖ ≤ 1/(4λ)`.
3. The amplitude identity `1/(e(θ) − 1) = −1/2 − (i/2)·cot(πθ)` (`inv_e2pi_sub_one`) shows the
   real part of `g` is *constant*, so `‖g(i+1) − g i‖ = ½|cot(π d(i+1)) − cot(π d i)|`.  Since
   `cot(π·)` is antitone on `(0,1)` (`cotpi_antitone`) and `d` is monotone, the absolute values
   come off with a single sign and the sum telescopes to `½|cot(π d 0) − cot(π d(K−1))|`, at most
   `1/(2λ)` because `|cot(πθ)| ≤ 1/sin(πθ) ≤ 1/(2λ)` there.

Adding up: `1 + 2·(1/(4λ)) + 2·(1/(2λ)) = 1 + 3/(2λ) ≤ 1 + 2/λ`.

The differentiable form is the mean value theorem: `f(c+i+1) − f(c+i) = f'(ξ_i)` with
`ξ_i ∈ (c+i, c+i+1)`, so the `ξ_i` increase with `i` and `d i = f'(ξ_i)` inherits both the bounds
and the monotonicity of `f'`.  The integer form subtracts `k(x − c)`, which changes no term of
the sum because `k j` is an integer (`e2pi_sub_int`) and shifts `f'` down into `[λ, 1−λ]`.

## Why this row exists

`RiemannHypothesis.VanDerCorput` bounds exponential *integrals*.  The Dirichlet polynomials that
carry the analytic theory of `ζ` are exponential *sums*: `∑_{n ≤ N} n^{−it} = ∑ e(f(n))` with
`f(x) = −(t/2π) log x`.  Kusmin–Landau is the sum-side counterpart of the first-derivative test
and the first step of van der Corput's method for sums, hence a prerequisite for the approximate
functional equation and for the Weyl bound.

## Scope, and what is *not* claimed

* Only the first-derivative test for sums is proved.  The van der Corput `A` process (Weyl
  differencing) and `B` process (Poisson summation) are not, nor is the third-derivative test;
  those are what the exponent pair `(1/6, 2/3)` and hence `ζ(1/2+it) ≪ t^{1/6+ε}` require.
* No consequence for `ζ` is drawn in the module: no subconvexity bound, no approximate functional
  equation, no density estimate.  The row is infrastructure.
* The constant is `1 + 2/λ`; classical write-ups give `2/λ` or `1/λ + 2`.  No optimization was
  attempted.
* The hypothesis is that `f'` is monotone *and* trapped between two consecutive integers on the
  whole range.  Splitting a general range into such subranges is not done here.

## Adversarial revalidation: M1-KUSMIN-LANDAU

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.KusminLandau`
  succeeds, and the file contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements and for the amplitude identity they rest on.
* The statements are not vacuous.  The hypotheses of the discrete form are satisfiable — take
  `u j = θ j` for any fixed `θ ∈ [λ, 1−λ]`, giving constant differences — and the differentiable
  form is satisfied by any `f` with `f'` monotone in `[λ, 1−λ]`, for example `f(x) = x/3 + x²/N`
  on `[0, N]`.  For `K` large the conclusion `1 + 2/λ` is far below the trivial bound `K + 1`.
* An earlier draft carried a hypothesis `λ ≤ 1/2`; the finished proof does not use it, so it was
  removed rather than left in place — the statement is correspondingly more general (and for
  `λ > 1/2` it is vacuous for `K > 0`, since `[λ, 1−λ]` is then empty).
* The statements are unconditional: no unproved `Prop` of this repository occurs as a hypothesis,
  so `docs/goal/conditional-theorems.txt` gains no new entry from this module.
* The bound is not stronger than the classical one: `1 + 2/λ` against the classical `2/λ`.
