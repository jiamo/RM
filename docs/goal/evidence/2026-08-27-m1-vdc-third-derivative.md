# M1-VDC-THIRD-DERIVATIVE — van der Corput's third-derivative test

Date: 2026-08-27
File: `RiemannHypothesis/VanDerCorputThird.lean`

## Claim

Write `e(θ) = exp(2πiθ)` (`e2pi`).  The single public result is

* `norm_sq_sum_e2pi_le_of_deriv_three` — if `f`, `f'`, `f''` are differentiable on `[a, a+N]`
  with derivatives `f'`, `f''`, `f'''`, if `0 < r ≤ f''' ≤ R` there, and if `1 ≤ H ≤ N` with
  `H r ≤ 1`, then

      H ‖∑_{n < N} e(f(a+n))‖²
        ≤ (N + H) (N + 8 R N H² + 16 H + 20 R N H √H/√r + 80 √H/√r).

  Choosing `H ≍ r^(−1/3) N^(−1/3)` for `R ≍ r` this is the classical
  `‖∑ e(f n)‖ ≪ N r^(1/6) + √N r^(−1/6)`, the exponent pair `(1/6, 2/3)`.

Three auxiliary results are proved on the way and are also public:

* `sum_Ioo_int_eq_sum_Ico` — reindexing `∑_{k ∈ Ioo 0 H} g k` over `ℤ` as `∑_{k ∈ Ico 1 H}` over `ℕ`;
* `sub_le_of_deriv_bounds` — the mean value theorem in the two-sided form used throughout: a
  function whose derivative lies in `[r, R]` on an interval has increments in `[r·Δ, R·Δ]`;
* `norm_sum_e2pi_diff_le` — the second-derivative test applied to the *differenced* phase
  `f(· + k) − f(·)`, whose second derivative is `k f'''` up to the mean value theorem, giving
  `‖∑_{n < L} e(f(n+k) − f(n))‖ ≤ 2 (R L k + 2)(2 + 5/√(r k))`;
* `sum_diff_bound_le` — the elementary summation `∑_{1 ≤ k < H} (A + 20/√(r k)) ≤ A H + 40 √H/√r`
  over the shifts, using `∑_{k < H} 1/√k ≤ 2√H` (`RiemannHypothesis.SqrtHarmonic`).

## Proof

The A process of `RiemannHypothesis.WeylDifferencing` (`norm_sq_sum_e2pi_le`) bounds

    H ‖∑_{n < N} e(f(a+n))‖² ≤ (N + H) (N + 2 ∑_{0 < k < H} ‖∑_{n < N−k} e(f(a+n+k) − f(a+n))‖).

Each differenced sum has phase `f(· + k) − f(·)`.  By `sub_le_of_deriv_bounds` its second
derivative — the increment of `f''` over a step of length `k` — lies between `r k` and `R k`, so
the second-derivative test of `RiemannHypothesis.VanDerCorputSums`
(`norm_sum_e2pi_le_of_deriv_two`) applies with the pair `(r k, R k)`; the hypothesis `r k ≤ 1`
that it needs is exactly `H r ≤ 1`.  Summing the resulting
`2 (R N k + 2)(2 + 5/√(r k)) ≤ 8 R N k + 16 + 20 R N √k/√r + 40/√(r k)` over `0 < k < H` with
`∑_{k < H} k ≤ H²/2`, `√k ≤ √H` and `∑_{1 ≤ k < H} 1/√k ≤ 2√H` gives the stated bound.

## Why this row exists

The open boundary of `M1-VDC-SECOND-DERIVATIVE` and of `M1-WEYL-DIFFERENCING` named the same
missing step: the two processes were proved separately and never composed.  Composing them is the
whole content of the third-derivative test, and it is the first estimate in this repository whose
exponent (`1/6`) is better than the convexity exponent (`1/4`) for the phase of `ζ`.

## Scope, and what is *not* claimed

* The number of shifts `H` is left free.  No choice of `H` is made here, so no clean
  `N r^(1/6) + √N r^(−1/6)` is stated; the choice is made, for the phase of `ζ` on a dyadic
  block, in `RiemannHypothesis.AFESubconvexity` (row `M1-AFE-SUBCONVEXITY`).
* Nothing about `ζ` is claimed in this module: it is an estimate for exponential sums with a real
  phase, with no arithmetic input.
* The constants (`8`, `16`, `20`, `80`) are not optimized, and the process is not iterated, so no
  exponent pair beyond `(1/6, 2/3)` is obtained; in particular the Bombieri–Iwaniec / Huxley
  exponent `32/205` and the Bourgain exponent `13/84` are far out of reach.
* No B process (Poisson summation with stationary phase) is proved, so the approximate functional
  equation still cannot be derived — see `M1-ZETA-CHI-AFE`.

## Adversarial revalidation: M1-VDC-THIRD-DERIVATIVE

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.VanDerCorputThird` succeeds, and the file contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_sq_sum_e2pi_le_of_deriv_three`; the line is in `scripts/audit.sh`.
* The statement is not vacuous: `f(x) = r x³/6` satisfies the hypotheses on any interval with
  `f''' ≡ r = R`, and every hypothesis is used — `H r ≤ 1` is what lets the second-derivative
  test be applied to the differenced phase, `H ≤ N` is what makes the differenced ranges
  nonempty, `r > 0` is what makes `1/√r` finite.
* The bound is not uniformly better than the trivial one, and is not claimed to be.  The trivial
  bound gives `H N²` on the left; the right-hand side is larger than that unless `R N H²` and
  `R N H √H/√r` are both `≪ N²/H`, which is the classical regime of the test.  Outside it the
  statement is true but weaker than the triangle inequality.
* The statement is unconditional: no unproved `Prop` of this repository occurs as a hypothesis, so
  `docs/goal/conditional-theorems.txt` gains no entry from this module.
