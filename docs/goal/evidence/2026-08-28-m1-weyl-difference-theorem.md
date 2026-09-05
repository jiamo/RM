# M1-WEYL-DIFFERENCE-THEOREM — van der Corput's difference theorem

Date: 2026-08-28
File: `RiemannHypothesis/WeylDifferenceTheorem.lean`

## Claim

Write `e(θ) = exp(2πiθ)` and, for a real sequence `x : ℕ → ℝ`,

    weylSum x m N = ∑_{n < N} e(m · x n),   diffSeq x k n = x (n + k) − x n .

The module proves

* `mul_normSq_weylSum_le` — the **A process** for a sequence indexed by the naturals: for every
  `H ≥ 1`,

      H ‖∑_{n<N} e(m xₙ)‖² ≤ (N + H − 1)(N + 2 ∑_{k=1}^{H−1} ‖∑_{n<N−k} e(m (x(n+k) − xₙ))‖);

* `weylSumsVanish_of_diff` — if every difference sequence `diffSeq x k`, `k ≥ 1`, has vanishing
  Weyl sums, then so does `x`;

* `equidistributedMod1_of_diff` — **van der Corput's difference theorem**: if every difference
  sequence is equidistributed modulo one, then so is `x`.

## Proof

The inequality is the integer-indexed A process of `M1-WEYL-DIFFERENCING`
(`WeylDifferencing.norm_sq_sum_e2pi_le`) transported along `n ↦ n.toNat`: the phase
`f n = m · x n.toNat` restricts on `[0, N)` to the given sequence, the differenced sum over
`Ico 0 (N − k)` is exactly `weylSum (diffSeq x k) m (N − k)`, and the shift range `Ioo 0 H` in `ℤ`
is reindexed to `Ico 1 H` in `ℕ`.

For the difference theorem, fix a nonzero frequency `m` and an `ε > 0`, and choose a natural
number `H > 4/ε²`.  For each of the `H − 1` shifts the hypothesis provides a threshold beyond
which `‖weylSum (diffSeq x k) m M‖ ≤ M/(4H)`; taking the maximum of the finitely many thresholds
and `N ≥ M + H + 1` gives `‖weylSum (diffSeq x k) m (N − k)‖ ≤ N/(4H)` simultaneously, hence

    ∑_{k=1}^{H−1} ‖·‖ ≤ (H − 1)·N/(4H) ≤ N/4 .

Since `H ≤ N`, the A process then gives `H ‖weylSum x m N‖² ≤ 2N · (3N/2) = 3N² < ε² N² H`, that
is `‖weylSum x m N‖ / N < ε`.  As `m` was an arbitrary nonzero frequency, the Weyl sums of `x`
vanish, and Weyl's criterion (`M1-WEYL-CRITERION`) turns that into equidistribution.

## Why this row exists

The A process was proved in `M1-WEYL-DIFFERENCING` as a bare inequality, with no consequence
drawn.  Its standard qualitative consequence — the difference theorem — is what lowers the degree
of an equidistribution problem, and it is the engine of `M1-WEYL-POLYNOMIAL`.

## Scope, and what is *not* claimed

* No rate of convergence: the hypothesis carries none, and the argument only produces `1/H`
  after the thresholds, so the conclusion is purely qualitative.
* Nothing about `ζ` is claimed: the module is about arbitrary real sequences.  No subconvexity
  bound, no approximate functional equation, no density estimate follows from it.

## Adversarial revalidation: M1-WEYL-DIFFERENCE-THEOREM

* The module is imported by `RiemannHypothesis.lean`,
  `lake build RiemannHypothesis.WeylDifferenceTheorem` succeeds, the file contains no `sorry`,
  and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements; the checks are in `scripts/audit.sh`.
* Both the inequality and the difference theorem are pinned in `scripts/revalidation.lean` with
  `weylSum` and `diffSeq` written out as explicit sums, so the definitions cannot be weakened
  without breaking the audit.
* The statement is not vacuous: the hypothesis is satisfiable — for `x n = α n²` with `α`
  irrational the differences `2αkn + αk²` are linear with irrational slope, hence equidistributed
  by `M1-WEYL-LINEAR` — and it fails for sequences that are not equidistributed, e.g. `x n = n`,
  whose differences are constant and not equidistributed.
* The conclusion is a genuine restriction: `EquidistributedMod1` pins every continuous average at
  its mean, and `not_equidistributedMod1_const_zero` shows the predicate is not universally true.
* No unproved `Prop` of this repository occurs among the hypotheses; `EquidistributedMod1` and
  `WeylSumsVanish` are definitions that this repository proves for concrete sequences.
