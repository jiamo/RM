# M1-SUBCONVEXITY-UNCONDITIONAL — the exponent 1/6 for zeta, with no hypothesis

File: `RiemannHypothesis/SubconvexityUnconditional.lean`.
Gates: `lake build RiemannHypothesis.SubconvexityUnconditional`, `./scripts/audit.sh`.

## What is proved

Unconditionally, for every real `t ≥ 10⁹`,

```
‖ζ(1/2 + i t)‖ ≤ 200 · t^(1/6) · (log t + 1).
```

(`norm_riemannZeta_criticalLine_le`.)  This is the classical Weyl–Hardy–Littlewood
subconvexity exponent `1/6`.  Until now the repository had it only *conditionally* on the
approximate functional equation (`M1-AFE-SUBCONVEXITY`,
`norm_riemannZeta_criticalLine_le_of_afe`), because the block estimate was proved only for
blocks up to `√t`, the length of the two Dirichlet polynomials the approximate functional
equation produces.

## How the hypothesis is removed

The approximate functional equation is not needed if one is willing to use a *longer*
Dirichlet polynomial and to bound every one of its dyadic blocks.  The Euler–Maclaurin
representation already in the repository
(`RiemannHypothesis.riemannZeta_eq_zetaApprox_of_pos_re`, valid on the punctured right
half-plane) gives, at length `N = ⌈t²⌉`,

```
ζ(1/2+it) = ∑_{n ≤ N} n^(-1/2-it) + (N+1)^(1/2-it)/(s-1) + ∑_{n ≥ N} eulerTerm n s,
```

and both error terms are bounded: the polar term by `2`, because `√(N+1) ≤ 2t`, and the
tail by `8`, because `‖eulerTerm n s‖ ≤ ‖s‖ (n+1)^(-3/2)` and
`∑_{n ≥ N} (n+1)^(-3/2) ≤ 2/√N ≤ 2/t` (`tsum_shift_rpow_neg_three_halves_le`, proved by the
telescoping inequality `(x+1)^(-3/2) ≤ 2/√x − 2/√(x+1)`).  Together:
`‖ζ(1/2+it) − ∑_{n ≤ N} n^(-1/2-it)‖ ≤ 10` (`norm_riemannZeta_sub_zetaSum_le`).

What remains is to bound every dyadic block of a polynomial of length `t²`, and *no single
van der Corput test does that*.  Writing `u = t^(1/6)`, the three tests of the repository
cover the three ranges, each by the same bound `60 √M u` for a block `[M, M+L)` with
`L ≤ M`:

* `M ≤ 30u²` — the trivial bound (inside the dyadic induction);
* `30u² ≤ M ≤ u⁴` — van der Corput's **third derivative test**
  (`norm_sum_e2pi_logPhase_block_le_quartic`).  This is the estimate of
  `M1-AFE-SUBCONVEXITY` with its range extended from `M ≤ u³` to `M ≤ u⁴`; the extension is
  exactly what the length-`t²` polynomial needs, and the only place the old proof used
  `M ≤ u³` was the step `A ≤ 8P²/u⁴ ≤ 8P`, which holds verbatim for `P ≤ u⁴`
  (`block_bound_numeric_quartic`).
* `u⁴ ≤ M ≤ 2u⁶` — van der Corput's **second derivative test**
  (`norm_sum_e2pi_logPhase_block_le_mid`), with `f''(x) = c/x² ∈ [c/4M², c/M²]`,
  `c = u⁶/2π`.  Its conclusion `2(RL+2)(2+5/√r)` expands to
  `4c/M + 20√c + 8 + 40M/√c`, and each of the four terms is at most a fixed multiple of
  `√M u` in this range.
* `2u⁶ ≤ M ≤ 2u¹²` — the **Kusmin–Landau first derivative test**
  (`norm_sum_e2pi_logPhase_block_le_long`).  Here the phase derivative `c/x` is below
  `1/4π`, so its distance to the nearest integer is the derivative itself, at least
  `c/2M`; the general form of the test proved in `RiemannHypothesis/KusminLandauGeneral.lean`
  (`norm_sum_e2pi_le_of_deriv_general`) then gives `(V+2)(1+2/λ) ≤ 3 + 192√M`.

`norm_sum_e2pi_logPhase_block_le_all` is the case distinction, Abel summation against the
weight `n^(-1/2)` gives `norm_sum_block_criticalLine_le_all`, and the dyadic strong
induction gives `norm_zetaSum_le_of_le_pow_twelve`:
`‖∑_{n ≤ N} n^(-1/2-i u⁶)‖ ≤ 60 u (log₂ N + 1)` for `N ≤ 2u¹²`.  With `log₂ N ≤ 1 + 2.887 log t`
this is the main theorem.

## Hypothesis hygiene

There is no hypothesis: every theorem of the file is unconditional, and none of them takes
an unproved `Prop` of this repository as an argument, so
`docs/goal/conditional-theorems.txt` is unchanged.  The four hygiene questions of
`AGENTS.md` do not arise.

## Adversarial revalidation: M1-SUBCONVEXITY-UNCONDITIONAL

* **Is the statement vacuous?**  No: the hypothesis `10⁹ ≤ t` is satisfiable, and the
  conclusion bounds `‖ζ(1/2+it)‖`, a quantity that is not bounded a priori.  The exponent is
  real (`t ^ ((1 : ℝ) / 6)`, `Real.rpow`), not a natural power; the proof depends on
  `u ^ 6 = t`, which pins the semantics.
* **Is it weaker than it looks?**  It is a pointwise bound on the critical line only.  It is
  *not* the Lindelöf hypothesis, it is not uniform in `σ`, and it says nothing about moments:
  a pointwise subconvexity bound does not give a sharp mean value.  The threshold `10⁹` and
  the constant `200` are explicit but crude; because of the factor `log t` and the constant,
  the bound is numerically worse than the convexity bound until `t` is very large.
* **Does it depend on anything unproved?**
  `#print axioms RiemannHypothesis.SubconvexityUnconditional.norm_riemannZeta_criticalLine_le`
  gives exactly `propext, Classical.choice, Quot.sound`; there is no `sorry` in the file, and
  it imports only `AFESubconvexity`, `KusminLandauGeneral` and `Continuation`, all of which
  are themselves `sorry`-free.
* **Is the improvement real, or bookkeeping?**  The earlier theorem
  `norm_riemannZeta_criticalLine_le_of_afe` has `AFECriticalLine C` as an explicit
  hypothesis, and that `Prop` is not proved anywhere in the repository; the new theorem has
  no hypothesis but `10⁹ ≤ t`.  The mathematical content of the difference is the two new
  block estimates — the second derivative test in the middle range and Kusmin–Landau beyond
  `2t` — which are what a Dirichlet polynomial of length `t²` needs and a polynomial of
  length `√t` does not.
* **What is still open?**  The B process (Poisson summation with stationary phase) is still
  not formalized, so the approximate functional equation itself is still only *recorded*,
  and nothing beyond the exponent pair `(1/6, 2/3)` is available: the Bombieri–Iwaniec,
  Huxley and Bourgain exponents remain out of reach, as does the logarithm-free form
  `O(t^(1/6))`.
