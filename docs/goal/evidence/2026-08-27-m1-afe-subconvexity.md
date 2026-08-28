# M1-AFE-SUBCONVEXITY — the exponent `1/6` for the Dirichlet polynomial, and for `ζ` conditionally on the AFE

Date: 2026-08-27
File: `RiemannHypothesis/AFESubconvexity.lean`

## Claim

Throughout, the height is written `t = u⁶` with `u ≥ 1`, so that every inequality to be checked is
polynomial in `u`.

**Unconditional:**

* `norm_sum_weighted_le` — Abel summation.  If `‖∑_{j < l} z j‖ ≤ B` for every `l ≤ L` and the
  weights `w` are nonnegative and nonincreasing, then `‖∑_{j < L} w j · z j‖ ≤ w 0 · B`.
* `block_bound_numeric` — the arithmetic core, a statement about real numbers only: from the
  conclusion of the third-derivative test together with `R P³ · 3 ≤ u⁶`, `A u⁴ ≤ 8 P²`,
  `P ≤ H u² ≤ 2P`, `L ≤ P`, `30 u² ≤ P` one gets `X ≤ 60 √P u`.
* `norm_sum_e2pi_logPhase_block_le` — for `30 u² ≤ M ≤ u³` and `L ≤ M`,

      ‖∑_{j < L} e(−(u⁶/2π) log (M + j))‖ ≤ 60 √M u.

* `cpow_criticalLine_eq` — the splitting `x^(−1/2−it) = x^(−1/2) · e(−(t/2π) log x)` for `x > 0`.
* `norm_sum_block_criticalLine_le` — for `30 u² ≤ M ≤ u³` and `L ≤ M`,

      ‖∑_{j < L} (M + j)^(−1/2 − i u⁶)‖ ≤ 60 u.

* `norm_zetaSum_le_of_le_cube` — for `N ≤ u³`,

      ‖∑_{1 ≤ n ≤ N} n^(−1/2 − i u⁶)‖ ≤ 60 u (log₂ N + 1).

**Conditional, on `AFECriticalLine C`:**

* `norm_riemannZeta_criticalLine_le_of_afe` — for `t ≥ 10⁹`,

      ‖ζ(1/2 + i t)‖ ≤ C + 120 t^(1/6) (log t + 1).

## Proof

*The block.*  Fix `M` with `30 u² ≤ M ≤ u³` and put `c = u⁶/(2π)`, so that the phase is
`f(x) = −c log x` and `f'''(x) = −2c/x³`.  On `[M, 2M]` we have `|f'''| ∈ [c/(4M³), 2c/M³] =: [r, R]`.
The third-derivative test of `RiemannHypothesis.VanDerCorputThird` is applied with
`H = ⌈M/u²⌉₊`, which satisfies `M ≤ H u² ≤ 2M` because `M ≥ 30 u² ≥ u²`; the hypothesis `H r ≤ 1`
of the test is then `3 R M³ ≤ u⁶`, which holds since `R = 2c/M³ = u⁶/(π M³)` and `π > 3`.  The
resulting inequality is fed to `block_bound_numeric`, whose only job is to check that

    H X² ≤ (P + H)(P + 8 R P H² + 16 H + 20 R P H √H/√r + 80 √H/√r) ≤ 2343 P²

with the above substitutions, whence `X² ≤ 2343 P u² ≤ 3600 P u²` and `X ≤ 60 √P u`.  The
intermediate constants are `8 R L H² ≤ 11 u²`, `16 H ≤ 32 P`, `20 R L H A ≤ 107 P`, `80 A ≤ 640 P`,
so the inner bracket is at most `781 P`.  A conjugation (`VanDerCorputSums.e2pi_neg`) handles the
sign of `f'''`, and a trivial-bound branch covers `L < H`.

*From the phase to the Dirichlet polynomial.*  `cpow_criticalLine_eq` writes each term as the
nonnegative decreasing weight `(M+j)^(−1/2)` times the pure phase, and Abel summation
(`norm_sum_weighted_le`) transfers the block bound at the cost of `w 0 = M^(−1/2)`:
`60 √M u · M^(−1/2) = 60 u`.

*Dyadic decomposition.*  `norm_zetaSum_le_of_le_cube` is a strong induction on `N`: for
`N < 60 u²` the trivial bound `2√N ≤ 60 u` already suffices; otherwise `K = ⌈N/2⌉` satisfies
`30 u² ≤ K`, the tail `(K, N]` is one admissible block, the head is handled by the induction
hypothesis, and `Nat.log 2 N = Nat.log 2 K + 1`.  This gives `log₂ N + 1` blocks in total.

*The conditional bound.*  With `u = t^(1/6)`, the length `afeLength t = ⌊√(t/2π)⌋` is at most
`u³ = √t`, so both Dirichlet polynomials of the approximate functional equation are bounded by
`60 t^(1/6)(log₂ √t + 1) ≤ 60 t^(1/6)(log t + 1)` — the dual sum is the conjugate of the direct one
(`zetaSumDual_criticalLine`) and `‖χ(1/2+it)‖ = 1` (`norm_zetaChi_criticalLine`), so it carries the
same bound.  Adding the AFE error `C t^(−1/4) ≤ C` gives the claim.

## The hypothesis

`AFECriticalLine C` is a `def ... : Prop`, recorded and not proved; the four hygiene questions of
`AGENTS.md` are answered in the module docstring of
`RiemannHypothesis/ApproximateFunctionalEquation.lean` and summarized in the evidence file
`docs/goal/evidence/2026-08-27-m1-zeta-chi-afe.md`.  In one sentence: the approximate functional
equation is an unconditional classical theorem of Hardy and Littlewood (1921) whose known proofs
need the Riemann–Siegel contour integral, or truncated Poisson summation followed by stationary
phase (van der Corput's B process), and neither is available in mathlib or in this repository.
It is in no way derived from the Riemann hypothesis.

## Scope, and what is *not* claimed

* **The AFE is not proved.**  The `t^(1/6)` bound for `ζ` is therefore conditional; only the
  bound for the Dirichlet polynomial `∑_{n ≤ N} n^(−1/2−it)`, `N ≤ t^(1/2)`, is unconditional.
* The `log` factor is not removed: the classical statement is `ζ(1/2+it) ≪ t^(1/6) log t`, which
  is what is proved here, not `t^(1/6+ε)` with the `ε` optimized away or `t^(1/6)` outright.
* The constants (`60`, `120`) are not optimized, and the height restriction `t ≥ 10⁹` is an
  artefact of the numerical inequalities, not of the method.
* Nothing about moments follows.  The sharp second moment `∫_0^T |ζ(1/2+it)|² dt ∼ T log T` and
  Ingham's fourth moment `∼ T (log T)⁴/(2π²)` need, beyond the AFE, the Montgomery–Vaughan mean
  value theorem for Dirichlet polynomials (or an equivalent Hilbert-inequality input), which is
  not in the repository.  A pointwise subconvexity bound does not give a sharp mean value.
* No density estimate follows.  The Ingham → Huxley → Guth–Maynard line needs zero-detecting
  polynomials and large-value estimates, none of which is formalized here.
* The exponent `1/6` is the Hardy–Littlewood/Weyl exponent.  Nothing towards `32/205` (Huxley),
  `13/84` (Bourgain) or Lindelöf is claimed.

## Adversarial revalidation: M1-AFE-SUBCONVEXITY

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.AFESubconvexity` succeeds, and the file contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all seven public
  declarations; the lines are in `scripts/audit.sh`.
* The one conditional theorem is listed in `docs/goal/conditional-theorems.txt` as
  `RiemannHypothesis.AFESubconvexity.norm_riemannZeta_criticalLine_le_of_afe <-
  RiemannHypothesis.AFECriticalLine`, and it is the only new entry from this module.
* The unconditional statements are not vacuous.  The hypothesis window `30 u² ≤ M ≤ u³` is
  nonempty exactly for `u ≥ 30`, in particular for all `u` large; the dyadic theorem is
  applied at `N = afeLength t` and `u = t^(1/6)`, where `N ≤ √t = u³` holds, so the range of
  applicability is exactly the one used.
* The bounds are not uniformly better than the trivial ones, and that is stated rather than
  hidden.  At the full length `N = √t = u³` the trivial bound is `2√N = 2 u^(3/2)`, while the
  theorem gives `60 u (log₂ N + 1) ≈ 60 u (3 log₂ u + 1)`; the latter is the smaller only once
  `√u > 90 log₂ u + 30`, i.e. `u ≳ 10⁷`, i.e. `t ≳ 10⁴²`.  The exponent `1/6` is genuinely below
  the exponent `1/4` of the trivial bound, so the saving is real and grows without bound, but the
  constants proved here are large enough that it becomes numerically visible only very high up.
  Below that height the statements are true and weaker than the triangle inequality, and no
  numerical claim of a saving is made.  The threshold `t ≥ 10⁹` in the conditional theorem is
  what the numerical inequalities of the proof require, not the point at which the bound becomes
  informative.
* `block_bound_numeric` was extracted precisely so that the real-arithmetic content of the block
  bound is separated from the analytic content and can be read — and checked — independently of
  the exponential-sum machinery.
