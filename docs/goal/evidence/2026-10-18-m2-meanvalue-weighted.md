# The weighted Montgomery–Vaughan mean value theorem, with the constant `10√2`

Date: 2026-10-18
Task: `M2-MEANVALUE-WEIGHTED` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/MontgomeryVaughanWeightedMeanValue.lean` (new; imports
`MontgomeryVaughanWeighted` and `MontgomeryVaughanMeanValue`)

## Claim

```lean
theorem abs_integral_normSq_expSum_sub_le_weighted (lam δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ |lam r - lam s|) (a : Fin n → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2)
        - T * ∑ r, ‖a r‖ ^ 2|
      ≤ 10 * Real.sqrt 2 * ∑ r, ‖a r‖ ^ 2 / δ r

lemma log_local_spacing {N : ℕ} (k l : Fin N) (hkl : k ≠ l) :
    1 / ((k : ℕ) + 2 : ℝ) ≤ |-Real.log ((k : ℕ) + 1 : ℝ) - -Real.log ((l : ℕ) + 1 : ℝ)|

theorem abs_integral_normSq_dirichletPoly_sub_le_weighted (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
        - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
      ≤ 10 * Real.sqrt 2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) + 1) * ‖a n‖ ^ 2
```

(namespace `RiemannHypothesis.MontgomeryVaughanWeighted`; `dirichletPoly a N s = ∑_{n=1}^N a n
n^(−s)` from `DirichletPolyMeanSquare.lean`).

In words: `∫₀ᵀ |∑_{n≤N} a_n n^{−it}|² dt = ∑_{n≤N} |a_n|² (T + O(n))`, precisely with
`|O(n)| ≤ 10√2 (n + 1)`, for all complex coefficients, all `N` and all real `T`. With
Montgomery and Vaughan's `3π/2` the constant would be `3π`; the one proved is
`10√2 ≈ 14.14 ≈ 4.50π`, i.e. twice the constant `5√2` of `weightedHilbertInequality`
(M2-HILBERT-WEIGHTED). Mode: a **proof** in this repository.

## The argument

Exactly as round 1 derived the unweighted theorem (`MontgomeryVaughanMeanValue.lean`, unchanged):

* `MontgomeryVaughan.integral_normSq_expSum_eq` (reused) gives the mean square as
  `T ∑ |a_r|² − i (H(x) − H(a))`, `H` the Hilbert form, `x_r = a_r e^{iλ_r T}`, `|x_r| = |a_r|`;
* `weightedHilbertInequality` bounds `|H(x)|` and `|H(a)|` by `5√2 ∑ |a_r|²/δ_r` each, so the
  difference is at most `10√2 ∑ |a_r|²/δ_r` (`abs_integral_normSq_expSum_sub_le_weighted`).
* `log_local_spacing`: for `n = k+1 ≠ m = l+1`, `|log n − log m| ≥ 1/(n+1)`, from
  `log x ≥ 1 − 1/x` (`one_sub_div_le_log_sub`): if `m > n` then
  `log m − log n ≥ 1 − n/m ≥ 1 − n/(n+1) = 1/(n+1)`; if `m < n` then
  `log n − log m ≥ 1 − m/n ≥ 1/n`.
* `abs_integral_normSq_dirichletPoly_sub_le_weighted`: `n^{−it} = e^{it(−log n)}`, reindexing
  `Icc 1 N` by `Fin N` (`sum_Icc_eq_sum_fin`, reused) and `1/δ_k = k + 2 = n + 1`.

## Hypothesis hygiene

No new `def … : Prop`; no theorem takes an unproved `Prop` as a hypothesis.
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M2-MEANVALUE-WEIGHTED

* *Constants, by hand.* `2 · 5√2 = 10√2 ≈ 14.142`; `3π ≈ 9.425`; ratio `≈ 1.50`. Local spacing at
  `n = 1`: `log 2 ≈ 0.693 ≥ 1/2`; at `n = 2`: `min(log 2 − 0, log 3 − log 2) = log 1.5 ≈ 0.405
  ≥ 1/3`.
* *Non-triviality.* `N = 1`, `a_1 = 1`: the integral is exactly `T`, the left side `0`. `N = 2`,
  `a = (1, 1)`, `T = π/log 2`: the integral is `2T + 2 sin(T log 2)/log 2 = 2T`, so again `0`; for
  general `T` the off-diagonal term `2 sin(T log 2)/log 2` is at most `2/log 2 ≈ 2.885`, against
  the right side `10√2 (2 + 3) ≈ 70.7`. Compared with round 1 (`2πN ∑ |a_n|²`), the new bound is
  better whenever the mass of `a` sits at `n ≪ N`: for `a = e_1` it gives `20√2 ≈ 28.3` against
  `2πN`, independent of `N`.
* *Vacuity.* No hypotheses beyond the data; the exponential-sum form has the spacing hypothesis,
  satisfied by `log_local_spacing`.
* *Load-bearing.* In the exponential-sum form, `λ = (0, ε)`, `δ = (1, 1)`, `a = (1, 1)`:
  `|1 + e^{iεt}|² = 2 + 2 cos εt`, so `∫₀ᵀ = 2T + 2 sin(εT)/ε`; at `T = π/(2ε)` the left side is
  `2/ε`, unbounded against the fixed right side `20√2`, so the spacing hypothesis is needed.
* *Claim mode.* A proof in this repository; the round-1 theorem
  `abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul` is not replaced.
* *Statement pinning.* `scripts/revalidation.lean` writes out the three statements above in full
  and supplies the repository's declarations as proof terms; axioms pinned in step 3 of
  `scripts/audit.sh`.

## Not proved

* The constant `3π` (it would follow from `3π/2` in M2-HILBERT-WEIGHTED).
* The large sieve for Dirichlet polynomials at well-spaced real points. (The weighted cosecant
  inequality and the weighted circle large sieve are proved in M2-LARGE-SIEVE-WEIGHTED.)
* The fourth moment of `ζ` (item (ii) of M2-MEANVALUE). Nothing about `ζ` follows from this row.

## Commands and gates

This section covers `M2-HILBERT-WEIGHTED` (R1), `M2-MEANVALUE-WEIGHTED` (R2) and
`M2-LARGE-SIEVE-WEIGHTED` (R3). At the start `git status` was clean. Sandbox: 8 cores, 64 GB,
Lean 4.33.0, prebuilt Mathlib. In this checkout `scripts/audit.sh` has mode `100644`, so it was
run as `bash scripts/audit.sh`.

* R1: `lake build RiemannHypothesis.MontgomeryVaughanWeighted` →
  `Built RiemannHypothesis.MontgomeryVaughanWeighted`, `Build completed successfully (8751 jobs).`
  `#print axioms` of `weightedHilbertInequality` and `hilbertInequality_of_uniform` →
  `[propext, Classical.choice, Quot.sound]`. R2 was started after this.
* R2: `lake build RiemannHypothesis.MontgomeryVaughanWeightedMeanValue` →
  `Built RiemannHypothesis.MontgomeryVaughanWeightedMeanValue`,
  `Build completed successfully (8753 jobs).` Axioms of the two R2 theorems: the standard three.
* `lake build` (full, from an empty `.lake/build`, R1 and R2 registered, about 3 h)
  → `Build completed successfully (12516 jobs).` R3 was started after this.
* R3: `lake build RiemannHypothesis.LargeSieveWeighted
  RiemannHypothesis.MontgomeryVaughanWeightedMeanValue` (after generalizing
  `LocalSpacingMaximal.lean` to a `Fintype` index) → `Built RiemannHypothesis.LocalSpacingMaximal`,
  `… MontgomeryVaughanWeighted`, `… HilbertCosecantWeighted`,
  `… MontgomeryVaughanWeightedMeanValue`, `… LargeSieveWeighted`,
  `Build completed successfully (8764 jobs).`
* `lake build` (incremental, everything registered) → `Built RiemannHypothesis`,
  `Build completed successfully (12518 jobs).`
* `bash scripts/audit.sh` → exit 0. Final lines:
  ```
  ==> exhaustive axiom audit (scripts/axiom_audit.lean)
  AXIOM AUDIT: 32184 theorems checked, 0 outside the standard three
  OK
  ==> coverage of the pinned axiom checks (scripts/audit_coverage.py)
  exported theorems : 28767
  audited names     : 877
  covered           : 877 (3.0%)
  missing coverage  : 27890
  stale audit lines : 0
  ==> checking for Float
  ==> pinning the claims of the closed rows (scripts/revalidation.lean)
  ==> checking the conditional/unconditional boundary
  ==> validating the task board
  OK: 184 tasks validate
  OK
  ```
  (step 1 of that run: `Build completed successfully (12518 jobs).`)
* `#print axioms`, from step 3 of that run: each of
  `LocalSpacing.sum_sum_mul_div_sq_le`, `LocalSpacing.delta_mul_sum_delta_div_sq_le`,
  `MontgomeryVaughanWeighted.weighted_eigenvalue_sq_le`, `.weightedHilbertInequality`,
  `.hilbertInequality_of_uniform`, `.abs_integral_normSq_expSum_sub_le_weighted`,
  `.log_local_spacing`, `.abs_integral_normSq_dirichletPoly_sub_le_weighted`,
  `HilbertCosecantWeighted.delta_mul_sum_delta_cscSq_le`, `.sum_sum_cscSq_le`,
  `.wcsc_eigenvalue_sq_le`, `.weightedCosecantInequality`, `.weightedCosecantInequality_finset`,
  `LargeSieveWeighted.large_sieve_weighted_dual`, `.large_sieve_weighted` depends on axioms
  `[propext, Classical.choice, Quot.sound]`.
* `python3 scripts/goal_state.py validate` → `OK: 184 tasks validate`.
* `docs/goal/conditional-theorems.txt`: unchanged (empty diff in step 6 of the audit, and
  `git diff` against the starting commit is empty).
* `rg "sorry|native_decide|^axiom|implemented_by"` on the five new modules → no match.
