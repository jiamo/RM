# The large sieve with the constant `N + δ⁻¹`

Date: 2026-10-18
Task: `M2-LARGE-SIEVE-MV` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/LargeSieveMV.lean` (new; imports `HilbertCosecant` and
`LargeSieveDual`)

## Claim

```lean
theorem large_sieve_mv {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹) * ∑ n ∈ range N, ‖a n‖ ^ 2

theorem large_sieve_mv_dual {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹) * ∑ i ∈ s, ‖x i‖ ^ 2

theorem admissibleConstant_large_sieve_mv : AdmissibleConstant (fun δ N => (N : ℝ) + δ⁻¹)
```

The hypotheses of `large_sieve_mv` are those of `large_sieve_gallagher`
(`RiemannHypothesis/LargeSieveGallagher.lean`), verbatim, so it is a drop-in replacement; only
the constant changes, from `δ⁻¹ + πN` to `N + δ⁻¹`. Mode: a **proof**, in this repository, of the
Montgomery–Vaughan large sieve (Mathematika 20 (1973), 119–134; Iwaniec–Kowalski, Theorem 7.7,
which states the slightly sharper `N − 1 + δ⁻¹`). All three theorems have axioms exactly
`[propext, Classical.choice, Quot.sound]`.

## Proof

* `two_I_mul_sin`, `kernel_mul_two_I_sin`: `2i sin πβ = e(β/2) − e(−β/2)`, and with the geometric
  sum `(∑_{n<N} e(nβ))(e(β) − 1) = e(Nβ) − 1`,
  `(∑_{n<N} e(nβ)) · 2i sin πβ = e((N − 1/2)β) − e(−β/2)` for every real `β`.
* `large_sieve_mv_dual`: expand `∑_n |∑_i x_i e(n t_i)|² = ∑_{i,j} x_i conj(x_j) K_N(t_i − t_j)`.
  The diagonal is `N ∑ |x_i|²`. For `i ≠ j`, `sin π(t_i − t_j) ≠ 0` (separation), and the previous
  identity turns the off-diagonal part into `(H(v) − H(w))/(2i)`, where
  `H(y) = ∑_{i≠j} y_i conj(y_j)/sin π(t_i − t_j)`, `v_i = x_i e((N − 1/2) t_i)`,
  `w_i = x_i e(−t_i/2)`. Since `|v_i| = |w_i| = |x_i|`, `cosecantHilbertInequality_finset`
  (`M2-HILBERT-CSC`) bounds `|H(v)|` and `|H(w)|` by `δ⁻¹ ∑ |x_i|²`, so the real part of the
  off-diagonal part is at most `(δ⁻¹ + δ⁻¹)/2 · ∑ |x_i|²`. (The triangle inequality suffices; the
  fact that `H(v)` is purely imaginary is not needed.)
* `large_sieve_mv`: the duality principle `sum_normSq_adjoint_le` (`LargeSieveDual.lean`) applied
  to `φ n i = conj e(n t_i)`, with the dual inequality at the points `−t_i` (separated by
  `intDist_neg`).
* `admissibleConstant_large_sieve_mv`: the definition of `AdmissibleConstant`
  (`LargeSieve.lean`), next to `admissibleConstant_large_sieve`.

## Hypothesis hygiene

No new `def … : Prop`, and no theorem with an unproved `Prop` as hypothesis.

## Adversarial revalidation: M2-LARGE-SIEVE-MV

* *Constants, by hand.* `N = 1`, points `0` and `1/2`, `δ = 1/2`, `a_0 = 1`: the left side is
  `|1|² + |1|² = 2`, the right side `(1 + 2) · 1 = 3`. One point, all `a_n = 1`: left side `N²`,
  right side `(N + δ⁻¹) N`. The repository's ceiling `le_of_admissibleConstant` says that every
  admissible constant is at least `max N (2δ)⁻¹`; `N + δ⁻¹` satisfies it, so the theorem is
  consistent with the proved lower bound, and it is within a factor `2` of it.
* *The constant is the pinned one.* `scripts/revalidation.lean` writes
  `((N : ℝ) + δ⁻¹) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2` and supplies `large_sieve_mv`; it also pins
  the dual form and `AdmissibleConstant (fun δ N => (N : ℝ) + δ⁻¹)`. Axioms are pinned in step 3
  of `scripts/audit.sh`.
* *Vacuity.* The hypotheses are those of `large_sieve_gallagher`, satisfiable by the points
  `k δ`, `0 ≤ k < ⌊δ⁻¹⌋`; for `s` a single point the statement reduces to Cauchy–Schwarz.
* *Load-bearing.* Without separation two equal points `t_1 = t_2` and `a_n = 1` give `2N²`, which
  exceeds `(N + δ⁻¹) N` for `N > δ⁻¹`. `δ ≤ 1/2` is inherited from the cosecant inequality and is
  automatic for two or more points.
* *Claim mode.* A proof in this repository; no Mathlib large sieve is used.

## Not proved

* Selberg's constant `N − 1 + δ⁻¹` (Iwaniec–Kowalski, Theorem 7.7). It needs either Selberg's
  majorant (`M2-BEURLING-SELBERG`, not formalized) or a refinement of the argument above that was
  not found in a clean form; it is recorded as open on `M2-LARGE-SIEVE`.
* The large sieve for Dirichlet polynomials at well-spaced real points, and the character form.
* Anything about `ζ`.

## Commands and gates

This section covers both `M2-HILBERT-CSC` (R1) and `M2-LARGE-SIEVE-MV` (R2). R1 was built and
its axioms checked before R2 was started; the repository-wide gates below ran once R2 was
closed, before any R3 work. Sandbox: 8 cores, 64 GB, Lean 4.33.0, prebuilt Mathlib. In this
checkout `scripts/audit.sh` has mode `100644`, so it was run as `bash scripts/audit.sh`.

* `lake build RiemannHypothesis.HilbertCosecant` → `Built RiemannHypothesis.HilbertCosecant`,
  `Build completed successfully (8753 jobs).`
* `lake build RiemannHypothesis.LargeSieveMV` → `Built RiemannHypothesis.LargeSieveMV`,
  `Build completed successfully (8758 jobs).`
* `lake build` (full; a first full build from an empty `.lake/build` took about 1 h 45 min)
  → `Build completed successfully (12512 jobs).` (step 1 of the audit run below).
* A first `bash scripts/audit.sh` failed at step 6 only: the conditional-theorem scan listed the
  helper `HilbertCosecant.sum_inv_sq_le_of_separated`, whose hypothesis was stated through the
  definition `WellSpaced.Separated`. The hypothesis was restated in unfolded form (as
  `MontgomeryVaughan.colSq_le` does), so that `docs/goal/conditional-theorems.txt` stays as it
  is; no manifest entry was added.
* `bash scripts/audit.sh` (second run) → exit 0. Final lines:
  ```
  ==> lake build
  Build completed successfully (12512 jobs).
  ==> checking for sorry outside Challenge.lean
  ==> checking axioms of the compared theorems
  ==> exhaustive axiom audit (scripts/axiom_audit.lean)
  AXIOM AUDIT: 32110 theorems checked, 0 outside the standard three
  OK
  ==> coverage of the pinned axiom checks (scripts/audit_coverage.py)
  ==> checking for Float
  ==> pinning the claims of the closed rows (scripts/revalidation.lean)
  ==> checking the conditional/unconditional boundary
  ==> validating the task board
  OK: 180 tasks validate
  OK
  ```
* `#print axioms`, from step 3 of that run:
  ```
  'RiemannHypothesis.HilbertCosecant.hasSum_inv_sq_int' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.HilbertCosecant.sum_inv_sin_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.HilbertCosecant.cosecantHilbertInequality' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.HilbertCosecant.cosecantHilbertInequality_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.LargeSieveMV.kernel_mul_two_I_sin' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.LargeSieveMV.large_sieve_mv_dual' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.LargeSieveMV.large_sieve_mv' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RiemannHypothesis.LargeSieveMV.admissibleConstant_large_sieve_mv' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
* `python3 scripts/goal_state.py validate` → `OK: 180 tasks validate`.
* `docs/goal/conditional-theorems.txt`: unchanged (empty diff in step 6, and
  `git diff` against the starting commit is empty).
* `rg "sorry|native_decide|^axiom|implemented_by"` on the two new modules → no match.
