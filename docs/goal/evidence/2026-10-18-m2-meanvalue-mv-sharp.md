# The Montgomery–Vaughan mean value theorem, `(T + O(N)) ∑ |a_n|²`

Date: 2026-10-18
Task: `M2-MEANVALUE-MV-SHARP` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/MontgomeryVaughanMeanValue.lean` (new; imports `MontgomeryVaughan`
and `DirichletPolyMeanSquare`)

## Claim

```lean
theorem integral_normSq_expSum_eq (lam : Fin n → ℝ) (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (a : Fin n → ℂ) (T : ℝ) :
    (((∫ t in (0:ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2 : ℝ)) : ℂ)
      = T * ∑ r, ((‖a r‖ ^ 2 : ℝ) : ℂ)
        + -I * (hilbertForm lam (fun r => a r * cexp ((T : ℂ) * (lam r : ℂ) * I))
          - hilbertForm lam a)

theorem abs_integral_normSq_expSum_sub_le (lam : Fin n → ℝ) (a : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2)
        - T * ∑ r, ‖a r‖ ^ 2|
      ≤ 2 * Real.pi / δ * ∑ r, ‖a r‖ ^ 2

theorem abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
        - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
      ≤ 2 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
```

`hilbertForm lam x` is `∑ r, ∑ s ∈ univ.erase r, x r * conj (x s) / (lam r - lam s)`, the left
side of `GeneralizedHilbertInequality`. `dirichletPoly a N s = ∑_{1≤n≤N} a n · n^(−s)` is the
existing definition in `DirichletPolyMeanSquare.lean`.

The last theorem says `∫₀ᵀ |∑_{n≤N} a_n n^{-it}|² dt = (T + O(N)) ∑ |a_n|²`, with the
explicit constant `2πN`. That is better than the `4πN` asked for. It improves the
`8 N (1 + log N)` of `integral_normSq_dirichletPoly_mvt_zero` (`DirichletPolyMeanValue.lean`,
unchanged). Mode: a proof in this repository. All three theorems have axioms exactly
`[propext, Classical.choice, Quot.sound]`.

## Proof

* `integral_pair`: `∫₀ᵀ e^{idt} dt` is `T` for `d = 0` and `−i(e^{idT} − 1)/d` otherwise
  (Mathlib's `integral_exp_mul_complex`).
* `integral_normSq_expSum_eq`: expand `|∑ a_r e^{iλ_r t}|²` as
  `∑_{r,s} a_r conj(a_s) e^{i(λ_r−λ_s)t}` and integrate term by term. The diagonal gives
  `T ∑ |a_r|²`. The off-diagonal term `(r,s)` gives
  `−i (a_r conj(a_s) e^{i(λ_r−λ_s)T} − a_r conj(a_s))/(λ_r − λ_s)`. Since
  `a_r conj(a_s) e^{i(λ_r−λ_s)T} = x_r conj(x_s)` for `x_r = a_r e^{iλ_r T}`, the off-diagonal
  part is `−i (H(x) − H(a))`.
* `abs_integral_normSq_expSum_sub_le`: `|x_r| = |a_r|`, and the generalized Hilbert inequality
  bounds each of `|H(x)|`, `|H(a)|` by `(π/δ) ∑ |a_r|²`.
* `log_separated`: for `1 ≤ m < n ≤ N`,
  `log n − log m = log(n/m) ≥ 1 − m/n = (n−m)/n ≥ 1/n ≥ 1/N`, using Mathlib's
  `Real.one_sub_inv_le_log_of_pos`. So `λ_n = −log n` is `1/N`-separated.
* `abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul`: `n^{−it} = e^{it(−log n)}`
  (`Complex.cpow_def_of_ne_zero`, `Complex.natCast_log`), reindexed from `Finset.Icc 1 N` to
  `Fin N` (`sum_Icc_eq_sum_fin`). Then `2π/(1/N) = 2πN`. The case `N = 0` is trivial.

## Adversarial revalidation: M2-MEANVALUE-MV-SHARP

* *Constants, by hand.* The error is `|H(x)| + |H(a)| ≤ 2 · (π/δ) ∑|a|²`. With `δ = 1/N`
  this is `2πN`. The separation bound at the tightest pair `(m, n) = (N−1, N)` is
  `log(N/(N−1)) ≥ 1/N`, which is true: for `N = 2`, `log 2 = 0.693… ≥ 0.5`.
* *Vacuity.* `abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul` has no hypotheses at all: it
  holds for every `a`, `N` and real `T` (for `T < 0` the interval integral is oriented, and the
  bound still holds). `abs_integral_normSq_expSum_sub_le` assumes exactly the hypotheses of the
  Hilbert inequality, which are satisfiable.
* *Load-bearing.* Separation enters only through `generalizedHilbertInequality` and through
  `hinj`, which `integral_normSq_expSum_eq` needs to divide by `λ_r − λ_s`. Without separation
  the main term `T ∑ |a_r|²` is wrong: `λ_1 = λ_2` with `a = (1, 1)` gives `4T`, not `2T`.
* *Shape.* The error term is outside the sum (`O(N) ∑ |a_n|²`). The weighted shape
  `∑ |a_n|² (T + O(n))` is **not** claimed.
* *Statement pinning.* All three statements are pinned in `scripts/revalidation.lean`, the
  first with `hilbertForm` unfolded. Their axioms are pinned in `scripts/audit.sh`.

## Not proved

* The weighted form `∫₀ᵀ |∑ a_n n^{-it}|² dt = ∑ |a_n|² (T + O(n))` (Montgomery–Vaughan,
  Theorem 2). It needs the weighted Hilbert inequality.
* Anything about `ζ`: these are statements about Dirichlet polynomials. No density estimate is
  rerun here.

## Build measurements (R0)

Measured in this round's sandbox: 8 cores, 64 GB of RAM, Lean 4.33.0, prebuilt Mathlib.

* **Build time.** `lake build` ran from a state in which only about 50 of this repository's
  modules were built. It finished in 8,406 s (2 h 20 min) wall time: 12,509 jobs, 3,757
  modules compiled, `Build completed successfully`. Large parts of `Family003` form a chain of
  dependent modules, and for long stretches a single `lean` process was running. Wall time is
  therefore dominated by the critical path, not by the core count.
* **Slowest modules** (seconds, from the build log):
  `Family003…Detector.HighRowsFirstTerms` 966, `…HighRowsSelectedTerms` 889,
  `…HighRowsCentralTerms` 882, `Family003…SiegelZeros.LocalAlgebra.LocalQuotientEquiv` 323,
  `Zeta23.ThmE.PrimeSideChi` 291, `Zeta23.GammaFacts.IntMu` 125, `Zeta23.ThmE.IntMuChi` 122,
  `RiemannHypothesis.SubconvexityUnconditional` 115. Every other module took under 2 minutes.
* **Peak memory of the heaviest module.** A solo run of
  `lake env lean RiemannHypothesis/Family003/NumberTheory/DirichletL/Detector/HighRowsFirstTerms.lean`,
  sampled every 2 s, peaked at **27.3 GB resident (VmRSS) and 22.3 GB anonymous memory**. The
  resident figure includes the memory-mapped Mathlib `.olean` files. During the full build the
  two sibling modules showed the same peaks (22.3 GB anonymous each). The next largest module,
  `…GaussSum.ActiveReindexing`, peaked at 3.6 GB anonymous. Almost every other module stayed
  below 1 GB anonymous, though every process maps all its imported `.olean` files, which
  inflates its VmRSS. Peak used memory of the whole machine during the build: 27.0 GB.
  **Conclusion: 7 GB is not enough.** The three `HighRows…Terms` modules cannot be compiled on
  a standard 2-core, 7 GB GitHub-hosted runner. `ci.yml` therefore takes its runner from the
  repository variable `CI_RUNNER` (default `ubuntu-latest`); set it to a runner with at least
  32 GB. The audit's `scripts/conditional_theorems.lean` step also reached about 11 GB
  resident.
* **Parallelism.** This Lake (5.0) has no `-j` flag. The environment variable `LEAN_NUM_THREADS`
  limits it. Checked here by rebuilding four independent leaf modules (`Redheffer`,
  `Alternating`, `LiouvilleSums`, `ChebyshevCriterion`): with `LEAN_NUM_THREADS=1` at most one
  `lean` compile ran at a time; by default four ran at once.
* **Resumability.** The same four modules were rebuilt under
  `LEAN_NUM_THREADS=1 timeout --signal=INT --kill-after=1m 14s lake build …`. The command
  exited with 124 after two modules had finished. A second `lake build` compiled only the other
  two. This is the behaviour the workflow's save-on-timeout step relies on.
* **Cache size.** `.lake/build` takes 9.1 GB and `vendor/zeta23/.lake/build` 0.97 GB; together,
  compressed with `tar | zstd -3`, they take 1.05 GB.
* **Workflow file.** `pyyaml` is not installed in this sandbox and could not be installed
  (no network). `.github/workflows/ci.yml` was instead parsed with Perl's
  `CPAN::Meta::YAML`, which loaded it with top-level keys
  `concurrency, jobs, name, on, permissions` and the eight steps in order. GitHub Actions
  itself was not run.

## Commands and gates (both rows of this round)

The gates were first run on 2026-10-18 against an older checkout (12,509, then 12,510 jobs;
`OK: 176 tasks validate`). The round was then rebased onto the requester's repository at commit
`5960dab`, and the gates were run again there, from an empty `.lake/build` (Mathlib prebuilt).
The results below are from that second run. Outputs are quoted from the logs.

* `lake build RiemannHypothesis.HilbertInequality RiemannHypothesis.MontgomeryVaughanMeanValue`
  → `Build completed successfully (8750 jobs).` This needed the four repairs to
  `HilbertInequality.lean` listed in `2026-10-18-m2-generalized-hilbert.md`, § "Other rows".
* `lake build` (full) → every module of `RiemannHypothesis`, `Solution` and `vendor/zeta23`
  built (12,510 jobs, 6,049 s wall time, 8 cores, peak machine memory 25.6 GB). One target
  failed: `Challenge`, with `Challenge.lean:62:2: Unknown constant
  RiemannHypothesis.zeta_strip_iff_eta` (and the same at lines 67 and 71). The requester's
  `Challenge.lean` refers to the theorems of `RiemannHypothesis.Main` but imports only
  `RiemannHypothesis.Defs`. That file is outside this round and was left as it is, so the final
  line of `lake build` on the committed tree is `error: build failed`.
* `./scripts/audit.sh` on the committed tree stops at its first step, the same build failure
  (exit 1).
* `./scripts/audit.sh` with one temporary line, `import RiemannHypothesis.Main`, added to
  `Challenge.lean` (reverted afterwards; not committed) → exit 0, final line `OK`, in 858 s. It
  reported `Build completed successfully (12510 jobs).`,
  `AXIOM AUDIT: 32079 theorems checked, 0 outside the standard three`, no `sorry` outside
  `Challenge.lean`, `scripts/revalidation.lean` elaborating with the new pins, an empty
  conditional-theorem diff, and `OK: 178 tasks validate`.
  `docs/goal/conditional-theorems.txt` is byte for byte the requester's.
* `#print axioms`, from step 3 of that audit run:
  ```
  'RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'RiemannHypothesis.MontgomeryVaughan.integral_normSq_expSum_eq' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'RiemannHypothesis.MontgomeryVaughan.abs_integral_normSq_expSum_sub_le' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'RiemannHypothesis.MontgomeryVaughan.abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  ```
* `python3 scripts/goal_state.py validate` → `OK: 178 tasks validate`.
* `rg "sorry|native_decide|^axiom|implemented_by"` on the two new modules → no match.

`scripts/audit.sh` has git mode `100755`, so `./scripts/audit.sh` runs directly, as the CI step
needs.
