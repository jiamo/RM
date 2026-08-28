# M1-REDHEFFER — Redheffer's determinant and the linear-algebra form of the hypothesis

Date: 2026-08-22
Module: `RiemannHypothesis/Redheffer.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `sum_mertens_div` — `∑_{d = 1}^{m} M(⌊m/d⌋) = 1` for every `m ≥ 1`, where
  `M(N) = ∑_{n ≤ N} μ(n)` is the Mertens function of `RiemannHypothesis.MoebiusCriterion`; it
  comes from the hyperbola reindexing `sum_pairs_inner` and `∑_{d ∣ k} μ(d) = [k = 1]`, both in
  `RiemannHypothesis/MertensSums.lean`.
* `redheffer` — the Redheffer matrix `A n`, an `n × n` matrix of zeroes and ones whose
  `(i, j)` entry (indices standing for `i+1`, `j+1`) is `1` exactly when the column is the
  first one or `i+1 ∣ j+1`.
* `redheffer_eq_divisorMatrix_mul_mertensColumn` — the factorisation `A = B · C`, where `B` is
  the divisibility matrix (unit upper triangular, `det B = 1`, `det_divisorMatrix`) and `C`
  agrees with the identity off its first column, whose entries are `M(⌊n/(i+1)⌋)` (lower
  triangular with diagonal `(M(n), 1, …, 1)`, `det_mertensColumn`).  Verifying the first column
  of the product is exactly `sum_mertens_div` applied to `m = ⌊n/(i+1)⌋`.
* `det_redheffer` — **Redheffer's theorem**: `det (A n) = M(n)` for `n ≥ 1`.
* `RedhefferBoundForm` — the statement `|det (A n)| = O(n^{1/2+ε})` for every `ε > 0`.
* `mertensBound_of_redhefferBound`, `zeta_of_redhefferBound` — the Redheffer bound is the
  Mertens bound `MertensBoundForm`, and hence (through `zeta_of_mertensBound`, M1's Mertens
  criterion) it implies `ZetaForm`, the Riemann hypothesis.

## Scope and claim mode

* Only the implication `RedhefferBoundForm → ZetaForm` is proved, inheriting the scope of
  `RiemannHypothesis.MoebiusCriterion`: the converse (RH implies the square-root bound for
  `M`) needs the explicit formula and is not attempted here.
* Nothing here proves the Riemann hypothesis: `RedhefferBoundForm` is a hypothesis, not a
  theorem, and no term of that type exists in the repository.  What is unconditional is the
  determinant evaluation `det_redheffer` and the identity `sum_mertens_div`.
* No `sorry`; `#print axioms` on each result listed above yields exactly `propext`,
  `Classical.choice`, `Quot.sound` (checked in `scripts/audit.sh`).
* The statements are pinned in `scripts/revalidation.lean` under `M1-REDHEFFER`, including a
  definitional pin of the matrix entries, so the shape of the matrix cannot drift.

## Adversarial revalidation: M1-REDHEFFER

Each exit criterion is pinned in `scripts/revalidation.lean` (section `M1-REDHEFFER`) by an
`example` whose statement is written out in full and whose proof is the repository's
declaration, so a weakening or renaming breaks the audit:

* the entries of `redheffer n` are pinned definitionally (`rfl`);
* `sum_mertens_div hm : ∑ d ∈ Finset.Icc 1 m, mertens (m / d) = 1` for `1 ≤ m`;
* `det_redheffer hn : (redheffer n).det = mertens n` for `1 ≤ n`;
* `zeta_of_redhefferBound : RedhefferBoundForm → ZetaForm`.

Checks run: `lake build`, `lake build RiemannHypothesis.Redheffer`, `./scripts/audit.sh`
(no `sorry` outside `Challenge.lean`, axioms exactly `propext`, `Classical.choice`,
`Quot.sound`, no `Float`), `python3 scripts/goal_state.py validate`.

Counter-check on the claim: `det_redheffer` is an unconditional identity, and the criterion
`zeta_of_redhefferBound` is an implication from an unproved hypothesis; no term of type
`RedhefferBoundForm` or `ZetaForm` is produced anywhere.
