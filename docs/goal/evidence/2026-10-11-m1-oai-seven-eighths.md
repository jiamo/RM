# Quasi-Riemann hypothesis, zeta and Dirichlet cases (openai/math family 003)

Date: 2026-10-11
Modules: `RiemannHypothesis/QuasiRiemann.lean`, `RiemannHypothesis/DirichletSevenEighths.lean`,
and the absorbed closure under `RiemannHypothesis/Family003/` (see `docs/family003/README.md`).
Rows: `M1-OAI-ZETA-SEVEN-EIGHTHS` (rank 1), then `M1-OAI-DIRICHLET-SEVEN-EIGHTHS` (rank 2,
depends on rank 1; both `TODO_READY`/`IN_PROGRESS` at the start of the delivery and on one
dependency chain, so completed together under §2.1 of `docs/goal/goal-prompt.md`).

## What is proved

| theorem | statement |
|---|---|
| `RiemannHypothesis.QuasiRiemann.riemannZeta_ne_zero_of_seven_eighths_lt_re` | `∀ {s : ℂ}, (7/8 : ℝ) < s.re → _root_.riemannZeta s ≠ 0` |
| `RiemannHypothesis.QuasiRiemann.nontrivial_zero_re_mem` | `riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → 1/8 ≤ s.re ∧ s.re ≤ 7/8` |
| `RiemannHypothesis.DirichletSevenEighths.LFunction_ne_zero_of_seven_eighths_lt_re` | `∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}, (7/8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → _root_.DirichletCharacter.LFunction χ s ≠ 0` |

The first and third are the upstream theorems `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`
and `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (module
`OAI.NumberTheory.DirichletL.Nonvanishing`, openai/math `fd4aeeb`), with the same statements;
their proofs are the upstream proofs, compiled against this repository's pins (Lean v4.33.0,
Mathlib `db584cd6`) as `RiemannHypothesis.Family003.…`.  The second is new here: the lower
bound is the upper bound reflected through Mathlib's functional equation `riemannZeta_one_sub`
(the factor `cos(π(1-s)/2)` vanishes only at the trivial zeroes, which are excluded; `s = 0` is
excluded by `riemannZeta_zero = -1/2`).

## Host convention at `s = 1`

`riemannZeta` is Mathlib's total function; at the pole it takes the value
`riemannZeta 1 = (γ - log (4π)) / 2 ≠ 0` (`riemannZeta_one`, `riemannZeta_ne_zero_of_one_le_re`).
The upstream statement is about the same constant and has no pole hypothesis; since the
upstream proof compiles unchanged in substance against the host definition, the exact upstream
claim holds on the host convention.  No discrepancy to record.  `completedRiemannZeta` is not
involved.  For the Dirichlet statement the exclusion `¬ (χ = 1 ∧ s = 1)` is the upstream one.

## How the closure was made to compile

The mechanical stage (`scripts/family003/port.py`) wrote 2940 native modules with provenance
headers.  The host-compatibility pass then made the whole import closure of
`RiemannHypothesis.Family003.NumberTheory.DirichletL.Nonvanishing` compile:
`lake build +RiemannHypothesis.Family003.NumberTheory.DirichletL.Nonvanishing` completes
(7019 jobs, no errors).  The kinds of edit, all recorded in the edited files' headers, are listed
in `docs/family003/README.md`; in this delivery's last stage they were: finite-index instances
for `Subgroup.comap` and `Subgroup.map` (new `Compat.FiniteIndexComap`, `Compat.FiniteIndexMap`),
`LinearMap.extendOfIsometry` (new `Compat.ExtendOfIsometry`, built from the host's
`LinearMap.extendOfNorm`), a `Finite (O ⧸ Q)` instance from `[NeZero Q]`
(`Compat.FiniteQuotientNeZero`), the renames `Measurable.of_eval` → `measurable_pi_lambda` and
`multiplicity_pos_of_dvd` (one argument fewer), `_root_.not_imp` for an ambiguous identifier,
two `simpa` repairs, one `simp` lemma added, and `set_option maxHeartbeats 0` on three theorems
whose kernel check exceeds the default limit on the host (proofs unchanged).

## Adversarial revalidation: M1-OAI-ZETA-SEVEN-EIGHTHS

(The same checks were run for the Dirichlet row; see the next section.)

* `lake build +RiemannHypothesis.QuasiRiemann` and `lake build +RiemannHypothesis.DirichletSevenEighths`
  succeed; both modules compile without warnings.  Both are imported from `RiemannHypothesis.lean`,
  so the default `lake build` compiles the absorbed closure.
* `#print axioms` on all three public theorems: `[propext, Classical.choice, Quot.sound]`;
  also checked by the pinned list in `scripts/audit.sh` and by the exhaustive
  `scripts/axiom_audit.lean`, which covers every theorem of the absorbed closure.
* No `sorry`, `axiom`, `native_decide`, `bv_decide` or `implemented_by` under
  `RiemannHypothesis/Family003/` or in the two public modules.  The upstream comparator stubs
  are not imported.
* Faithfulness: the public statements are pinned verbatim in `scripts/revalidation.lean`; they
  mention only Mathlib's `riemannZeta`, `DirichletCharacter`, `DirichletCharacter.LFunction`, and
  no repository-defined notion.  No hypothesis besides `7/8 < re s` (and, for `L`, the pole
  exclusion) appears: no detector certificate or analytic band assumption.
* Non-vacuity: the hypotheses are satisfiable (e.g. `s = 2`), and the conclusion is a
  non-vanishing statement about Mathlib's functions, not about a proxy.
* Hypothesis hygiene (AGENTS.md): no new `Prop` is assumed; nothing is conditional.
* Provenance: every absorbed module carries the openai/math provenance header (third-party
  modules carry their original authorship and the "required by openai/math family 003" line);
  `NOTICE` and `LICENSES/openai-math-LICENSE`, `LICENSES/PrimeNumberTheoremAnd-LICENSE`,
  `LICENSES/rellich-kondrachov-LICENSE` are present.

## Adversarial revalidation: M1-OAI-DIRICHLET-SEVEN-EIGHTHS

* `lake build +RiemannHypothesis.DirichletSevenEighths` succeeds without warnings (after rank 1
  was closed and its gates run); the module re-exports
  `RiemannHypothesis.Family003.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` (pinned list and exhaustive audit).
* The statement is pinned verbatim in `scripts/revalidation.lean`: all moduli `q` with
  `NeZero q`, all characters `χ : DirichletCharacter ℂ q`, hypothesis `7/8 < re s` and the pole
  exclusion `¬ (χ = 1 ∧ s = 1)` only, conclusion about Mathlib's
  `DirichletCharacter.LFunction`.  No detector certificate or analytic band assumption.
* The exclusion is necessary as stated (Mathlib's `LFunction 1` has a pole at `1`, where its
  value is a junk value) and is exactly the upstream one.

## Open boundary

None for these two rows.  The Riemann hypothesis is not touched: `7/8` is a zero-free
half-plane, and nothing here locates any zero on the critical line.  The Hecke row
(`M1-OAI-HECKE-SEVEN-EIGHTHS`) and the Siegel-zero row (`M1-OAI-SIEGEL-ZERO-GAP`) need further
upstream modules (`OAI.NumberTheory.DirichletL.Hecke.Nonvanishing`,
`OAI.NumberTheory.SiegelZeros.Main` and their closures) and are not started.
