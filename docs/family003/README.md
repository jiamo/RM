# openai/math family 003 — native absorption

Source: `github.com/openai/math`, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
(checked 2026-10-11), family 003, *The quasi-Riemann hypothesis*.  Licence: Apache 2.0
(`LICENSES/openai-math-LICENSE`, `NOTICE`).  Upstream toolchain Lean v4.34.1 / Mathlib
`d13f23b7`; this repository: Lean v4.33.0 / Mathlib `db584cd6` (unchanged).

The intake bundle (`openai_rh_fd4aeeb_source_bundle.json`, restored with
`restore_openai_rh_bundle.py`) is reference material only; nothing imports it.  The upstream
comparator stubs (`ComparatorChallenges/*.lean`, which contain `sorry` by design) are **not**
imported or copied.

## Layout

| path | content |
|---|---|
| `RiemannHypothesis/Family003/NumberTheory/DirichletL/**` | the upstream `OAI.NumberTheory.DirichletL.*` modules in the import closure of `OAI.NumberTheory.DirichletL.Nonvanishing`, module prefix `OAI` → `RiemannHypothesis.Family003`, namespace `OAI` → `RiemannHypothesis.Family003` |
| `RiemannHypothesis/Family003/External/PrimeNumberTheoremAnd/**`, `…/External/RellichKondrachov/**` | the third-party modules of that closure (PrimeNumberTheoremAnd `c39a7511`, rellich-kondrachov `70f85d4c`, with the upstream openai/math compatibility patches already applied) |
| `RiemannHypothesis/Family003/Compat/**` | host-compatibility layer: lemmas, instances and tactic shims present at the upstream Mathlib/Lean pin but absent at the host pin, each proved here from host material |
| `RiemannHypothesis/QuasiRiemann.lean` | public endpoint of row `M1-OAI-ZETA-SEVEN-EIGHTHS` |
| `RiemannHypothesis/DirichletSevenEighths.lean` | public endpoint of row `M1-OAI-DIRICHLET-SEVEN-EIGHTHS` |
| `RiemannHypothesis/HeckeSevenEighths.lean` | public endpoint of row `M1-OAI-HECKE-SEVEN-EIGHTHS` |
| `RiemannHypothesis/SiegelZeroGap.lean` | public endpoint of row `M1-OAI-SIEGEL-ZERO-GAP` |
| `RiemannHypothesis/Family003/NumberTheory/SiegelZeros/**`, `…/External/PrimeNumberTheoremAnd/SiegelZeros/**` | the import closure of upstream `OAI.NumberTheory.SiegelZeros.Main` (306 upstream modules, 12 PrimeNumberTheoremAnd modules), same renaming |
| `docs/family003/source-to-native-map.tsv` | upstream module / path ↔ native module / path, one line per absorbed module |
| `scripts/family003/port.py` | the mechanical stage (rename + provenance header) |
| `scripts/family003/compat.py` | records each host-compatibility edit in the edited file's header |

3279 Lean files in total: 3260 absorbed modules plus 19 compatibility files (2942 + 18 for the
zeta / Dirichlet / Hecke closure, then 318 + 1 for the Siegel-zero closure).  (The map lists
3263 upstream modules: three PrimeNumberTheoremAnd modules, `Fourier`, `SmoothExistence` and
`Sobolev`, are identical to files this repository already vendors as
`Zeta23.FromPNTPlus.*`, and imports of them are redirected there.)

## Provenance and edits

Every absorbed module starts with a provenance header naming the source repository, original
path and module, revision, paper and licence, and the line `Host compatibility edits:` —
either `none` (the file is the upstream file with only the module/namespace rename) or `yes`
followed by one bullet per kind of edit.  1123 files carry `yes` (1017 before the Siegel-zero
closure was added).  The kinds of edit, with
counts of files:

* importing a compatibility file that supplies an upstream-named lemma or instance absent at the
  host pin (`Compat.Backports`: `ite_eq_left/right`, `dite_eq_left/right`, `Finset.*₀` product
  bounds; `Compat.MathlibBackports`, `Compat.FinsetInjOn`, `Compat.ContDiffUrysohn`,
  `Compat.IteratedFDerivBound`, `Compat.FiniteIndexComap`, `Compat.FiniteIndexMap`,
  `Compat.ExtendOfIsometry`, `Compat.FiniteQuotientNeZero`, …) — about 600;
* `convert`/`convert_to` run with `(preTransparency := .instances)`, emulating Lean v4.34's
  reducible instances (547), and, after `convert`, closing residual instance-equality goals with
  `with_reducible_and_instances rfl` (≈ 90);
* individual renames and signature changes between the two Mathlib pins
  (`Measurable.of_eval` → `measurable_pi_lambda`, `Isometry.antilipschitzWith` →
  `Isometry.antilipschitz`, `multiplicity_pos_of_dvd` without its finiteness argument,
  `eLpNorm_eq_lintegral_rpow_enorm_toReal` without its measurability argument, `_root_.not_imp`
  for an identifier that is ambiguous with `Classical.not_imp` at the host pin);
* small proof repairs where the host `simp` set differs (an extra `Real.pi_pos.le`, `not_le.mp`
  instead of `simpa` on a set-complement membership, a few side goals);
* four files whose generic Dedekind-domain section gains `[Module.Free ℤ A] [Module.Finite ℤ A]`
  (instances that the upstream Mathlib infers and the host does not); these are hypotheses on
  intermediate lemmas only, discharged at every use in the closure (the closure compiles), and
  do not appear in the public theorems;
* `set_option maxHeartbeats 0` on three theorems (`HighRowsFirstTerms`, `HighRowsSelectedTerms`,
  `HighRowsCentralTerms`): the host kernel exceeds the default limit when checking the upstream
  proof terms (each takes about 11 minutes to check); the proofs are unchanged.

No statement of an upstream theorem used by the endpoints was weakened, no `sorry`, `axiom`,
`native_decide`, `bv_decide` or `implemented_by` appears anywhere under
`RiemannHypothesis/Family003/`, and `#print axioms` on the endpoints is
`[propext, Classical.choice, Quot.sound]` (the repository's exhaustive audit,
`scripts/axiom_audit.lean`, checks every theorem of the absorbed closure as well).

The exact diff of any file against upstream is recoverable by re-running
`scripts/family003/port.py` on the restored bundle into a scratch tree.

## Rows

| row | status | public theorem |
|---|---|---|
| `M1-OAI-ZETA-SEVEN-EIGHTHS` | `DONE_STRONG` | `RiemannHypothesis.QuasiRiemann.riemannZeta_ne_zero_of_seven_eighths_lt_re` (+ `nontrivial_zero_re_mem`) |
| `M1-OAI-DIRICHLET-SEVEN-EIGHTHS` | `DONE_STRONG` | `RiemannHypothesis.DirichletSevenEighths.LFunction_ne_zero_of_seven_eighths_lt_re` |
| `M1-OAI-HECKE-SEVEN-EIGHTHS` | `DONE_STRONG` | `RiemannHypothesis.HeckeSevenEighths.LFunction_ne_zero_of_seven_eighths_lt_re` (+ `ofResidue` and ray-class corollaries) |
| `M1-OAI-SIEGEL-ZERO-GAP` | `DONE_STRONG` | `RiemannHypothesis.SiegelZeroGap.exists_absolute_real_zero_gap` (+ `dirichletRealZeroBound`) |

Evidence: `docs/goal/evidence/2026-10-11-m1-oai-seven-eighths.md` (zeta, Dirichlet),
`docs/goal/evidence/2026-10-11-m1-oai-hecke-seven-eighths.md` (Hecke),
`docs/goal/evidence/2026-10-12-m1-oai-siegel-zero-gap.md` (Siegel zeroes; lists the host-compatibility
edits made for that closure).

## The value of `ζ` at `s = 1`

The zeta statement has no pole exception.  In both pins `riemannZeta` is Mathlib's total
function `ℂ → ℂ`, defined through the even Hurwitz zeta function, with the junk value
`riemannZeta 1 = (γ - log (4π)) / 2` at the pole (`riemannZeta_one`), which is non-zero.  The
proof compiled here is the upstream proof of the upstream statement about that constant; no
completed zeta function is involved.  So the exact upstream claim holds on the host
convention.

## Scope

The first three rows are zero-free half-planes `re s > 7/8`; the fourth excludes Landau–Siegel
zeroes of real primitive Dirichlet `L`-functions.  None of them is the Riemann hypothesis, and
none implies anything about zeroes on the critical line.
