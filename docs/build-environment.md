# Building this project

`lake build` builds the whole project: 12,510 jobs, including the vendored `Zeta23` library and
the native absorption `RiemannHypothesis/Family003`. (At commit `5960dab` the `Challenge`
target failed, because `Challenge.lean` referred to theorems of `RiemannHypothesis.Main` without
importing it. This was fixed on 2026-10-18 by importing `RiemannHypothesis.Main` in
`Challenge.lean`; every target now builds.) If it does not build for you, the cause is almost
certainly one of the two below. Both are dependency-resolution problems, not Lean problems.
Memory is the third constraint; see "Resources" below.

## 0. The manifest is tracked

`lake-manifest.json` is committed and is not ignored by `.gitignore`. It pins Mathlib at
`db584cd6d46c92f209a44c0f1c829460d327499d` and contains the path dependency `Zeta23`
(`vendor/zeta23`). With the committed manifest, `lake build` resolves nothing new. Do not
replace it with a manifest regenerated elsewhere.

## 1. `error: dependency 'Zeta23' not in manifest`

`Zeta23` is a **path** dependency (`vendor/zeta23`, declared in `lakefile.toml`) and must have a
corresponding entry in `lake-manifest.json`. A manifest regenerated without it, or copied from a
checkout that predates the vendoring, makes `lake build` fail before it compiles anything. The
committed manifest contains

```json
{"type": "path", "scope": "", "name": "Zeta23",
 "manifestFile": "lake-manifest.json", "inherited": false,
 "dir": "vendor/zeta23", "configFile": "lakefile.toml"}
```

If you regenerate the manifest with `lake update`, keep that entry.

## 2. Toolchain / Mathlib pin mismatch

The three pins must agree:

| file | value |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.33.0` |
| `lakefile.toml` (`mathlib` rev) | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| `vendor/zeta23/lean-toolchain`, `vendor/zeta23/lakefile.toml` | the same pair |

A mismatch shows up as *dependency* modules failing to compile (`Batteries`, `Aesop`,
`Plausible`, even `Mathlib.*`), with errors such as ``object file '…/Lean/Meta/GlobalInstances.olean'
… does not exist`` or ``'Nat.sqrt' has already been declared``. These errors mean that a
Mathlib checkout built for one Lean release is being recompiled by a different one. Editing this
repository's own sources will not fix it.

To recover, re-resolve the dependencies against the pins above and fetch the matching prebuilt
artefacts:

```sh
rm -rf .lake/packages          # only if the packages directory is stale or symlinked elsewhere
lake exe cache get             # fetches the Mathlib olean cache for the pinned revision
lake build
```

`lake exe cache get` downloads about 8,700 prebuilt Mathlib files, so the only long step is the
download. After it, a cold `lake build` compiles only this repository and `vendor/zeta23`.

## Continuous integration

`.github/workflows/ci.yml` runs **only when started by hand** (`on: workflow_dispatch`): from
the Actions tab ("CI" → "Run workflow") or with `gh workflow run CI`. It does not run on push or
on pull requests. This is the owner's decision for as long as no runner with at least 32 GB of
RAM is configured, because three modules need about 22 GB each (see "Resources" below). To
re-enable automatic runs once such a runner exists, set the repository variable `CI_RUNNER` to
its label and add `push:` and `pull_request:` back next to `workflow_dispatch:` in the `on:`
block; the comment above that block in `ci.yml` shows the three lines. A newer run on the same
ref cancels the older one. The job runs these steps:

1. Install elan and the toolchain named in `lean-toolchain`.
2. Run `lake exe cache get` to fetch the prebuilt Mathlib cache. Mathlib is never compiled.
3. Restore `.lake/build` and `vendor/zeta23/.lake/build` from the Actions cache. The key is
   `lake-build-v1-<os>-<hash of lean-toolchain and lake-manifest.json>-<sha>-<run id>-<attempt>`.
   The restore keys drop the run suffix and then the sha, so a run starts from the latest saved
   build of the same commit, or failing that of any commit with the same toolchain and
   manifest.
4. Run `lake build` under `timeout 300m`.
5. **Save the build directories under `if: always()`**, also when the build timed out or the
   run was cancelled. Each module that finished keeps its `.olean` and trace, so a re-run
   resumes where the last run stopped. The key carries the run id and attempt, so every attempt
   saves its own progress instead of colliding with an earlier save.
6. Run `./scripts/audit.sh`. It calls `lake build` again, which is then a no-op.
7. Run `python3 scripts/goal_state.py validate`.

The job limit is 350 minutes. `--wfail` is not used, because the imported code has warnings.

**A cold first run will not finish in one job.** It times out after 300 minutes, saves its
partial build, and must be started again by hand, possibly once or twice. Each new run resumes
from the saved cache. Once a build is cached, a run recompiles only the modules changed since
the saved build and what depends on them. The cached build is about 10 GB on disk
(`.lake/build` 9.1 GB, `vendor/zeta23/.lake/build` 0.97 GB), but it compresses to about 1.05 GB
(measured with `tar | zstd -3`, roughly what the cache action does). So one saved entry fits
well inside the 10 GB per-repository Actions cache quota. When the quota fills up, GitHub evicts
the oldest entries first.

### Resources (measured 2026-10-18, see `docs/goal/evidence/2026-10-18-m2-meanvalue-mv-sharp.md`)

* Wall time: a nearly cold `lake build` took 8,406 s (2 h 20 min) on an 8-core, 64 GB machine.
  It compiled 3,757 modules; Mathlib was prebuilt, and about 50 of this repository's modules
  were already built at the start. Much of `Family003` is a long chain of dependent modules, and
  for long stretches only one module was compiling. More cores therefore help less than the core
  count suggests, and single-core speed matters more. A second run on the same kind of machine,
  from an empty `.lake/build`, took 6,049 s (1 h 41 min) for 12,510 jobs; the peak memory used
  by the whole machine was 25.6 GB.
* Slowest modules: `Family003/NumberTheory/DirichletL/Detector/HighRows{First,Selected,Central}Terms`
  (about 15 minutes each), then
  `Family003/NumberTheory/SiegelZeros/LocalAlgebra/LocalQuotientEquiv` (5 min) and
  `Zeta23.ThmE.PrimeSideChi` (5 min). Every other module took under 2 minutes.
* **Memory: the 22 GB modules.** Those three `HighRows…Terms` modules each need about 22 GB
  of RAM (peak anonymous memory 22.3 GB, peak resident set 27.3 GB including the memory-mapped
  Mathlib `.olean` files, measured on a solo run of `HighRowsFirstTerms`). The next largest module,
  `Family003/NumberTheory/DirichletL/GaussSum/ActiveReindexing`, peaks at 3.6 GB anonymous, and
  almost every other module stays below 1 GB of anonymous memory. **7 GB is therefore not
  enough.** A standard GitHub-hosted runner for a private repository (2 cores, about 7 GB)
  cannot compile those three modules. Point the workflow at a runner with at least 32 GB of RAM
  by setting the repository variable `CI_RUNNER` to its label: a larger GitHub-hosted runner or
  a self-hosted one. `ci.yml` uses `${{ vars.CI_RUNNER || 'ubuntu-latest' }}`. Until such a
  runner exists, CI is started only by hand (see "Continuous integration" above).
* Parallelism: this Lake (5.0, with Lean 4.33.0) has no `-j` option. The number of modules
  compiled at once follows the size of Lean's thread pool, which the environment variable
  `LEAN_NUM_THREADS` sets. For example, `LEAN_NUM_THREADS=1 lake build` compiles one module at a
  time. This keeps two of the heavy modules from overlapping, but does not reduce the memory of
  a single one.

## Notes

* Do not point the project at whatever Mathlib happens to be installed system-wide. The sources
  here use lemma names from the pinned revision (`intervalIntegral.integral_finsetSum`,
  `continuous_finsetSum`, …) whose spelling differs in neighbouring releases.
* To build one module, run, e.g., `lake build RiemannHypothesis.MontgomeryVaughan`. The default
  targets are `RiemannHypothesis`, `Challenge` and `Solution`.
* `Challenge.lean` contains the challenge statements. In this tree each of its three theorems
  is a direct reference to the equivalence proved in `RiemannHypothesis.Main`, so it has no
  `sorry` either; `scripts/audit.sh` still allows `sorry` there. Nothing under
  `RiemannHypothesis/` uses `sorry`.
