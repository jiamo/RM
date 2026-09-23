# Building this project

`lake build` builds the whole project — 9221 targets, including the vendored `Zeta23` library —
with no errors. If it does not build for you, the cause is almost certainly one of the two
below; both are dependency-resolution problems, not Lean problems.

## 1. `error: dependency 'Zeta23' not in manifest`

`Zeta23` is a **path** dependency (`vendor/zeta23`, declared in `lakefile.toml`) and must have a
corresponding entry in `lake-manifest.json`. A manifest regenerated without it — or copied from a
checkout that predates the vendoring — makes `lake build` fail before it compiles anything. The
committed manifest now contains

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

Symptoms of a mismatch are *dependency* modules failing to compile — `Batteries`, `Aesop`,
`Plausible`, even `Mathlib.*` — with errors such as ``object file '…/Lean/Meta/GlobalInstances.olean'
… does not exist`` or ``'Nat.sqrt' has already been declared``. Those mean a Mathlib checkout built
for one Lean release is being recompiled by a different one, and no amount of editing this
repository's own sources will fix it.

The recovery is to re-resolve the dependencies against the pins above and fetch the matching
prebuilt artefacts:

```sh
rm -rf .lake/packages          # only if the packages directory is stale or symlinked elsewhere
lake update -R                 # clones Mathlib at the pinned rev and runs its cache fetch
lake build
```

`lake update -R` downloads the Mathlib olean cache for the pinned revision (about 8700 files),
so the only long step is that download; afterwards a cold `lake build` compiles just this
repository and `vendor/zeta23`.

## Notes

* Do not point the project at whatever Mathlib happens to be installed system-wide. The sources
  here use lemma names from the pinned revision (`intervalIntegral.integral_finsetSum`,
  `continuous_finsetSum`, …) whose spelling differs in neighbouring releases.
* Build a specific module with, e.g., `lake build RiemannHypothesis.HilbertFreeBound`; the default
  targets are `RiemannHypothesis`, `Challenge` and `Solution`.
* `Challenge.lean` contains the challenge statements and deliberately still uses `sorry`; nothing
  under `RiemannHypothesis/` does.
