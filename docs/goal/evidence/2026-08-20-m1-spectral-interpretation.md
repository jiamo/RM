# M1-SPECTRAL-INTERPRETATION (2026-08-20)

New file: `RiemannHypothesis/Spectral.lean`.

## The chain, step by step

| step | status | declaration |
|---|---|---|
| 1. Poisson summation for the Gaussian | provided by mathlib | used inside `jacobiTheta_S_smul` |
| 2. modularity of `θ` | provided by mathlib | `jacobiTheta_S_smul` |
| 2'. modularity on the imaginary axis, `θ(i/t) = √t θ(it)` | **proved here** | `RiemannHypothesis.jacobiTheta_imaginary_axis` |
| 3. the heat trace is mathlib's Hurwitz kernel at `a = 0` | **proved here** | `RiemannHypothesis.evenKernel_zero_eq_jacobiTheta` |
| 4. Mellin: `Λ(s) = ∫₀^∞ ((θ(it) - 1)/2) t^(s/2) dt/t` for `1 < re s` | **proved here** | `RiemannHypothesis.completedRiemannZeta_eq_mellin_jacobiTheta` |
| 5. modularity is the hypothesis of mathlib's FE pair | provided by mathlib, cited | `RiemannHypothesis.theta_modularity_is_the_input_to_the_functional_equation` (`= HurwitzZeta.evenKernel_functional_equation`) |
| 6. `Λ(1 - s) = Λ(s)` | provided by mathlib, cited | `RiemannHypothesis.completedRiemannZeta_functional_equation` (`= completedRiemannZeta_one_sub`) |

Steps 2', 3, 4 are new Lean proofs in this repository; steps 1, 2, 5, 6 are mathlib results
and are marked as such both in the docstrings and in the table above. The derivation of
step 6 from step 5 happens inside mathlib's abstract functional-equation machinery
(`HurwitzZeta.hurwitzEvenFEPair : WeakFEPair ℂ`, whose field `h_feq` is exactly step 5); it
is **not** re-derived here.

## Why step 4 is the substance

Mathlib defines `completedRiemannZeta` through the Hurwitz-zeta machinery, so the classical
Riemann–Mellin representation in terms of the *one-variable* theta function
`θ(τ) = ∑_{n ∈ ℤ} e^{π i n² τ}` is not directly available. Step 4 recovers it: it applies
`WeakFEPair.hasMellin` to `hurwitzEvenFEPair 0` at `s/2` (legitimate because
`k = 1/2 < re(s/2)` exactly when `1 < re s`), identifies the pair's `f` with the heat trace
through step 3, and divides by the constant `2`.

## Geometric reading, and its limit

`θ(it) = ∑_{n ∈ ℤ} e^{-π n² t}` is the trace of the heat semigroup on `ℝ/ℤ`, so `Λ(s)` is
the Mellin transform of that trace and the functional equation is the `t ↦ 1/t` symmetry of
the trace. This is the geometric reading of the *functional equation* only. The spectral
reading of the *zeroes* (Hilbert–Pólya) is conjectural; nothing here advances it, and the
file says so.

## Commands

```bash
lake build                               # 3195 jobs, success
./scripts/audit.sh                       # OK
lake env lean scripts/revalidation.lean  # no output, exit 0
```

Axioms of the three theorems proved here: `[propext, Classical.choice, Quot.sound]`.
