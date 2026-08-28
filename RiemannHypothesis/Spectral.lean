/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The heat-kernel reading of the functional equation

This file makes explicit the classical chain

```text
theta modularity  --(Mellin transform)-->  functional equation of the completed zeta
```

which is the *geometric* content behind the symmetry `s ↦ 1 - s`: `ζ` is the spectral zeta
function attached to the Laplacian on the circle `ℝ/ℤ`, the Jacobi theta function
`θ(it) = ∑_{n ∈ ℤ} e^{-π n² t}` is the trace of the corresponding heat semigroup, its
modular transformation is Poisson summation, and the completed zeta function is the Mellin
transform of `(θ(it) - 1)/2`.  The functional equation is then the `t ↦ 1/t` symmetry of that
integral.

## Main results proved here

* `jacobiTheta_imaginary_axis` : `θ(i/t) = √t · θ(it)` for `t > 0` — the modular
  transformation restricted to the imaginary axis, which is the form in which the heat-kernel
  argument uses it.  Proved from Mathlib's `jacobiTheta_S_smul`, whose own proof is Poisson
  summation for the Gaussian.
* `evenKernel_zero_eq_jacobiTheta` : Mathlib's Hurwitz kernel at `a = 0` is the theta
  function on the imaginary axis.
* `completedRiemannZeta_eq_mellin_jacobiTheta` : for `1 < re s`,
  `Λ(s) = ∫₀^∞ (θ(it) - 1)/2 · t^(s/2) dt/t`, i.e. `Λ(s)` is the Mellin transform of the
  heat trace at `s/2`.  This is the Riemann–Mellin representation, stated in terms of the
  one-variable theta function.

## The rest of the chain

The step from the modularity of `θ` to `Λ(1 - s) = Λ(s)` is carried out inside Mathlib by the
abstract functional-equation machinery: `HurwitzZeta.hurwitzEvenFEPair` is a `WeakFEPair`
whose defining hypothesis `h_feq` is exactly `HurwitzZeta.evenKernel_functional_equation`
(the kernel form of the modular transformation used above), and
`completedRiemannZeta_one_sub` is the resulting symmetry.  Those two declarations are cited,
not reproved, here; `theta_modularity_is_the_input_to_the_functional_equation` and
`completedRiemannZeta_functional_equation` below record them as checked statements so that
the chain is machine-readable end to end.

## What this does *not* say

This is the heat-kernel (geometric) reading of the *functional equation* only.  It says
nothing about the zeroes.  The spectral reading of the zeroes — the Hilbert–Pólya
expectation that the numbers `γ` with `ζ(1/2 + iγ) = 0` are the eigenvalues of a
self-adjoint operator — remains **conjectural**, and nothing in this repository advances it.
-/

noncomputable section

open Complex Filter MeasureTheory Real
open scoped Topology

namespace RiemannHypothesis

/-! ## The theta function on the imaginary axis -/

/-- `I * t` lies in the upper half-plane for `t > 0`. -/
lemma im_I_mul_ofReal_pos {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ)).im := by
  simpa using ht

/-- **Modularity of the theta function on the imaginary axis**: `θ(i/t) = √t · θ(it)` for
`t > 0`.  This is Mathlib's `jacobiTheta_S_smul` (proved there by Poisson summation for the
Gaussian) written on the ray where the heat-kernel argument uses it: `θ(it)` is the trace of
the heat semigroup on `ℝ/ℤ` at time `t`, and this is the statement that small times and large
times are exchanged. -/
theorem jacobiTheta_imaginary_axis {t : ℝ} (ht : 0 < t) :
    jacobiTheta (I * (1 / t : ℝ)) = (Real.sqrt t : ℂ) * jacobiTheta (I * (t : ℝ)) := by
  have hτ : 0 < (I * (t : ℂ)).im := im_I_mul_ofReal_pos ht
  have h := jacobiTheta_S_smul ⟨I * (t : ℂ), hτ⟩
  have hS : ((ModularGroup.S • (⟨I * (t : ℂ), hτ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
      = I * ((1 / t : ℝ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    rw [inv_eq_iff_eq_inv]
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hcoef : (-I * (I * (t : ℂ))) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
    have h1 : -I * (I * (t : ℂ)) = ((t : ℝ) : ℂ) := by
      rw [← mul_assoc]
      simp [Complex.I_mul_I]
    rw [h1, Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [hS] at h
  rw [h, hcoef]

/-! ## The heat trace is Mathlib's Hurwitz kernel at `a = 0` -/

/-- The even Hurwitz kernel at `a = 0` is the theta function on the imaginary axis:
`evenKernel 0 t = θ(it)`. -/
theorem evenKernel_zero_eq_jacobiTheta (t : ℝ) :
    ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) = jacobiTheta (I * (t : ℝ)) := by
  have h : ((0 : UnitAddCircle)) = ((0 : ℝ) : UnitAddCircle) := by norm_num
  rw [h, HurwitzZeta.evenKernel_def, jacobiTheta_eq_jacobiTheta₂]
  simp

/-! ## The Mellin representation of the completed zeta function -/

/-- **The Riemann–Mellin representation**: for `1 < re s` the completed zeta function is the
Mellin transform of the (centred) heat trace,

`Λ(s) = ∫₀^∞ ((θ(it) - 1)/2) t^(s/2) dt/t`.

Together with `jacobiTheta_imaginary_axis` this is the classical route to the functional
equation: splitting the integral at `t = 1` and applying the modular transformation to the
part over `(0,1)` produces an expression manifestly invariant under `s ↦ 1 - s`. -/
theorem completedRiemannZeta_eq_mellin_jacobiTheta {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s
      = mellin (fun t : ℝ => (jacobiTheta (I * (t : ℝ)) - 1) / 2) (s / 2) := by
  have hk : (HurwitzZeta.hurwitzEvenFEPair 0).k < (s / 2).re := by
    change (1 / 2 : ℝ) < (s / 2).re
    rw [Complex.div_re]
    norm_num
    linarith
  have hm := (HurwitzZeta.hurwitzEvenFEPair 0).hasMellin hk
  have hfun : ((HurwitzZeta.hurwitzEvenFEPair 0).f · - (HurwitzZeta.hurwitzEvenFEPair 0).f₀)
      = fun t : ℝ => jacobiTheta (I * (t : ℝ)) - 1 := by
    funext t
    simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, if_pos]
    rw [evenKernel_zero_eq_jacobiTheta]
  rw [hfun] at hm
  have hΛ : completedRiemannZeta s = (HurwitzZeta.hurwitzEvenFEPair 0).Λ (s / 2) / 2 := rfl
  rw [hΛ, ← hm.2, mellin_div_const]

/-! ## The rest of the chain, as checked citations -/

/-- The input to Mathlib's derivation of the functional equation: the modular transformation
of the heat kernel, `evenKernel a x = x^(-1/2) · cosKernel a (1/x)`.  This is
`HurwitzZeta.evenKernel_functional_equation`; it is the hypothesis `h_feq` of the
`WeakFEPair` structure `HurwitzZeta.hurwitzEvenFEPair`, and at `a = 0` it is
`jacobiTheta_imaginary_axis` above.  *Provided by Mathlib; cited, not reproved here.* -/
theorem theta_modularity_is_the_input_to_the_functional_equation
    (a : UnitAddCircle) (x : ℝ) :
    HurwitzZeta.evenKernel a x = 1 / x ^ (1 / 2 : ℝ) * HurwitzZeta.cosKernel a (1 / x) :=
  HurwitzZeta.evenKernel_functional_equation a x

/-- The end of the chain: `Λ(1 - s) = Λ(s)`.  *Provided by Mathlib
(`completedRiemannZeta_one_sub`); cited, not reproved here.*  What the present file adds is
that the object being reflected is the Mellin transform of the heat trace
(`completedRiemannZeta_eq_mellin_jacobiTheta`) and that the reflection is the modular
transformation of that trace (`jacobiTheta_imaginary_axis`). -/
theorem completedRiemannZeta_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

end RiemannHypothesis

end
