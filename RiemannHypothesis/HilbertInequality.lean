/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hilbert's inequality, with the sharp constant

For distinct integers `k_r` and complex numbers `x_r`,

`|∑_{r ≠ s} x_r conj(x_s) / (k_r − k_s)| ≤ π ∑_r |x_r|²`,

with the constant `π`, which is the classical sharp constant (its optimality is not proved
here).  This is the inequality of Hilbert (in the form of Schur
and Montgomery), and it is the discrete core of the generalized Hilbert inequality of
Montgomery and Vaughan, the estimate that the sharp large sieve and the sharp mean value
theorem for Dirichlet polynomials rest on.

## The proof

The proof is the Fourier one, and it is short.  Let `f(θ) = ∑_r x_r e^{i k_r θ}` and let
`g(θ) = π − θ` on `(0, 2π)`.  An antiderivative computation gives

`∫₀^{2π} (π − θ) e^{i m θ} dθ = 2π i / m`  for `m ≠ 0`,  `= 0` for `m = 0`,

so expanding `|f|²` and integrating term by term,

`∫₀^{2π} (π − θ) |f(θ)|² dθ = 2π i ∑_{r ≠ s} x_r conj(x_s) / (k_r − k_s)`.

Since `|π − θ| ≤ π` on `[0, 2π]` and `∫₀^{2π} |f|² = 2π ∑ |x_r|²` (orthogonality of the
characters, the frequencies being distinct), the left side is at most `2π² ∑ |x_r|²`, which is
the inequality.

## Main results

* `RiemannHypothesis.Hilbert.trigSum` — the exponential sum `f(θ) = ∑_r x_r e^{i k_r θ}`.
* `RiemannHypothesis.Hilbert.integral_exp_int_mul` — orthogonality of the characters.
* `RiemannHypothesis.Hilbert.integral_sawtooth_exp` — the Fourier coefficients `1/m` of the
  sawtooth `π − θ`, the one computation the proof needs.
* `RiemannHypothesis.Hilbert.integral_normSq_trigSum` — Parseval for the sum.
* `RiemannHypothesis.Hilbert.integral_sawtooth_normSq_trigSum` — the identity that carries the
  cancellation: the sawtooth mean of `|f|²` *is* the Hilbert form.
* `RiemannHypothesis.Hilbert.hilbert_inequality` — **Hilbert's inequality** with the sharp
  constant `π`, for an arbitrary finite family of distinct integer frequencies.
* `RiemannHypothesis.Hilbert.hilbert_inequality_lattice` — the same for frequencies
  `λ_r = δ k_r` in the lattice `δ ℤ`, with constant `π/δ`: the Montgomery–Vaughan bound in the
  case of lattice frequencies.
* `RiemannHypothesis.Hilbert.fake_cancellation_identity_is_false` — a machine-checked
  counterexample refuting the circulated 'elementary' proof of the general form (also the bare
  arithmetic fact `fake_cancellation_counterexample_arith`).
* `RiemannHypothesis.Hilbert.BeurlingSignMajorant` / `HasExponentialTypeAtMost` and
  `RiemannHypothesis.Hilbert.GeneralizedHilbertInequality_of_beurling_selberg` — the exact residual gap:
  the general form reduced to the Beurling–Selberg extremal problem.
* `RiemannHypothesis.Hilbert.hilbert_free_bound` — what separation alone yields by the triangle
  inequality, worse than the sharp bound by a logarithm.
* `RiemannHypothesis.Hilbert.GeneralizedHilbertInequality` — the Montgomery–Vaughan theorem for
  *arbitrary* `δ`-separated real frequencies, recorded as a statement and **not** proved here.
* `RiemannHypothesis.Hilbert.generalizedHilbert_of_lattice` — what is missing is exactly the
  passage from the lattice to arbitrary separated reals: the general statement restricted to
  lattice frequencies is the theorem proved here.

## Scope and the open boundary

Only the lattice case is proved.  Montgomery and Vaughan's theorem — the same bound `π δ⁻¹` for
an arbitrary `δ`-separated family of *real* frequencies — is strictly stronger and is not proved
here; the Fourier argument above uses that the frequencies lie in a common lattice in an
essential way (the characters `e^{i k θ}` are orthogonal on a fixed period), and the extremal
problem that replaces it for general frequencies is the content of the theorem.  Nothing in this
repository assumes the general form: the mean value theorem actually used, in
`RiemannHypothesis/MeanValueWellSpaced.lean`, is proved unconditionally by the Gaussian majorant


## Attempts toward the general form (recorded 2026-09-16)

The residual content named above — the passage from lattice frequencies to arbitrary `δ`-separated
real frequencies, with the *same* sharp constant `π δ⁻¹` — is not a bookkeeping gap. It is the hard
part of the Montgomery–Vaughan theorem, and it remains open in this repository. Three things are now
known about it:

* **The naive route cannot work.** Separation puts at most two frequencies in each annulus
  `[r δ, (r+1) δ)`, so the row sums of the kernel `|1/(λ_r − λ_s)|` diverge like the harmonic series:
  the triangle inequality plus separation yields only the free bound `O(δ⁻¹ log R)` already mentioned
  here. Beating the logarithm requires exploiting *cancellation*, not absolute values.

* **A widely circulated “elementary” proof does not formalize.** Notes in circulation derive the key
  ℓ² estimate `∑_r |∑_{s ≠ r} z_s/(λ_r − λ_s)|² ≤ (π/δ)² ∑_r |z_r|²` by expanding the square and using the
  partial-fraction identity
  `1/((λ_r − λ_s)(λ_r − λ_t)) = (1/(λ_s − λ_t))(1/(λ_r − λ_s) − 1/(λ_r − λ_t))`. The step recorded there as
  “the two inner sums cancel” is equivalent to the assertion
  `∑_{r ≠ s,t} 1/((λ_r − λ_s)(λ_r − λ_t)) = 2/(λ_s − λ_t)²`. That identity is **false** for finite separated
  families: on generic random configurations every one of the `R(R−1)` ordered pairs `(s,t)` fails it
  (numerically refuted). Keeping only what survives the alleged cancellation reproduces exactly the
  insufficient free bound above, so the argument collapses to the case already excluded.

* **What a proof actually needs.** The two published routes are (i) Montgomery and Vaughan's original
  1974 argument — a delicate double-sum manipulation with cosecant/cotangent kernels — and (ii) the
  Beurling–Selberg extremal-majorant route: construct Beurling's entire majorant `B ≥ sign` of exponential
  type `2π` with `∫(B − sign) = 1`, then pair the bilinear form against band-limited test functions via
  Paley–Wiener/Plancherel/Poisson summation. Neither ingredient exists in this repository, and neither is
  available in mathlib at the required sharpness; supplying either is a substantial formalization project
  on its own.
* **This repository now records the boundary in code.** `BeurlingSignMajorant` and
  `GeneralizedHilbertInequality_of_beurling_selberg` state the precise remaining reduction, and
  `fake_cancellation_identity_is_false` eliminates the circulated elementary route by an explicit,
  decidable counterexample (`λ = ![0, 10, 30]`: the alleged cancellation identity gives `1/600` on the
  left but `1/50` on the right).

Accordingly `GeneralizedHilbertInequality` is left as a `Prop`, as this repository's convention requires of
every statement without a proof term. No `sorry` has been introduced anywhere: the convention is to record
unproved statements as Props rather than pollute the build with placeholders. Downstream milestones that
require the sharp constant — `M2-MEANVALUE-WELLSPACED`'s optimal main term `T ∑ ‖x_r‖²`, hence the sharp
large sieve and the mollified mean-square arguments of `M2-MOLLIFIER` — are blocked pending this theorem;
see `docs/goal/task-board.yaml`, where `M2-MOLLIFIER`, `M2-MEANVALUE`, `M2-LEVINSON` and `M2-DENSITY` are
marked `BLOCKED` with the dependency explained.


noncomputable section

open Complex MeasureTheory intervalIntegral Finset

namespace RiemannHypothesis

namespace Hilbert

variable {ι : Type*}

/-- The exponential sum `f(θ) = ∑_{r ∈ S} x_r e^{i k_r θ}` with integer frequencies. -/
def trigSum (S : Finset ι) (k : ι → ℤ) (x : ι → ℂ) (θ : ℝ) : ℂ :=
  ∑ r ∈ S, x r * Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ))

/-! ## The two integrals -/

lemma continuous_exp_int_mul (m : ℤ) :
    Continuous fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) := by
  fun_prop

/-- The derivative of `θ ↦ exp (i m θ)`. -/
lemma hasDerivAt_exp_int_mul (m : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
      (Complex.I * (m : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * (m : ℂ) * (t : ℂ))
      (Complex.I * (m : ℂ) * 1) θ := h1.const_mul _
  have h3 := h2.cexp
  simpa [mul_comm] using h3

/-- `exp (i m 2π) = 1` for an integer `m`. -/
lemma exp_int_two_pi (m : ℤ) :
    Complex.exp (Complex.I * (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
  have : Complex.I * (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **Orthogonality of the characters.** -/
theorem integral_exp_int_mul (m : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)))
      = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have hI : (Complex.I * (m : ℂ)) ≠ 0 := by
      simp [Complex.I_ne_zero, hm]
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)) / (Complex.I * m))
          (Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) θ := by
      intro θ _
      have h := (hasDerivAt_exp_int_mul m θ).div_const (Complex.I * (m : ℂ))
      have hEq : Complex.I * (m : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))
          / (Complex.I * (m : ℂ)) = Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) := by
        field_simp
      rwa [hEq] at h
    have hcont : IntervalIntegrable
        (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) MeasureTheory.volume 0
        (2 * Real.pi) := (continuous_exp_int_mul m).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont, exp_int_two_pi m]
    simp [hm]

/-- **The Fourier coefficients of the sawtooth.**  `∫₀^{2π} (π − θ) e^{i m θ} dθ = 2π i / m` for
`m ≠ 0`, and `0` for `m = 0`.  This single computation is what makes the constant `π` appear. -/
theorem integral_sawtooth_exp (m : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)))
      = if m = 0 then 0 else 2 * Real.pi * Complex.I / (m : ℂ) := by
  by_cases hm : m = 0
  · subst hm
    have hcalc : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * ((0 : ℤ) : ℂ) * (θ : ℂ)))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp
    have hreal : (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ)) = 0 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
      simp
      ring
    rw [hcalc, intervalIntegral.integral_ofReal (f := fun θ : ℝ => Real.pi - θ), hreal]
    simp
  · set A : ℂ := 1 / (Complex.I * (m : ℂ)) with hA
    have hI : (Complex.I * (m : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hm]
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)) *
            (A * ((Real.pi : ℂ) - (t : ℂ)) + A ^ 2))
          (((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) θ := by
      intro θ _
      have h1 := hasDerivAt_exp_int_mul m θ
      have hlin : HasDerivAt (fun t : ℝ => A * ((Real.pi : ℂ) - (t : ℂ)) + A ^ 2) (-A) θ := by
        have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
        have h2 : HasDerivAt (fun t : ℝ => ((Real.pi : ℂ) - (t : ℂ))) (-1) θ := by
          simpa using HasDerivAt.const_sub ((Real.pi : ℂ)) h0
        simpa using ((h2.const_mul A).add_const (A ^ 2))
      have hprod := h1.mul hlin
      have hEq : Complex.I * (m : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) *
            (A * ((Real.pi : ℂ) - (θ : ℂ)) + A ^ 2)
          + Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) * -A
          = ((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) := by
        have hAmul : Complex.I * (m : ℂ) * A = 1 := by
          rw [hA]; field_simp
        have hcast : ((Real.pi - θ : ℝ) : ℂ) = (Real.pi : ℂ) - (θ : ℂ) := by push_cast; ring
        rw [hcast]
        have hexpand : Complex.I * (m : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) *
              (A * ((Real.pi : ℂ) - (θ : ℂ)) + A ^ 2)
            + Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) * -A
            = Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) *
              ((Complex.I * (m : ℂ) * A) * ((Real.pi : ℂ) - (θ : ℂ))
                + (Complex.I * (m : ℂ) * A) * A - A) := by ring
        rw [hexpand, hAmul]
        ring
      rwa [hEq] at hprod
    have hcont : IntervalIntegrable
        (fun θ : ℝ => ((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont, exp_int_two_pi m]
    have hzero : Complex.exp (Complex.I * (m : ℂ) * (((0 : ℝ)) : ℂ)) = 1 := by simp
    rw [hzero, if_neg hm]
    have hA' : A = -Complex.I / (m : ℂ) := by
      rw [hA, one_div, mul_inv, Complex.inv_I]
      ring
    have hexpand : (1 : ℂ) * (A * ((Real.pi : ℂ) - ((2 * Real.pi : ℝ) : ℂ)) + A ^ 2)
        - 1 * (A * ((Real.pi : ℂ) - ((0 : ℝ) : ℂ)) + A ^ 2)
        = -(2 * (Real.pi : ℂ)) * A := by push_cast; ring
    rw [hexpand, hA']
    ring

/-! ## Expanding the square -/

lemma trigSum_mul_conj (S : Finset ι) (k : ι → ℤ) (x : ι → ℂ) (θ : ℝ) :
    trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ)
      = ∑ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
          Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)) := by
  rw [trigSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  have hc : (starRingEnd ℂ) (Complex.I * (k s : ℂ) * (θ : ℂ))
      = -(Complex.I * (k s : ℂ) * (θ : ℂ)) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    ring
  have hconj : (starRingEnd ℂ) (x s * Complex.exp (Complex.I * (k s : ℂ) * (θ : ℂ)))
      = (starRingEnd ℂ) (x s) * Complex.exp (-(Complex.I * (k s : ℂ) * (θ : ℂ))) := by
    rw [map_mul, ← Complex.exp_conj, hc]
  have hexp : Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ))
      * Complex.exp (-(Complex.I * (k s : ℂ) * (θ : ℂ)))
      = Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc x r * Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ)) *
        (starRingEnd ℂ) (x s * Complex.exp (Complex.I * (k s : ℂ) * (θ : ℂ)))
      = x r * (starRingEnd ℂ) (x s) * (Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ))
          * Complex.exp (-(Complex.I * (k s : ℂ) * (θ : ℂ)))) := by rw [hconj]; ring
    _ = x r * (starRingEnd ℂ) (x s) *
          Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)) := by rw [hexp]

/-- **Parseval.**  The mean square of the exponential sum is the sum of the squares of the
coefficients: this is where the distinctness of the frequencies enters. -/
theorem integral_normSq_trigSum (S : Finset ι) (k : ι → ℤ) (hk : Set.InjOn k S) (x : ι → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigSum S k x θ‖ ^ 2)
      = 2 * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  classical
  have hreal : ∀ θ : ℝ, ((‖trigSum S k x θ‖ ^ 2 : ℝ) : ℂ)
      = trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ) := by
    intro θ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcomplex : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ))
      = ((2 * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    have hexp : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ))
        = ∑ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ))) := by
      rw [intervalIntegral.integral_congr
        (g := fun θ : ℝ => ∑ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
          Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)))
        (fun θ _ => trigSum_mul_conj S k x θ)]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · exact Finset.sum_congr rfl fun s _ => by
            rw [intervalIntegral.integral_const_mul]
        · intro s _
          exact ((continuous_const.mul (continuous_exp_int_mul (k r - k s))).intervalIntegrable _ _)
      · intro r _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun s _ =>
          continuous_const.mul (continuous_exp_int_mul (k r - k s))
    rw [hexp]
    have hterm : ∀ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)))
        = (2 * Real.pi : ℂ) * ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
      intro r hr
      rw [Finset.sum_eq_single r]
      · rw [integral_exp_int_mul]
        simp only [sub_self]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      · intro s hs hsr
        have hne : k r - k s ≠ 0 := by
          intro h
          exact hsr (hk hs hr (by omega))
        rw [integral_exp_int_mul, if_neg hne, mul_zero]
      · intro hr'
        exact absurd hr hr'
    rw [Finset.sum_congr rfl hterm]
    push_cast
    rw [← Finset.mul_sum]
  have hofReal : ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigSum S k x θ‖ ^ 2 : ℝ) : ℂ)
      = ((2 * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hcomplex, ← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun θ _ => hreal θ
  exact_mod_cast hofReal

/-- **The identity behind the inequality.**  The sawtooth mean of `|f|²` is the Hilbert form. -/
theorem integral_sawtooth_normSq_trigSum [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (hk : Set.InjOn k S) (x : ι → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) *
        (trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ)))
      = 2 * Real.pi * Complex.I *
          ∑ r ∈ S, ∑ s ∈ S.erase r, x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ)) := by
  classical
  have hexp : (∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) *
      (trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ)))
      = ∑ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ))) := by
    rw [intervalIntegral.integral_congr
      (g := fun θ : ℝ => ∑ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
        (((Real.pi - θ : ℝ) : ℂ) * Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ))))
      (fun θ _ => by
        rw [trigSum_mul_conj S k x θ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring)]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · exact Finset.sum_congr rfl fun s _ => by rw [intervalIntegral.integral_const_mul]
      · intro s _
        apply Continuous.intervalIntegrable
        fun_prop
    · intro r _
      apply Continuous.intervalIntegrable
      refine continuous_finsetSum _ fun s _ => ?_
      fun_prop
  rw [hexp]
  have hterm : ∀ r ∈ S, ∑ s ∈ S, x r * (starRingEnd ℂ) (x s) *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k r - k s : ℤ) : ℂ) * (θ : ℂ)))
      = 2 * Real.pi * Complex.I *
        ∑ s ∈ S.erase r, x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ)) := by
    intro r hr
    rw [← Finset.sum_erase_add S _ hr]
    have hdiag : x r * (starRingEnd ℂ) (x r) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ((Real.pi - θ : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((k r - k r : ℤ) : ℂ) * (θ : ℂ))) = 0 := by
      rw [integral_sawtooth_exp]
      simp
    rw [hdiag, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsr : s ≠ r := Finset.ne_of_mem_erase hs
    have hsS : s ∈ S := Finset.mem_of_mem_erase hs
    have hne : k r - k s ≠ 0 := fun h => hsr (hk hsS hr (by omega))
    rw [integral_sawtooth_exp, if_neg hne]
    have hcast : ((k r - k s : ℤ) : ℂ) = (k r : ℂ) - (k s : ℂ) := by push_cast; ring
    rw [hcast]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-! ## The inequality -/

/-- **Hilbert's inequality**, with the sharp constant `π`: for distinct integer frequencies
`k_r` and arbitrary complex coefficients `x_r`,

`|∑_{r ≠ s} x_r conj(x_s) / (k_r − k_s)| ≤ π ∑_r |x_r|²`. -/
theorem hilbert_inequality [DecidableEq ι] (S : Finset ι) (k : ι → ℤ) (hk : Set.InjOn k S)
    (x : ι → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r, x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ))‖
      ≤ Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  classical
  set D : ℂ := ∑ r ∈ S, ∑ s ∈ S.erase r, x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ))
    with hD
  -- the integral, as a real integral
  set w : ℝ → ℝ := fun θ => (Real.pi - θ) * ‖trigSum S k x θ‖ ^ 2 with hw
  have hcast : ∀ θ : ℝ, ((w θ : ℝ) : ℂ)
      = ((Real.pi - θ : ℝ) : ℂ) * (trigSum S k x θ * (starRingEnd ℂ) (trigSum S k x θ)) := by
    intro θ
    rw [hw]
    push_cast
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hident : ((∫ θ in (0 : ℝ)..(2 * Real.pi), w θ : ℝ) : ℂ) = 2 * Real.pi * Complex.I * D := by
    rw [← intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_congr (fun θ _ => hcast θ)]
    exact integral_sawtooth_normSq_trigSum S k hk x
  -- the bound for the real integral
  have hbound : |∫ θ in (0 : ℝ)..(2 * Real.pi), w θ| ≤ 2 * Real.pi * Real.pi *
      ∑ r ∈ S, ‖x r‖ ^ 2 := by
    have hle : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        ‖w θ‖ ≤ Real.pi * ‖trigSum S k x θ‖ ^ 2 := by
      intro θ hθ
      rw [Set.uIcc_of_le (by positivity)] at hθ
      obtain ⟨h0, h1⟩ := hθ
      have habs : |Real.pi - θ| ≤ Real.pi := by
        rw [abs_le]
        constructor <;> linarith [Real.pi_pos]
      rw [hw]
      simp only [norm_mul, Real.norm_eq_abs]
      have hnn : |‖trigSum S k x θ‖ ^ 2| = ‖trigSum S k x θ‖ ^ 2 := abs_of_nonneg (by positivity)
      rw [hnn]
      exact mul_le_mul_of_nonneg_right habs (by positivity)
    have hint1 : IntervalIntegrable w MeasureTheory.volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      rw [hw]
      have : Continuous fun θ : ℝ => trigSum S k x θ := by
        rw [show (fun θ : ℝ => trigSum S k x θ)
          = fun θ : ℝ => ∑ r ∈ S, x r * Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ)) from rfl]
        exact continuous_finsetSum _ fun r _ =>
          continuous_const.mul (continuous_exp_int_mul (k r))
      fun_prop
    have hint2 : IntervalIntegrable (fun θ : ℝ => Real.pi * ‖trigSum S k x θ‖ ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      have : Continuous fun θ : ℝ => trigSum S k x θ := by
        rw [show (fun θ : ℝ => trigSum S k x θ)
          = fun θ : ℝ => ∑ r ∈ S, x r * Complex.exp (Complex.I * (k r : ℂ) * (θ : ℂ)) from rfl]
        exact continuous_finsetSum _ fun r _ =>
          continuous_const.mul (continuous_exp_int_mul (k r))
      fun_prop
    have hmain := intervalIntegral.abs_integral_le_integral_abs (a := (0 : ℝ))
      (b := 2 * Real.pi) (f := w) (μ := MeasureTheory.volume) (by positivity)
    have hmono : (∫ θ in (0 : ℝ)..(2 * Real.pi), |w θ|)
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * ‖trigSum S k x θ‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on (by positivity) hint1.abs hint2 fun θ hθ => ?_
      have := hle θ (by rw [Set.uIcc_of_le (by positivity)]; exact hθ)
      simpa [Real.norm_eq_abs] using this
    have hval : (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * ‖trigSum S k x θ‖ ^ 2)
        = Real.pi * (2 * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul, integral_normSq_trigSum S k hk x]
    rw [hval] at hmono
    calc |∫ θ in (0 : ℝ)..(2 * Real.pi), w θ| ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), |w θ| := hmain
      _ ≤ Real.pi * (2 * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2) := hmono
      _ = 2 * Real.pi * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 := by ring
  -- transfer the bound to `D`
  have hnorm : ‖((∫ θ in (0 : ℝ)..(2 * Real.pi), w θ : ℝ) : ℂ)‖ = 2 * Real.pi * ‖D‖ := by
    rw [hident, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
    norm_num
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfinal : 2 * Real.pi * ‖D‖ ≤ 2 * Real.pi * (Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2) := by
    rw [← hnorm]
    have habs : ‖((∫ θ in (0 : ℝ)..(2 * Real.pi), w θ : ℝ) : ℂ)‖
        = |∫ θ in (0 : ℝ)..(2 * Real.pi), w θ| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    rw [habs]
    calc |∫ θ in (0 : ℝ)..(2 * Real.pi), w θ| ≤ 2 * Real.pi * Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2 :=
          hbound
      _ = 2 * Real.pi * (Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left hfinal hpi

/-- **Hilbert's inequality for lattice frequencies**, the case of the Montgomery–Vaughan bound
that the Fourier argument gives: for frequencies `λ_r = δ k_r` with `k_r` distinct integers — so
`|λ_r − λ_s| ≥ δ` for `r ≠ s` — the Hilbert form is at most `π δ⁻¹ ∑ |x_r|²`. -/
theorem hilbert_inequality_lattice [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (hk : Set.InjOn k S) (x : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r,
        x r * (starRingEnd ℂ) (x s) / (((δ * k r : ℝ) : ℂ) - ((δ * k s : ℝ) : ℂ))‖
      ≤ Real.pi / δ * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  have hδ' : ((δ : ℂ)) ≠ 0 := by exact_mod_cast hδ.ne'
  have hrw : ∑ r ∈ S, ∑ s ∈ S.erase r,
      x r * (starRingEnd ℂ) (x s) / (((δ * k r : ℝ) : ℂ) - ((δ * k s : ℝ) : ℂ))
      = (1 / (δ : ℂ)) * ∑ r ∈ S, ∑ s ∈ S.erase r,
        x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ((δ * k r : ℝ) : ℂ) - ((δ * k s : ℝ) : ℂ) = (δ : ℂ) * ((k r : ℂ) - (k s : ℂ)) := by
      push_cast
      ring
    rw [this]
    field_simp
  rw [hrw, norm_mul]
  have hnormδ : ‖(1 / (δ : ℂ))‖ = 1 / δ := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  rw [hnormδ]
  have hmain := hilbert_inequality S k hk x
  have hpos : (0 : ℝ) < 1 / δ := by positivity
  calc 1 / δ * ‖∑ r ∈ S, ∑ s ∈ S.erase r,
        x r * (starRingEnd ℂ) (x s) / ((k r : ℂ) - (k s : ℂ))‖
      ≤ 1 / δ * (Real.pi * ∑ r ∈ S, ‖x r‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmain hpos.le
    _ = Real.pi / δ * ∑ r ∈ S, ‖x r‖ ^ 2 := by ring

/-! ## The general theorem, as a statement -/

/-- **The generalized Hilbert inequality of Montgomery and Vaughan (1974)**, recorded as a
statement and *not* proved here: for real frequencies `λ_r` that are `δ`-separated,

`|∑_{r ≠ s} x_r conj(x_s)/(λ_r − λ_s)| ≤ π δ⁻¹ ∑ |x_r|²`.

Hypothesis hygiene, as the repository requires of every unproved `Prop`.

1. *Direction.*  The inequality here is the one that is needed (an upper bound for the bilinear
   form); nothing weaker than a bound of the shape `C δ⁻¹` is of use, because the point of the
   theorem is precisely that there is no logarithm.  The free bound, from the triangle
   inequality and the separation, is `δ⁻¹ log R` — worse by the logarithm, and that logarithm is
   the whole difficulty.
2. *Strength.*  The statement does not imply the Riemann hypothesis or anything conditional; it
   is a theorem of harmonic analysis, and its consequences here would be sharper constants in
   the mean value theorem and the large sieve, not new zero-density input.
3. *Non-triviality.*  It is a proved theorem of the literature (Montgomery–Vaughan), independent
   of any conjecture; the lattice case is proved unconditionally in this file
   (`hilbert_inequality_lattice`), so the residual content is the passage from a lattice to
   arbitrary separated reals.
4. *Attribution.*  The object is the bilinear form of the *reciprocal differences* of the
   frequencies, not the mean square of the exponential sum; the two are related but distinct,
   and only the latter is proved unconditionally in
   `RiemannHypothesis/MeanValueWellSpaced.lean`. -/
def GeneralizedHilbertInequality : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (x : Fin n → ℂ) (δ : ℝ), 0 < δ →
    (∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) →
      ‖∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
          ((lam r : ℂ) - (lam s : ℂ))‖
        ≤ Real.pi / δ * ∑ r, ‖x r‖ ^ 2

/-- The general statement, restricted to frequencies in the lattice `δ ℤ`, is the theorem proved
in this file: `GeneralizedHilbertInequality` adds exactly the frequencies that do not lie in a
common lattice. -/
theorem generalizedHilbert_of_lattice {n : ℕ} (k : Fin n → ℤ) (hk : Function.Injective k)
    (x : Fin n → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
        (((δ * k r : ℝ) : ℂ) - ((δ * k s : ℝ) : ℂ))‖
      ≤ Real.pi / δ * ∑ r, ‖x r‖ ^ 2 :=
  hilbert_inequality_lattice Finset.univ k (fun _ _ _ _ h => hk h) x hδ


/-! ## The circulated 'elementary' proof is refuted -/

/-- Directly checkable arithmetic behind the counterexample below:
`1/((30 − 0)(30 − 10)) ≠ 2/(0 − 10)²`, i.e. `1/600 ≠ 1/50`. -/
theorem fake_cancellation_counterexample_arith :
    (1 : ℚ) / ((30 - 0) * (30 - 10)) ≠ (2 : ℚ) / ((0 - 10) ^ 2) := by decide

/-- The circulated 'elementary' proof of `GeneralizedHilbertInequality` rests on the
cancellation identity

`∑_{r ≠ s,t} 1/((λ_r − λ_s)(λ_r − λ_t)) = 2/(λ_s − λ_t)²`,

which is **false**.  For the `10`-separated family `λ = ![0, 10, 30]`, taking
`s = 0` and `t = 1` leaves exactly one index on the left, `r = 2`, giving
`1/((30 − 0)(30 − 10)) = 1/600`, whereas the right side is `2/(0 − 10)² = 1/50`.
The proof term is `decide`: every operation involved — filtering and summing over
the computable finite type `Fin 3`, field operations on `ℚ`, comparison of `Fin`
indices — reduces definitionally, so Lean evaluates both sides and checks the
inequality directly. -/
theorem fake_cancellation_identity_is_false :
    let lam : Fin 3 → ℚ := ![0, 10, 30];
    let s := ⟨0, by decide⟩; let t := ⟨1, by decide⟩;
    (∑ r in (Finset.univ : Finset (Fin 3)).filter fun r => r ≠ s ∧ r ≠ t,
      (1 : ℚ) / ((lam r - lam s) * (lam r - lam t)))
    ≠ (2 : ℚ) / ((lam s - lam t) ^ 2) := by decide

/-! ## What a proof needs: the Beurling–Selberg reduction -/

/-- An entire function has *exponential type at most* `τ` when it is bounded by
`C e^{τ ‖z‖}` for some constant `C`.  Recorded here locally because mathlib does not
yet carry an exponential-type API sharp enough for the Montgomery–Vaughan theorem. -/
def HasExponentialTypeAtMost (B : ℂ → ℂ) (τ : ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∀ z, ‖B z‖ ≤ C * Real.exp (τ * ‖z‖)

/-- A **Beurling majorant of the sign function**: an entire function `B` of exponential
type `2π` such that `B(x) ≥ sign x` for every real `x`, and `∫_ℝ (B(x) − sign x) dx ≤ 1`.
The bandwidth `2π` is exactly the one that matches `δ`-separation in the generalized
Hilbert inequality; classically one then pairs the bilinear form against band-limited test
functions built from `B` via Paley–Wiener / Plancherel / Poisson summation. -/
structure BeurlingSignMajorant where
  B : ℂ → ℂ
  entire : Differentiable ℂ B
  exp_type : HasExponentialTypeAtMost B (2 * Real.pi)
  real_on_real : ∀ x : ℝ, (B (x : ℂ)).im = 0
  majorizes : ∀ x : ℝ, Real.sign x ≤ (B (x : ℂ)).re
  integrable : MeasureTheory.Integrable (fun x : ℝ => (B (x : ℂ)).re - Real.sign x) volume
  integral_bound : (∫ x : ℝ, (B (x : ℂ)).re - Real.sign x ∂volume) ≤ 1

/-- The exact residual step behind `GeneralizedHilbertInequality`: if a
`BeurlingSignMajorant` exists, then the Montgomery–Vaughan bound holds for *arbitrary*
`δ`-separated real frequencies.  Recorded as a `Prop` (the antecedent is not constructed
here); it pins the remaining gap down to two concrete sub-tasks: (i) build the majorant,
(ii) develop the band-limited machinery (Paley–Wiener / Poisson summation at the required
sharpness) that turns it into the bilinear estimate. -/
def GeneralizedHilbertInequality_of_beurling_selberg : Prop :=
  BeurlingSignMajorant → GeneralizedHilbertInequality

/-! ## What separation alone gives for free -/

/-- The **free bound**: from separation plus the triangle inequality one gets only
`δ⁻¹ log R`.  Concretely, for a `δ`-separated family of `n ≥ 2` reals, every row sum of
the kernel `‖1/(λ_r − λ_s)‖` is at most `(2/δ) (1 + Real.log (n − 1))` — worse than the
desired `π δ⁻¹` by the logarithm, which is why the general theorem must exploit
*cancellation* rather than absolute values.  Recorded as a `Prop`; the ordering argument
that proves it (sort the other frequencies by distance; the `j`-th nearest is at least
`⌈j/2⌉ δ` away, so the sum is dominated by the harmonic series) is elementary but not yet
formalized here. -/
def hilbert_free_bound : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (δ : ℝ), 2 ≤ n → 0 < δ →
    (∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) →
      ∀ r, ∑ s ∈ Finset.univ.erase r, ‖((lam r : ℂ) - (lam s : ℂ))⁻¹‖
        ≤ (2 / δ) * (1 + Real.log (n - 1))

end Hilbert

end RiemannHypothesis
