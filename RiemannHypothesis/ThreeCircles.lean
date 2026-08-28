/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Complex.Hadamard

/-!
# Hadamard's three-circles theorem

Mathlib has the three-*lines* theorem, `Complex.HadamardThreeLines.norm_le_interp_of_mem_`
`verticalClosedStrip'`: a bounded function holomorphic on a vertical strip and continuous on its
closure obeys the logarithmically convex interpolation of its bounds on the two boundary lines.
This file transports it, along the exponential map, to the three-*circles* theorem: for `f`
holomorphic on a neighbourhood of the closed annulus `r₁ ≤ |z| ≤ r₃`, the maximum modulus
`M(r) = max_{|z| = r} ‖f z‖` satisfies

  `log M(r) ≤ (1 − λ) log M(r₁) + λ log M(r₃)`,   `λ = log(r/r₁)/log(r₃/r₁)`,

that is, `log M` is a convex function of `log r`.

## Main results

* `norm_le_rpow_mul_rpow_of_annulus` — the interpolation bound `‖f z‖ ≤ a^(1−λ) b^λ` at a point
  `z` of the annulus, given `‖f‖ ≤ a` on the inner circle and `‖f‖ ≤ b` on the outer one.
* `three_circles` — the same statement in the classical form, with `λ` written out as
  `log(‖z‖/r₁)/log(r₃/r₁)`.

## Why it is here

The tool is what the repository is missing at two open boundaries: the converse direction of
Backlund's criterion (`RiemannHypothesis/LindelofDensity.lean`), and the deduction of the Lindelöf
hypothesis from the Riemann hypothesis.  Both proceed by applying a convexity estimate to `log ζ`
on discs, after Borel–Carathéodory has made `log ζ` small in the mean.  Neither deduction is
carried out here; this file proves only the general analytic statement.  The second of the two is
carried out, away from the critical line, in `RiemannHypothesis/LindelofFromRH.lean`.

## Scope

`f` is assumed analytic on a neighbourhood of the *closed* annulus, which is the form in which the
theorem is used.  No claim is made about the sharpness of the bound, and nothing here mentions
`ζ`.
-/

namespace RiemannHypothesis

open Complex Set Metric

/-- The closed annulus `r₁ ≤ ‖z‖ ≤ r₃`. -/
def closedAnnulus (r₁ r₃ : ℝ) : Set ℂ := {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₃}

lemma isCompact_closedAnnulus (r₁ r₃ : ℝ) : IsCompact (closedAnnulus r₁ r₃) := by
  have hclosed : IsClosed (closedAnnulus r₁ r₃) := by
    have h1 : IsClosed {z : ℂ | r₁ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {z : ℂ | ‖z‖ ≤ r₃} := isClosed_le continuous_norm continuous_const
    exact h1.inter h2
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r₃)).subset ?_
  intro z hz
  simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2

/-- The exponential image of the closed vertical strip `log r₁ ≤ re w ≤ log r₃` is contained in
the closed annulus, for `0 < r₁ ≤ r₃`. -/
lemma exp_mem_closedAnnulus {r₁ r₃ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₃) {w : ℂ}
    (hw : w ∈ HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) :
    Complex.exp w ∈ closedAnnulus r₁ r₃ := by
  have hr₃ : 0 < r₃ := lt_of_lt_of_le hr₁ hr
  obtain ⟨hl, hu⟩ : Real.log r₁ ≤ w.re ∧ w.re ≤ Real.log r₃ := hw
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re := Complex.norm_exp w
  constructor
  · rw [hnorm, ← Real.exp_log hr₁]
    exact Real.exp_le_exp.mpr hl
  · rw [hnorm, ← Real.exp_log hr₃]
    exact Real.exp_le_exp.mpr hu

/-- **Hadamard's three-circles theorem.**  If `f` is analytic on a neighbourhood of the closed
annulus `r₁ ≤ ‖z‖ ≤ r₃`, is bounded by `a` on the inner circle and by `b` on the outer one, then
at every point `z` of the annulus

`‖f z‖ ≤ a ^ (1 − λ) * b ^ λ`,  where  `λ = (log ‖z‖ − log r₁)/(log r₃ − log r₁)`. -/
theorem norm_le_rpow_mul_rpow_of_annulus {f : ℂ → ℂ} {r₁ r₃ a b : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hf : AnalyticOnNhd ℂ f (closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (1 - (Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))
      * b ^ ((Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hr₃ : 0 < r₃ := hr₁.trans hr
  set l : ℝ := Real.log r₁ with hl
  set u : ℝ := Real.log r₃ with hu
  have hlu : l < u := Real.log_lt_log hr₁ hr
  set g : ℂ → ℂ := fun w => f (Complex.exp w) with hg
  -- `g` is analytic on the closed strip
  have hgan : AnalyticOnNhd ℂ g (HadamardThreeLines.verticalClosedStrip l u) := by
    intro w hw
    exact (hf _ (exp_mem_closedAnnulus hr₁ hr.le hw)).comp analyticAt_cexp
  -- hence `DiffContOnCl` on the open strip
  have hsub : HadamardThreeLines.verticalStrip l u
      ⊆ HadamardThreeLines.verticalClosedStrip l u := by
    intro w hw
    exact ⟨hw.1.le, hw.2.le⟩
  have hclosedStrip : IsClosed (HadamardThreeLines.verticalClosedStrip l u) := by
    have : HadamardThreeLines.verticalClosedStrip l u = Complex.re ⁻¹' (Icc l u) := rfl
    rw [this]
    exact isClosed_Icc.preimage Complex.continuous_re
  have hclosure : closure (HadamardThreeLines.verticalStrip l u)
      ⊆ HadamardThreeLines.verticalClosedStrip l u :=
    closure_minimal hsub hclosedStrip
  have hdiff : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip l u) := by
    refine ⟨?_, ?_⟩
    · exact fun w hw => ((hgan w (hsub hw)).differentiableAt).differentiableWithinAt
    · exact ((hgan.continuousOn).mono hclosure)
  -- and bounded on the closed strip, because the annulus is compact
  have hbdd : BddAbove (norm ∘ g '' HadamardThreeLines.verticalClosedStrip l u) := by
    have hcont : ContinuousOn (fun w : ℂ => ‖f w‖) (closedAnnulus r₁ r₃) :=
      (hf.continuousOn).norm
    obtain ⟨C, hC⟩ := (isCompact_closedAnnulus r₁ r₃).exists_bound_of_continuousOn hcont
    refine ⟨C, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    simpa using hC _ (exp_mem_closedAnnulus hr₁ hr.le hw)
  -- the boundary bounds
  have hbdl : ∀ w ∈ Complex.re ⁻¹' ({l} : Set ℝ), ‖g w‖ ≤ a := by
    intro w hw
    refine ha _ ?_
    have : w.re = l := hw
    rw [Complex.norm_exp, this, hl, Real.exp_log hr₁]
  have hbdu : ∀ w ∈ Complex.re ⁻¹' ({u} : Set ℝ), ‖g w‖ ≤ b := by
    intro w hw
    refine hb _ ?_
    have : w.re = u := hw
    rw [Complex.norm_exp, this, hu, Real.exp_log hr₃]
  -- apply the three-lines theorem at `w = log z`
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr₁ hz.1)
  set w : ℂ := Complex.log z with hw
  have hexp : Complex.exp w = z := Complex.exp_log hz0
  have hwre : w.re = Real.log ‖z‖ := Complex.log_re z
  have hwmem : w ∈ HadamardThreeLines.verticalClosedStrip l u := by
    refine ⟨?_, ?_⟩
    · rw [hwre, hl]
      exact Real.log_le_log hr₁ hz.1
    · rw [hwre, hu]
      exact Real.log_le_log (lt_of_lt_of_le hr₁ hz.1) hz.2
  have hmain := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := g) (z := w) (a := a) (b := b) hlu hwmem hdiff hbdd hbdl hbdu
  have hmain' : ‖f (Complex.exp w)‖
      ≤ a ^ (1 - (w.re - l) / (u - l)) * b ^ ((w.re - l) / (u - l)) := hmain
  rwa [hexp, hwre] at hmain'

/-- **Hadamard's three-circles theorem**, in the classical form: with `M(r)` denoting an upper
bound for `‖f‖` on the circle of radius `r`, the bound at radius `‖z‖` interpolates
logarithmically between the two. -/
theorem three_circles {f : ℂ → ℂ} {r₁ r₃ a b : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hf : AnalyticOnNhd ℂ f (closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (Real.log (r₃ / ‖z‖) / Real.log (r₃ / r₁))
      * b ^ (Real.log (‖z‖ / r₁) / Real.log (r₃ / r₁)) := by
  have hr₃ : 0 < r₃ := hr₁.trans hr
  have hz1 : 0 < ‖z‖ := lt_of_lt_of_le hr₁ hz.1
  have hden : Real.log r₃ - Real.log r₁ = Real.log (r₃ / r₁) := (Real.log_div hr₃.ne' hr₁.ne').symm
  have hdenpos : 0 < Real.log (r₃ / r₁) := by
    rw [← hden]
    have := Real.log_lt_log hr₁ hr
    linarith
  have h1 : Real.log ‖z‖ - Real.log r₁ = Real.log (‖z‖ / r₁) :=
    (Real.log_div hz1.ne' hr₁.ne').symm
  have h2 : 1 - Real.log (‖z‖ / r₁) / Real.log (r₃ / r₁)
      = Real.log (r₃ / ‖z‖) / Real.log (r₃ / r₁) := by
    field_simp
    rw [Real.log_div hr₃.ne' hr₁.ne', Real.log_div hz1.ne' hr₁.ne',
      Real.log_div hr₃.ne' hz1.ne']
    ring
  have := norm_le_rpow_mul_rpow_of_annulus hr₁ hr hf ha hb hz
  rwa [hden, h1, h2] at this

end RiemannHypothesis
