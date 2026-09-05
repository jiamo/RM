/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.JensenDiscCount

/-!
# Counting zeroes in a disc of *arbitrary* radius ratio

`RiemannHypothesis.ZeroCountingLemma` counts the zeroes of a holomorphic function in the disc of
radius `R / 4` against the maximum of `‖f‖` on the circle of radius `R`; the ratio `4` is built
into the proof.  For Backlund's estimate the ratio matters: the zeroes of the real part of `ζ` on
a horizontal segment of length `5/2` starting at the abscissa `3` have to be counted against a
circle that stays inside the half-plane `re s > 0`, which forces a ratio close to `1`.

Jensen's counting inequality `card_mul_log_le_circleAverage_sub_log` already allows arbitrary
radii; this file records its maximum-modulus form, in which the circle average of `log ‖f‖` is
replaced by the logarithm of a bound for `‖f‖` on the circle.

## Main results

* `card_mul_log_le_log_of_sphere_le` : `|S| · log (R / r) ≤ log M − log ‖f c‖` for a finite set
  `S` of zeroes of `f` in the closed ball of radius `r < R`, where `‖f‖ ≤ M` on the circle of
  radius `R` and `1 ≤ M`.
* `finite_setOf_zeros_radii`, `ncard_setOf_zeros_le_radii` : consequently the whole zero set of
  `f` in the ball of radius `r` is finite, with at most `(log M − log ‖f c‖) / log (R / r)`
  elements.
-/

open Complex Metric Real

namespace RiemannHypothesis

/-- **Jensen's counting inequality in maximum-modulus form.**  If `f` is analytic on a
neighbourhood of the closed ball `B(c, R)`, does not vanish at the centre, satisfies `‖f‖ ≤ M` on
the circle of radius `R` with `1 ≤ M`, and `S` is a finite set of zeroes of `f` in the concentric
closed ball of radius `r < R`, then `|S| · log (R / r) ≤ log M − log ‖f c‖`. -/
theorem card_mul_log_le_log_of_sphere_le
    {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hM1 : 1 ≤ M) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, dist ρ c ≤ r ∧ f ρ = 0) :
    (S.card : ℝ) * Real.log (R / r) ≤ Real.log M - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have habs : |R| = R := abs_of_pos hR
  have hsphere_sub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hmero : MeromorphicOn f (sphere c |R|) := by
    rw [habs]; exact (hf.mono hsphere_sub).meromorphicOn
  have hint : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    MeromorphicOn.circleIntegrable_log_norm hmero
  have havg : circleAverage (fun z => Real.log ‖f z‖) c R ≤ Real.log M := by
    refine circleAverage_mono_on_of_le_circle hint ?_
    intro z hz
    rw [habs] at hz
    rcases eq_or_lt_of_le (norm_nonneg (f z)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hM1
    · exact Real.log_le_log h0 (hM z hz)
  have hjensen := card_mul_log_le_circleAverage_sub_log hr hrR hf hc hS
  linarith

/-- The zero set of `f` in the closed ball of radius `r < R` is finite. -/
theorem finite_setOf_zeros_radii {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hM1 : 1 ≤ M) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    {z : ℂ | dist z c ≤ r ∧ f z = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hlog : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  set B : ℝ := (Real.log M - Real.log ‖f c‖) / Real.log (R / r) with hB
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq (⌈B⌉₊ + 1)
  have h1 : ((⌈B⌉₊ + 1 : ℕ) : ℝ) * Real.log (R / r) ≤ Real.log M - Real.log ‖f c‖ := by
    have := card_mul_log_le_log_of_sphere_le hr hrR hf hc hM1 hM (S := S) fun a ha => hSsub ha
    rwa [hScard] at this
  have h2 : ((⌈B⌉₊ + 1 : ℕ) : ℝ) ≤ B := by
    rw [hB, le_div_iff₀ hlog]; exact h1
  have h3 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  push_cast at h2
  linarith

/-- **The counting bound for the whole zero set** in the closed ball of radius `r < R`. -/
theorem ncard_setOf_zeros_le_radii {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hM1 : 1 ≤ M) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ({z : ℂ | dist z c ≤ r ∧ f z = 0}.ncard : ℝ) * Real.log (R / r)
      ≤ Real.log M - Real.log ‖f c‖ := by
  have hfin := finite_setOf_zeros_radii hr hrR hf hc hM1 hM
  have h := card_mul_log_le_log_of_sphere_le hr hrR hf hc hM1 hM
    (S := hfin.toFinset) fun a ha => by simpa using hfin.mem_toFinset.mp ha
  rwa [Set.ncard_eq_toFinset_card _ hfin]

end RiemannHypothesis
