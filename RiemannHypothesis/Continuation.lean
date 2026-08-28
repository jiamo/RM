/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EulerMaclaurin
import RiemannHypothesis.Connected
import RiemannHypothesis.Eta

/-!
# The Euler–Maclaurin representation, continued to the right half-plane

`RiemannHypothesis.EulerMaclaurin` proves the first-order Euler–Maclaurin representation
`ζ(s) = zetaApprox N s` on the half-plane of absolute convergence `1 < re s`.  The
right-hand side, however, converges and is analytic on the whole punctured right half-plane
`{s | 0 < re s} \ {1}`.  This file upgrades the identity to that domain by the identity
theorem, exactly as `RiemannHypothesis.Eta` does for `η = (1 - 2^(1-s)) ζ`.

## Main results

* `differentiableOn_tsum_eulerTerm` : the Euler–Maclaurin tail is analytic on
  `{s | 0 < re s} \ {1}`;
* `riemannZeta_eq_zetaApprox_of_pos_re` : `ζ(s) = zetaApprox N s` for `0 < re s`, `s ≠ 1`
  and every `N`.
-/

noncomputable section

open Complex Filter Finset Set

namespace RiemannHypothesis

/-- Each Euler–Maclaurin term is differentiable away from `s = 1`. -/
lemma differentiableAt_eulerTerm (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (eulerTerm n) s := by
  have h1 : ((n + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h2 : ((n + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold eulerTerm
  fun_prop (disch := first | assumption | exact Or.inl h1 | exact Or.inl h2)

/-- The Euler–Maclaurin tail `∑' n, eulerTerm (n + N) s` is differentiable on the punctured
right half-plane. -/
lemma differentiableOn_tsum_eulerTerm (N : ℕ) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, eulerTerm (n + N) s)
      ({s : ℂ | 0 < s.re} \ {1}) := by
  intro s hs
  obtain ⟨hs0, hs1'⟩ := hs
  have hsr : 0 < s.re := hs0
  have hs1 : s ≠ 1 := by simpa using hs1'
  -- a small ball around `s` staying in the half-plane and avoiding `1`
  set δ : ℝ := min (s.re / 2) (‖s - 1‖ / 2) with hδdef
  have hnorm1 : 0 < ‖s - 1‖ := by
    simpa [norm_pos_iff, sub_eq_zero] using hs1
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδre : δ ≤ s.re / 2 := min_le_left _ _
  have hδ1 : δ ≤ ‖s - 1‖ / 2 := min_le_right _ _
  set U : Set ℂ := {z : ℂ | ‖z - s‖ < δ} with hU
  have hU_open : IsOpen U := by
    simpa [hU, Metric.ball, dist_eq] using (Metric.isOpen_ball (x := s) (ε := δ))
  have hU_self : s ∈ U := by simp [hU, hδ]
  have hU_re : ∀ z ∈ U, δ ≤ z.re := by
    intro z hz
    have hzn : ‖z - s‖ < δ := hz
    have h1 : s.re - z.re ≤ ‖z - s‖ := by
      have h := Complex.abs_re_le_norm (s - z)
      rw [Complex.sub_re] at h
      rw [norm_sub_rev] at h
      exact le_trans (le_abs_self _) h
    linarith
  have hU_ne : ∀ z ∈ U, z ≠ 1 := by
    intro z hz hz1
    have hzn : ‖z - s‖ < δ := hz
    rw [hz1, norm_sub_rev] at hzn
    linarith
  set M : ℝ := ‖s‖ + δ with hM
  have hMnn : 0 ≤ M := by positivity
  have hUM : ∀ z ∈ U, ‖z‖ ≤ M := by
    intro z hz
    have hzn : ‖z - s‖ < δ := hz
    calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
      _ ≤ M := by rw [hM]; linarith
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, eulerTerm (n + N) s) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => M * ((n : ℝ) + 1) ^ (-(1 + δ)))
      ?_ (fun n => fun z hz =>
        (differentiableAt_eulerTerm (n + N) (hU_ne z hz)).differentiableWithinAt) hU_open ?_
    · exact (summable_natAddOne_rpow_neg (by linarith)).mul_left M
    · intro n z hz
      have hzre : δ ≤ z.re := hU_re z hz
      have hz0 : 0 ≤ z.re := le_trans hδ.le hzre
      refine (norm_eulerTerm_le (n + N) hz0 (hU_ne z hz)).trans ?_
      have hbase : (1 : ℝ) ≤ ((n : ℝ) + 1) := by simp
      have hbase' : (1 : ℝ) ≤ (((n + N : ℕ) : ℝ) + 1) := by
        have : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      calc ‖z‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + z.re))
          ≤ M * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + z.re)) :=
            mul_le_mul_of_nonneg_right (hUM z hz) (Real.rpow_nonneg (by linarith) _)
        _ ≤ M * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + δ)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hbase' (by linarith)) hMnn
        _ ≤ M * ((n : ℝ) + 1) ^ (-(1 + δ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
            have : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
              exact_mod_cast Nat.le_add_right n N
            linarith
  exact (hdiff.differentiableAt (hU_open.mem_nhds hU_self)).differentiableWithinAt

/-- `zetaApprox N` is analytic on the punctured right half-plane. -/
lemma analyticOnNhd_zetaApprox (N : ℕ) :
    AnalyticOnNhd ℂ (zetaApprox N) ({s : ℂ | 0 < s.re} \ {1}) := by
  have hopen : IsOpen ({s : ℂ | 0 < s.re} \ {1}) :=
    (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro s hs
  have hs1 : s ≠ 1 := by simpa using hs.2
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hbase : ∀ m : ℕ, (((m : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := fun m =>
    Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : DifferentiableOn ℂ
      (fun s : ℂ => ∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
      ({s : ℂ | 0 < s.re} \ {1}) := by
    intro z _
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun n _ => ?_
    fun_prop (disch := first | assumption | exact Or.inl (hbase n))
  have h2 : DifferentiableOn ℂ (fun s : ℂ => ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1))
      ({s : ℂ | 0 < s.re} \ {1}) := by
    intro z hz
    have hz1 : z ≠ 1 := by simpa using hz.2
    have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hb : (((N : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := hbase N
    refine DifferentiableAt.differentiableWithinAt ?_
    have hb' : (((N : ℕ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb
    fun_prop (disch := first | assumption | exact Or.inl hb')
  have h3 := differentiableOn_tsum_eulerTerm N
  have := (h1.add h2).add h3
  exact this.congr (fun z _ => rfl) s hs

/-- **The Euler–Maclaurin representation of `ζ` on the punctured right half-plane.**
Both sides are analytic on `{s | 0 < re s} \ {1}` and agree on `{s | 1 < re s}`, so the
identity theorem extends the identity of
`RiemannHypothesis.riemannZeta_eq_zetaApprox` to the whole punctured half-plane. -/
theorem riemannZeta_eq_zetaApprox_of_pos_re (N : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaApprox N s := by
  have hU : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := isPreconnected_punctured_halfPlane
  have hz₀ : (2 : ℂ) ∈ ({s : ℂ | 0 < s.re} \ {1}) := by simp
  have hfg : riemannZeta =ᶠ[nhds (2 : ℂ)] zetaApprox N := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact riemannZeta_eq_zetaApprox N hz
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_riemannZeta (analyticOnNhd_zetaApprox N) hU hz₀ hfg
  exact heq ⟨hs0, hs1⟩

end RiemannHypothesis

end
