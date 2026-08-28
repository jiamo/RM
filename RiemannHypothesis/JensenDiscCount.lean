/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Counting zeroes in a disc by the circle *average* of `log ‖f‖`

`RiemannHypothesis.ZeroCountingLemma` counts the zeroes of a holomorphic function in a disc
against the *maximum* of `‖f‖` on a larger circle.  That is enough for Riemann–von Mangoldt type
upper bounds, but it is too lossy for a zero-density theorem: the maximum of `‖ζ‖` on a circle
inside the critical strip is a power of the height, so the maximum costs a factor `log T` per
disc, and summing over `≍ T` discs only reproduces the trivial bound `O(T log T)`.

Jensen's *formula* (`MeromorphicOn.circleAverage_log_norm` in Mathlib) replaces the maximum by the
average of `log ‖f‖` over the circle, and the average of `log ‖ζ‖` over a family of circles is
controlled — after integrating in the vertical direction — by the mean square of `ζ` on vertical
lines.  This file records the counting form of Jensen's formula that the Bohr–Landau density
theorem in `RiemannHypothesis.BohrLandau` uses.

## Main result

* `card_mul_log_le_circleAverage_sub_log` : if `f` is analytic on a neighbourhood of the closed
  ball `B(c, R)`, if `f c ≠ 0`, and if `S` is a finite set of zeroes of `f` in the concentric
  closed ball of radius `r < R`, then

  `|S| · log (R / r) ≤ circleAverage (log ‖f ·‖) c R − log ‖f c‖`.

Zeroes are counted without multiplicity (`S` is a set of points); multiplicities only help.
-/

open Complex Metric Real MeromorphicOn

namespace RiemannHypothesis

/-- A zero of `f` inside the open ball has positive divisor, provided `f` is analytic on a
neighbourhood of the closed ball and does not vanish at the centre. -/
theorem one_le_divisor_of_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) {ρ : ℂ} (hρ : ρ ∈ ball c R)
    (hfρ : f ρ = 0) : 1 ≤ divisor f (closedBall c R) ρ := by
  have hballsub : ball c R ⊆ closedBall c R := ball_subset_closedBall
  have hfb : AnalyticOnNhd ℂ f (ball c R) := hf.mono hballsub
  have hmem : ρ ∈ closedBall c R := hballsub hρ
  have hcmem : c ∈ ball c R := mem_ball_self hR
  have hnottop : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev : ∀ᶠ z in nhds ρ, f z = 0 := analyticOrderAt_eq_top.mp htop
    have := hfb.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hρ
      (by filter_upwards [hev] with z hz using hz)
    exact hc (this hcmem)
  have hne : analyticOrderAt f ρ ≠ 0 := by
    rw [Ne, (hfb ρ hρ).analyticOrderAt_eq_zero]
    simpa using hfρ
  have hdiv : divisor f (closedBall c R) ρ = (meromorphicOrderAt f ρ).untop₀ :=
    divisor_apply hf.meromorphicOn hmem
  rw [hdiv, (hf ρ hmem).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f ρ = (n : ℕ∞) := by
    lift analyticOrderAt f ρ to ℕ using hnottop with n hn
    exact ⟨n, rfl⟩
  rw [hn] at hne ⊢
  have hn0 : n ≠ 0 := by simpa using hne
  simp only [ENat.map_coe]
  have hcast : ((n : ℤ) : WithTop ℤ).untop₀ = (n : ℤ) := by simp
  rw [hcast]
  omega

/-- **Jensen's counting inequality.**  If `f` is analytic on a neighbourhood of the closed ball
`B(c, R)`, does not vanish at the centre, and `S` is a finite set of zeroes of `f` inside the
concentric closed ball of radius `r < R`, then

`|S| · log (R / r) ≤ circleAverage (log ‖f ·‖) c R − log ‖f c‖`. -/
theorem card_mul_log_le_circleAverage_sub_log
    {f : ℂ → ℂ} {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, dist ρ c ≤ r ∧ f ρ = 0) :
    (S.card : ℝ) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  classical
  have hR : 0 < R := hr.trans hrR
  have habs : |R| = R := abs_of_pos hR
  have hmero : MeromorphicOn f (closedBall c |R|) := by rw [habs]; exact hf.meromorphicOn
  have hjensen := MeromorphicOn.circleAverage_log_norm hR.ne' hmero
  rw [habs] at hjensen
  set D := divisor f (closedBall c R) with hD
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hDc : D c = 0 := by
    rw [hD, divisor_apply hf.meromorphicOn hcmem, (hf c hcmem).meromorphicOrderAt_eq,
      ((hf c hcmem).analyticOrderAt_eq_zero).2 hc]
    simp
  have htc : meromorphicTrailingCoeffAt f c = f c :=
    (hf c hcmem).meromorphicTrailingCoeffAt_of_ne_zero hc
  rw [hDc, htc] at hjensen
  simp only [Int.cast_zero, zero_mul, add_zero] at hjensen
  rw [hjensen]
  -- it remains to bound the divisor sum from below
  set g : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) * Real.log (R * ‖c - u‖⁻¹) with hg
  have hDnonneg : ∀ u, 0 ≤ D u := fun u => hf.divisor_nonneg u
  have hlognn : ∀ u ∈ closedBall c R, 0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    rcases eq_or_ne u c with rfl | hne
    · simp
    · have h0 : 0 < ‖c - u‖ := by
        simpa [sub_eq_zero] using (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne)))
      have hle : ‖c - u‖ ≤ R := by
        have := mem_closedBall.1 hu
        rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
      have h1 : 1 ≤ R * ‖c - u‖⁻¹ := by
        rw [le_mul_inv_iff₀ h0]; linarith
      exact Real.log_nonneg h1
  have hgnonneg : ∀ u, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ closedBall c R
    · exact mul_nonneg (by exact_mod_cast hDnonneg u) (hlognn u hu)
    · have hzero : D u = 0 := by rw [hD]; simp [hu]
      simp [hg, hzero]
  have hsuppfin : (Function.support g).Finite := by
    refine Set.Finite.subset (D.finiteSupport (isCompact_closedBall c R)) ?_
    intro u hu
    simp only [hg, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    exact fun h => hu.1 (by exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h)
  -- each zero in `S` contributes at least `log (R / r)`
  have hSg : ∀ ρ ∈ S, Real.log (R / r) ≤ g ρ := by
    intro ρ hρS
    obtain ⟨hdist, hfρ⟩ := hS ρ hρS
    have hρball : ρ ∈ ball c R := by
      rw [mem_ball]; exact lt_of_le_of_lt hdist hrR
    have hne : ρ ≠ c := by
      intro h
      rw [h] at hfρ; exact hc hfρ
    have h0 : 0 < ‖c - ρ‖ := by
      simpa [sub_eq_zero] using (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne)))
    have hler : ‖c - ρ‖ ≤ r := by
      have := hdist
      rw [dist_eq_norm] at this
      rwa [← norm_neg, neg_sub] at this
    have hlog : Real.log (R / r) ≤ Real.log (R * ‖c - ρ‖⁻¹) := by
      have hstep : R / r ≤ R * ‖c - ρ‖⁻¹ := by
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hR.le h0 hler
      exact Real.log_le_log (by positivity) hstep
    have hone : (1 : ℝ) ≤ ((D ρ : ℤ) : ℝ) := by
      have := one_le_divisor_of_zero hR hf hc hρball hfρ
      exact_mod_cast this
    have hlog0 : 0 ≤ Real.log (R / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    calc Real.log (R / r) = 1 * Real.log (R / r) := (one_mul _).symm
      _ ≤ ((D ρ : ℤ) : ℝ) * Real.log (R * ‖c - ρ‖⁻¹) := by
          exact mul_le_mul hone hlog hlog0 (by linarith)
      _ = g ρ := rfl
  -- sum up
  set F : Finset ℂ := hsuppfin.toFinset ∪ S with hF
  have hsub : Function.support g ⊆ (F : Set ℂ) := by
    intro u hu
    simp only [hF, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]
    exact Or.inl hu
  have hfinsum : ∑ᶠ u, g u = ∑ u ∈ F, g u := finsum_eq_sum_of_support_subset g hsub
  have h1 : ∑ ρ ∈ S, g ρ ≤ ∑ u ∈ F, g u :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun i _ _ => hgnonneg i
  have h2 : (S.card : ℝ) * Real.log (R / r) ≤ ∑ ρ ∈ S, g ρ := by
    calc (S.card : ℝ) * Real.log (R / r) = ∑ _ρ ∈ S, Real.log (R / r) := by simp
      _ ≤ ∑ ρ ∈ S, g ρ := Finset.sum_le_sum hSg
  have : (S.card : ℝ) * Real.log (R / r) ≤ ∑ᶠ u, g u := by rw [hfinsum]; linarith
  simpa [hg] using this

end RiemannHypothesis
