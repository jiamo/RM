/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroCountingLemma
import Mathlib.Analysis.Analytic.Order

/-!
# A Jensen-type bound for the zeroes of a holomorphic function *with multiplicity*

`RiemannHypothesis.ZeroCountingLemma` bounds the *number* of zeroes of a holomorphic function in a
small disc.  This file bounds the total *order of vanishing*: a holomorphic function cannot vanish
to high total order in a small disc unless it is much larger somewhere on a large circle around it.

## Main results

* `exists_divided` : if `f` vanishes to order at least `m` at a point `a` of the ball `B(c, R)`,
  then `f / (· - a) ^ m` extends to a function holomorphic on `B(c, R)` and continuous on its
  closure.

* `pow_three_pow_mul_norm_le` : if `f` is holomorphic on `B(c, R)` and continuous on its closure,
  if `‖f z‖ ≤ M` on the circle `‖z - c‖ = R`, and if `f` vanishes to order at least `m` at a point
  `a` of the concentric ball of radius `R / 4`, then `3 ^ m * ‖f c‖ ≤ M`.

* `pow_three_sum_mul_norm_le` : the same with a *finite set* of zeroes, counted with multiplicity:
  `3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M`.

* `analyticOrder_le_log_div_log_three`, `sum_analyticOrder_le_log_div_log_three` : the logarithmic
  forms, bounding the (total) order by `log (M / ‖f c‖) / log 3`.

The proof divides the zeroes out one point at a time, each with its full multiplicity: the
hypothesis on the order gives a local factorization `f = (· - a) ^ m • g`, so `G = f / (· - a) ^ m`
extends holomorphically across `a`; on the circle `‖G‖ ≤ M / (3R/4) ^ m` by the maximum principle,
while `‖G c‖ = ‖f c‖ / ‖c - a‖ ^ m ≥ ‖f c‖ / (R/4) ^ m`.  Each point therefore improves the ratio
`M / ‖f c‖` by a factor `3 ^ m`.  No use is made of Jensen's formula.
-/

open Complex Metric Set

namespace RiemannHypothesis

/-- **Dividing out a zero with its multiplicity.**  If `f` is holomorphic on `B(c, R)`, continuous
on the closed ball, and vanishes to order at least `m` at a point `a` of the ball, then
`f / (· - a) ^ m` extends to a function with the same regularity. -/
theorem exists_divided {f : ℂ → ℂ} {c a : ℂ} {R : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (ha : a ∈ ball c R)
    (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G (ball c R) ∧ ∀ z, z ≠ a → G z = f z / (z - a) ^ m := by
  have hfa : AnalyticAt ℂ f a := (hf.differentiableOn.analyticOnNhd isOpen_ball) a ha
  obtain ⟨g, hg, hgeq⟩ := (natCast_le_analyticOrderAt hfa).mp hord
  set G : ℂ → ℂ := Function.update (fun z => f z / (z - a) ^ m) a (g a) with hG
  have hGne : ∀ z, z ≠ a → G z = f z / (z - a) ^ m := by
    intro z hz; rw [hG, Function.update_of_ne hz]
  have hGa : G a = g a := by rw [hG, Function.update_self]
  -- near `a`, `G` agrees with the analytic function `g`
  have hGg : G =ᶠ[nhds a] g := by
    filter_upwards [hgeq] with z hz
    rcases eq_or_ne z a with rfl | hza
    · exact hGa
    · rw [hGne z hza, hz, smul_eq_mul, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero _ (sub_ne_zero.mpr hza)), mul_one]
  -- `G` is holomorphic on the ball
  have hGdiff : DifferentiableOn ℂ G (ball c R) := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact (hg.differentiableAt.congr_of_eventuallyEq hGg).differentiableWithinAt
    · have hfz : DifferentiableAt ℂ f z :=
        hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)
      have hden : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ m) z := by fun_prop
      have hdiv : DifferentiableAt ℂ (fun w : ℂ => f w / (w - a) ^ m) z :=
        hfz.div hden (pow_ne_zero _ (sub_ne_zero.mpr hza))
      have hev : G =ᶠ[nhds z] fun w : ℂ => f w / (w - a) ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hza] with w hw using hGne w hw
      exact (hdiv.congr_of_eventuallyEq hev).differentiableWithinAt
  -- `G` is continuous on the closed ball
  have hGcont : ContinuousOn G (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · have hda := hGdiff.differentiableAt (isOpen_ball.mem_nhds ha)
      exact hda.continuousAt.continuousWithinAt
    · have hfz : ContinuousWithinAt f (closedBall c R) z :=
        (hf.continuousOn.mono (by rw [closure_ball c hR.ne'])) z hz
      have h1 : ContinuousWithinAt (fun w : ℂ => f w / (w - a) ^ m) (closedBall c R) z :=
        hfz.div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hza))
      have hev : G =ᶠ[nhds z] fun w : ℂ => f w / (w - a) ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hza] with w hw using hGne w hw
      exact h1.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) (hGne z hza)
  exact ⟨G, ⟨hGdiff, hGcont⟩, hGne⟩

/-- **Bounding the total order of the zeroes in a disc.**  If `f` is holomorphic on `B(c, R)`,
continuous on the closed ball, bounded by `M` on the boundary circle, and vanishes to order at
least `m a` at each point `a` of a finite set `S` inside the concentric ball of radius `R / 4`,
then `3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M`. -/
theorem pow_three_sum_mul_norm_le {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ) :
    ∀ (f : ℂ → ℂ) (M : ℝ) (m : ℂ → ℕ), DiffContOnCl ℂ f (ball c R) →
      (∀ z ∈ sphere c R, ‖f z‖ ≤ M) → (∀ a ∈ S, dist a c ≤ R / 4) →
      (∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt f a) →
      3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M := by
  classical
  induction S using Finset.induction with
  | empty =>
      intro f M _ hf hM _ _
      have : ‖f c‖ ≤ M := by
        refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf ?_ ?_
        · rw [frontier_ball c hR.ne']; exact hM
        · rw [closure_ball c hR.ne']; simp [hR.le]
      simpa using this
  | insert a S haS ih =>
      intro f M m hf hM hdist hord
      have hM0 : 0 ≤ M :=
        le_trans (norm_nonneg _) (hM (c + R) (by simp [Complex.norm_real, abs_of_pos hR]))
      have hsum : ∑ b ∈ insert a S, m b = m a + ∑ b ∈ S, m b :=
        Finset.sum_insert haS
      have hac : dist a c ≤ R / 4 := hdist a (Finset.mem_insert_self a S)
      have haball : a ∈ ball c R := by rw [mem_ball]; linarith [hac]
      rcases eq_or_ne (f c) 0 with hfc | hfc
      · simp [hfc, hM0]
      rcases Nat.eq_zero_or_pos (m a) with hma | hma
      · -- nothing to divide out at `a`
        have := ih f M m hf hM (fun b hb => hdist b (Finset.mem_insert_of_mem hb))
          (fun b hb => hord b (Finset.mem_insert_of_mem hb))
        rw [hsum, hma, zero_add]
        exact this
      -- `f` vanishes at `a`, so `c ≠ a`
      have hone : (1 : ℕ∞) ≤ analyticOrderAt f a :=
        le_trans (by exact_mod_cast hma) (hord a (Finset.mem_insert_self a S))
      have hfa0 : f a = 0 := by
        refine apply_eq_zero_of_analyticOrderAt_ne_zero (𝕜 := ℂ) ?_
        intro h
        rw [h] at hone
        simp at hone
      have hca : c ≠ a := by
        intro h; rw [h] at hfc; exact hfc hfa0
      obtain ⟨G, hG, hGne⟩ :=
        exists_divided hR hf haball (hord a (Finset.mem_insert_self a S))
      -- the bound for `G` on the boundary circle
      have hRa : ∀ z ∈ sphere c R, 3 * R / 4 ≤ ‖z - a‖ := by
        intro z hz
        have h1 : ‖z - c‖ = R := by simpa [Complex.dist_eq] using hz
        have h2 : ‖a - c‖ ≤ R / 4 := by simpa [Complex.dist_eq] using hac
        have h3 : ‖z - c‖ - ‖a - c‖ ≤ ‖z - a‖ := by
          have := norm_sub_norm_le (z - c) (a - c); simpa using this
        linarith
      have hRpos : (0 : ℝ) < 3 * R / 4 := by linarith
      have hGsphere : ∀ z ∈ sphere c R, ‖G z‖ ≤ M / (3 * R / 4) ^ m a := by
        intro z hz
        have hza : z ≠ a := by
          intro h
          have h1 : ‖z - c‖ = R := by simpa [Complex.dist_eq] using hz
          have h2 : ‖a - c‖ ≤ R / 4 := by simpa [Complex.dist_eq] using hac
          rw [h] at h1; linarith
        rw [hGne z hza, norm_div, norm_pow]
        have hden : (0 : ℝ) < ‖z - a‖ ^ (m a) := by
          have : (0 : ℝ) < ‖z - a‖ := lt_of_lt_of_le hRpos (hRa z hz)
          positivity
        rw [div_le_div_iff₀ hden (by positivity)]
        have hpow : (3 * R / 4) ^ m a ≤ ‖z - a‖ ^ m a :=
          pow_le_pow_left₀ hRpos.le (hRa z hz) _
        nlinarith [hM z hz, norm_nonneg (f z), pow_pos hRpos (m a)]
      -- the orders at the remaining points are unchanged
      have hGord : ∀ b ∈ S, (m b : ℕ∞) ≤ analyticOrderAt G b := by
        intro b hb
        have hba : b ≠ a := fun h => haS (h ▸ hb)
        have hbball : b ∈ ball c R := by
          rw [mem_ball]; linarith [hdist b (Finset.mem_insert_of_mem hb)]
        have hGb : AnalyticAt ℂ G b := (hG.differentiableOn.analyticOnNhd isOpen_ball) b hbball
        have hmon : AnalyticAt ℂ (fun z : ℂ => (z - a) ^ m a) b :=
          DifferentiableOn.analyticAt (s := Set.univ)
            (by fun_prop : Differentiable ℂ fun z : ℂ => (z - a) ^ m a).differentiableOn
            Filter.univ_mem
        have hev : f =ᶠ[nhds b] (fun z : ℂ => (z - a) ^ m a) * G := by
          filter_upwards [isOpen_ne.mem_nhds hba] with z hz
          have hzne : (z - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
          simp only [Pi.mul_apply, hGne z hz]
          rw [mul_comm, div_mul_cancel₀ _ hzne]
        have hmon0 : analyticOrderAt (fun z : ℂ => (z - a) ^ m a) b = 0 := by
          refine hmon.analyticOrderAt_eq_zero.2 ?_
          exact pow_ne_zero _ (sub_ne_zero.mpr hba)
        have hforder : analyticOrderAt f b = analyticOrderAt G b := by
          rw [analyticOrderAt_congr hev, analyticOrderAt_mul hmon hGb, hmon0, zero_add]
        rw [← hforder]
        exact hord b (Finset.mem_insert_of_mem hb)
      have hIH := ih G (M / (3 * R / 4) ^ m a) m hG hGsphere
        (fun b hb => hdist b (Finset.mem_insert_of_mem hb)) hGord
      -- compare the values at the centre
      have hcanorm : ‖c - a‖ ≤ R / 4 := by rw [← Complex.dist_eq, dist_comm]; exact hac
      have hcapos : 0 < ‖c - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hca)
      have hGcval : ‖G c‖ = ‖f c‖ / ‖c - a‖ ^ m a := by
        rw [hGne c hca, norm_div, norm_pow]
      have hR4 : (0 : ℝ) < R / 4 := by linarith
      have hpow4 : ‖c - a‖ ^ m a ≤ (R / 4) ^ m a := pow_le_pow_left₀ hcapos.le hcanorm _
      have hle : ‖f c‖ / (R / 4) ^ m a ≤ ‖G c‖ := by
        rw [hGcval, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [norm_nonneg (f c), hpow4, pow_pos hcapos (m a)]
      have hkey : 3 ^ (∑ b ∈ S, m b) * (‖f c‖ / (R / 4) ^ m a) ≤ M / (3 * R / 4) ^ m a := by
        refine le_trans ?_ hIH
        have h3 : (0 : ℝ) < 3 ^ (∑ b ∈ S, m b) := by positivity
        nlinarith
      have hsplit : (3 * R / 4 : ℝ) ^ m a = 3 ^ m a * (R / 4) ^ m a := by
        rw [← mul_pow]; ring_nf
      have hD : (0 : ℝ) < (R / 4) ^ m a := by positivity
      have hL : 3 ^ (∑ b ∈ S, m b) * (‖f c‖ / (R / 4) ^ m a)
          = (3 ^ (∑ b ∈ S, m b) * ‖f c‖) / (R / 4) ^ m a := by ring
      rw [hsplit, hL, div_le_div_iff₀ hD (by positivity)] at hkey
      rw [hsum, pow_add]
      nlinarith [hkey, hD]

/-- **Bounding the order of a single zero in a disc**: the case `S = {a}` of
`pow_three_sum_mul_norm_le`. -/
theorem pow_three_pow_mul_norm_le {f : ℂ → ℂ} {c a : ℂ} {R M : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (ha : dist a c ≤ R / 4) (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    3 ^ m * ‖f c‖ ≤ M := by
  classical
  have h := pow_three_sum_mul_norm_le hR {a} f M (fun _ => m) hf hM
    (by simpa using ha) (by simpa using hord)
  simpa using h

/-- Logarithmic form of `pow_three_pow_mul_norm_le`: the order of vanishing of `f` at a point of
the ball of radius `R / 4` is at most `log (M / ‖f c‖) / log 3`. -/
theorem analyticOrder_le_log_div_log_three {f : ℂ → ℂ} {c a : ℂ} {R M : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hc : f c ≠ 0)
    (ha : dist a c ≤ R / 4) (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    (m : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 := by
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have hkey := pow_three_pow_mul_norm_le hR hf hM ha hord
  have h1 : (3 : ℝ) ^ m ≤ M / ‖f c‖ := by
    rw [le_div_iff₀ hfc]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog3]
  have h2 : Real.log ((3 : ℝ) ^ m) ≤ Real.log (M / ‖f c‖) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  linarith

/-- Logarithmic form of `pow_three_sum_mul_norm_le`: the total order of vanishing of `f` on a
finite set of points of the ball of radius `R / 4` is at most `log (M / ‖f c‖) / log 3`. -/
theorem sum_analyticOrder_le_log_div_log_three {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (hc : f c ≠ 0) (S : Finset ℂ) (hdist : ∀ a ∈ S, dist a c ≤ R / 4)
    (hord : ∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt f a) :
    ((∑ a ∈ S, m a : ℕ) : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 := by
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have hkey := pow_three_sum_mul_norm_le hR S f M m hf hM hdist hord
  have h1 : (3 : ℝ) ^ (∑ a ∈ S, m a) ≤ M / ‖f c‖ := by
    rw [le_div_iff₀ hfc]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog3]
  have h2 : Real.log ((3 : ℝ) ^ (∑ a ∈ S, m a)) ≤ Real.log (M / ‖f c‖) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  linarith

end RiemannHypothesis
