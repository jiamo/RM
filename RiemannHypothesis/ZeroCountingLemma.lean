/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A Jensen-type bound for the number of zeroes of a holomorphic function in a disc

This file proves the classical counting estimate that underlies every zero-density theorem for
the Riemann zeta function: *a holomorphic function cannot have many zeroes in a small disc unless
it is much larger somewhere on a large circle around it.*

## Main results

* `pow_three_card_mul_norm_le` : if `f` is holomorphic on the open ball `B(c, R)` and continuous
  on its closure, if `‖f z‖ ≤ M` on the circle `‖z - c‖ = R`, and if `S` is a finite set of zeroes
  of `f` inside the concentric ball of radius `R / 4`, then `3 ^ |S| * ‖f c‖ ≤ M`.

* `card_le_log_div_log_three` : the same statement in logarithmic form,
  `|S| ≤ log (M / ‖f c‖) / log 3`.

* `finite_setOf_zeros`, `ncard_setOf_zeros_le` : consequently the zero set of `f` inside the ball
  of radius `R / 4` is finite, with at most `log (M / ‖f c‖) / log 3` elements.

The proof is the elementary one: divide out one zero at a time.  If `f a = 0` with
`‖a - c‖ ≤ R / 4`, then `g = dslope f a` (which is `z ↦ f z / (z - a)` away from `a`, and is
holomorphic across `a` by the removable-singularity theorem) satisfies
`‖g‖ ≤ M / (3R/4)` on the circle of radius `R` (by the maximum principle, since `‖z - a‖ ≥ 3R/4`
there), while `‖g c‖ ≥ ‖f c‖ / (R/4)`.  Each such step therefore improves the ratio
`M / ‖f c‖` by a factor of `3`.  No use is made of Jensen's formula.

Zeroes are counted *without* multiplicity: `S` is a finite set of points.
-/

open Complex Metric Set

namespace RiemannHypothesis

/-- **Counting zeroes in a disc.**  If `f` is holomorphic on `B(c, R)`, continuous on the closed
ball, bounded by `M` on the boundary circle, and `S` is a finite set of zeroes of `f` in the
concentric ball of radius `R / 4`, then `3 ^ |S| * ‖f c‖ ≤ M`. -/
theorem pow_three_card_mul_norm_le {c : ℂ} {R : ℝ} (hR : 0 < R) :
    ∀ (n : ℕ) (f : ℂ → ℂ) (M : ℝ), DiffContOnCl ℂ f (ball c R) →
      (∀ z ∈ sphere c R, ‖f z‖ ≤ M) →
      ∀ S : Finset ℂ, S.card = n → (∀ a ∈ S, dist a c ≤ R / 4 ∧ f a = 0) →
      3 ^ n * ‖f c‖ ≤ M := by
  intro n
  induction n with
  | zero =>
      intro f M hf hM _ _ _
      have : ‖f c‖ ≤ M := by
        refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf ?_ ?_
        · rw [frontier_ball c hR.ne']; exact hM
        · rw [closure_ball c hR.ne']; simp [hR.le]
      simpa using this
  | succ n ih =>
      intro f M hf hM S hScard hSzero
      obtain ⟨a, ha⟩ : ∃ a, a ∈ S := Finset.card_pos.mp (by omega)
      obtain ⟨hac, hfa⟩ := hSzero a ha
      have hM0 : 0 ≤ M :=
        le_trans (norm_nonneg _) (hM (c + R) (by simp [Complex.norm_real, abs_of_pos hR]))
      by_cases hca : c = a
      · subst hca; simp [hfa, hM0]
      have haball : a ∈ ball c R := by rw [mem_ball]; linarith [hac]
      set g := dslope f a with hg
      have hgz : ∀ z, z ≠ a → g z = (f z - f a) / (z - a) := by
        intro z hz
        rw [hg, dslope_of_ne _ hz, slope_def_field, ← neg_div_neg_eq]
      have hgdiff : DifferentiableOn ℂ g (ball c R) :=
        (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds haball)).mpr hf.differentiableOn
      have hgcont : ContinuousOn g (closure (ball c R)) := by
        rw [closure_ball c hR.ne']
        intro z hz
        by_cases hza : z = a
        · subst hza
          exact ((hgdiff.differentiableAt
            (isOpen_ball.mem_nhds haball)).continuousAt).continuousWithinAt
        · have h1 : ContinuousWithinAt (fun x => (f x - f a) / (x - a)) (closedBall c R) z := by
            have := (hf.continuousOn.mono (by rw [closure_ball c hR.ne'])) z hz
            exact (this.sub continuousWithinAt_const).div
              (continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero.mpr hza)
          have hev : g =ᶠ[nhds z] (fun x => (f x - f a) / (x - a)) := by
            filter_upwards [isOpen_ne.mem_nhds hza] with x hx using hgz x hx
          exact h1.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) (hgz z hza)
      have hgDCC : DiffContOnCl ℂ g (ball c R) := ⟨hgdiff, hgcont⟩
      have hRa : ∀ z ∈ sphere c R, 3 * R / 4 ≤ ‖z - a‖ := by
        intro z hz
        have h1 : ‖z - c‖ = R := by simpa [Complex.dist_eq] using hz
        have h2 : ‖a - c‖ ≤ R / 4 := by simpa [Complex.dist_eq] using hac
        have h3 : ‖z - c‖ - ‖a - c‖ ≤ ‖z - a‖ := by
          have := norm_sub_norm_le (z - c) (a - c); simpa using this
        linarith
      have hgsphere : ∀ z ∈ sphere c R, ‖g z‖ ≤ 4 * M / (3 * R) := by
        intro z hz
        have hza : z ≠ a := by
          intro h
          have h1 : ‖z - c‖ = R := by simpa [Complex.dist_eq] using hz
          have h2 : ‖a - c‖ ≤ R / 4 := by simpa [Complex.dist_eq] using hac
          rw [h] at h1; linarith
        rw [hgz z hza, hfa, sub_zero, norm_div]
        rw [div_le_div_iff₀ (by linarith [hRa z hz, norm_pos_iff.mpr (sub_ne_zero.mpr hza)])
          (by linarith)]
        nlinarith [hM z hz, norm_nonneg (f z), hRa z hz]
      have hIH := ih g (4 * M / (3 * R)) hgDCC hgsphere (S.erase a)
        (by rw [Finset.card_erase_of_mem ha, hScard]; rfl)
        (fun b hb => ⟨(hSzero b (Finset.mem_of_mem_erase hb)).1, by
          rw [hgz b (Finset.ne_of_mem_erase hb), (hSzero b (Finset.mem_of_mem_erase hb)).2, hfa]
          simp⟩)
      have hgc : ‖g c‖ = ‖f c‖ / ‖c - a‖ := by rw [hgz c hca, hfa, sub_zero, norm_div]
      have hcanorm : ‖c - a‖ ≤ R / 4 := by rw [← Complex.dist_eq, dist_comm]; exact hac
      have hcapos : 0 < ‖c - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hca)
      have h4 : 4 * ‖f c‖ / R ≤ ‖g c‖ := by
        rw [hgc, div_le_div_iff₀ hR hcapos]
        nlinarith [norm_nonneg (f c)]
      have h3 : (0:ℝ) < 3 ^ n := pow_pos (by norm_num) n
      have hkey : 3 ^ n * (4 * ‖f c‖ / R) ≤ 4 * M / (3 * R) := le_trans (by nlinarith) hIH
      have h5 := mul_le_mul_of_nonneg_right hkey (le_of_lt (show (0:ℝ) < 3 * R / 4 by positivity))
      have e1 : 3 ^ n * (4 * ‖f c‖ / R) * (3 * R / 4) = 3 ^ n * 3 * ‖f c‖ := by field_simp
      have e2 : 4 * M / (3 * R) * (3 * R / 4) = M := by field_simp
      rw [e1, e2] at h5
      rw [pow_succ]
      exact h5

/-- Logarithmic form of `pow_three_card_mul_norm_le`: the number of zeroes of `f` in the ball of
radius `R / 4` is at most `log (M / ‖f c‖) / log 3`. -/
theorem card_le_log_div_log_three {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hc : f c ≠ 0)
    (S : Finset ℂ) (hS : ∀ a ∈ S, dist a c ≤ R / 4 ∧ f a = 0) :
    (S.card : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 := by
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have hkey := pow_three_card_mul_norm_le hR S.card f M hf hM S rfl hS
  have h1 : (3 : ℝ) ^ S.card ≤ M / ‖f c‖ := by
    rw [le_div_iff₀ hfc]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog3]
  have h2 : Real.log ((3 : ℝ) ^ S.card) ≤ Real.log (M / ‖f c‖) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  linarith

/-- The zero set of `f` inside the ball of radius `R / 4` is finite. -/
theorem finite_setOf_zeros {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hc : f c ≠ 0) :
    {z : ℂ | dist z c ≤ R / 4 ∧ f z = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set B : ℝ := Real.log (M / ‖f c‖) / Real.log 3 with hB
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (⌈B⌉₊ + 1)
  have h1 : ((⌈B⌉₊ + 1 : ℕ) : ℝ) ≤ B := by
    have := card_le_log_div_log_three hR hf hM hc T (fun a ha => hTsub ha)
    rwa [hTcard] at this
  have h2 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  push_cast at h1
  linarith

/-- The number of zeroes of `f` in the ball of radius `R / 4`, counted without multiplicity, is at
most `log (M / ‖f c‖) / log 3`. -/
theorem ncard_setOf_zeros_le {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hc : f c ≠ 0) :
    ({z : ℂ | dist z c ≤ R / 4 ∧ f z = 0}.ncard : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 := by
  have hfin := finite_setOf_zeros hR hf hM hc
  have h := card_le_log_div_log_three hR hf hM hc hfin.toFinset
    (fun a ha => by simpa using hfin.mem_toFinset.mp ha)
  rwa [Set.ncard_eq_toFinset_card _ hfin]

end RiemannHypothesis
