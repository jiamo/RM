/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A holomorphic logarithm on a half-plane

A nonvanishing entire function has a holomorphic logarithm on any open half-plane
`{s : ℂ | a < re s}`.  This is the special case of the monodromy theorem that the equivalence
`ZetaStripForm ↔ ZetaLogBranchForm` of `RiemannHypothesis.Criteria` needs, proved here from
Morera's theorem on a disc (`DifferentiableOn.isExactOn_ball`): the half-plane is exhausted by
the increasing family of discs `B n = ball (a + n) n`, a primitive of the logarithmic derivative
`f'/f` exists on each disc, the primitives normalized at the base point `a + 1` agree on overlaps
because two functions with the same derivative on a disc that agree at a point are equal, and the
resulting function `F` on the half-plane satisfies `exp ∘ F = f` because `f · exp (-F)` has
vanishing derivative on the (convex) half-plane and takes the value `1` at the base point.

## Main results

* `RiemannHypothesis.exists_holomorphic_log_halfPlane` — if `f` is entire and has no zero with
  `a < re s`, then there is `F` with `F' = f'/f` and `exp (F s) = f s` on the half-plane.
-/

noncomputable section

open Complex Metric Set

namespace RiemannHypothesis

/-- **A holomorphic logarithm on a half-plane.**  If `f` is entire and does not vanish on the
half-plane `a < re s`, there is a function `F`, holomorphic there with derivative the logarithmic
derivative of `f`, such that `exp (F s) = f s` throughout the half-plane. -/
theorem exists_holomorphic_log_halfPlane {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℝ}
    (hne : ∀ s : ℂ, a < s.re → f s ≠ 0) :
    ∃ F : ℂ → ℂ, (∀ s : ℂ, a < s.re → HasDerivAt F (deriv f s / f s) s) ∧
      ∀ s : ℂ, a < s.re → Complex.exp (F s) = f s := by
  classical
  set h : ℂ → ℂ := fun z => deriv f z / f z with hh
  have hderiv : Differentiable ℂ (deriv f) := by
    have h1 : AnalyticOnNhd ℂ f Set.univ := (Complex.analyticOnNhd_univ_iff_differentiable).2 hf
    exact (Complex.analyticOnNhd_univ_iff_differentiable).1 h1.deriv
  set B : ℕ → Set ℂ := fun n => ball ((a : ℂ) + n) n with hB
  have hmemB : ∀ (n : ℕ) (z : ℂ), z ∈ B n ↔ ‖z - ((a : ℂ) + n)‖ < n := by
    intro n z; simp [hB, Metric.mem_ball, dist_eq_norm]
  have hBU : ∀ (n : ℕ) (z : ℂ), z ∈ B n → a < z.re := by
    intro n z hz
    have h1 : ‖z - ((a : ℂ) + n)‖ < n := (hmemB n z).1 hz
    have h2 : |(z - ((a : ℂ) + n)).re| ≤ ‖z - ((a : ℂ) + n)‖ := Complex.abs_re_le_norm _
    have h3 : (z - ((a : ℂ) + n)).re = z.re - a - n := by simp; ring
    have h4 := abs_lt.1 (lt_of_le_of_lt h2 h1)
    rw [h3] at h4
    linarith [h4.1]
  have hBmono : ∀ {m n : ℕ}, m ≤ n → B m ⊆ B n := by
    intro m n hmn z hz
    have h1 : ‖z - ((a : ℂ) + m)‖ < m := (hmemB m z).1 hz
    have h2 : ‖z - ((a : ℂ) + n)‖ ≤ ‖z - ((a : ℂ) + m)‖ + ‖((a : ℂ) + m) - ((a : ℂ) + n)‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub z ((a : ℂ) + m) ((a : ℂ) + n)
    have h3 : ‖((a : ℂ) + m) - ((a : ℂ) + n)‖ = (n : ℝ) - m := by
      have he : ((a : ℂ) + m) - ((a : ℂ) + n) = (((m : ℝ) - n : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)]
      ring
    rw [h3] at h2
    exact (hmemB n z).2 (by linarith)
  have hcover : ∀ z : ℂ, a < z.re → ∃ n : ℕ, z ∈ B n := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (((z.re - a) ^ 2 + z.im ^ 2) / (2 * (z.re - a)))
    have hpos : 0 < z.re - a := by linarith
    refine ⟨n, (hmemB n z).2 ?_⟩
    have hsq : ‖z - ((a : ℂ) + n)‖ ^ 2 = (z.re - a - n) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
    have hkey : (z.re - a - n) ^ 2 + z.im ^ 2 < (n : ℝ) ^ 2 := by
      have h1 : ((z.re - a) ^ 2 + z.im ^ 2) / (2 * (z.re - a)) < n := hn
      rw [div_lt_iff₀ (by linarith)] at h1
      nlinarith
    nlinarith [norm_nonneg (z - ((a : ℂ) + n)), hsq]
  -- the base point of the normalization
  set p : ℂ := (a : ℂ) + 1 with hp
  have hpU : a < p.re := by simp [hp]
  have hpB : ∀ n : ℕ, 1 ≤ n → p ∈ B n := by
    intro n hn
    refine (hmemB n p).2 ?_
    have he : p - ((a : ℂ) + n) = (((1 : ℝ) - n : ℝ) : ℂ) := by rw [hp]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonpos (by linarith)]
    linarith
  -- a normalized primitive of `f'/f` on each disc
  have hprim : ∀ n : ℕ, ∃ G : ℂ → ℂ,
      (∀ z ∈ B n, HasDerivAt G (h z) z) ∧ G p = Complex.log (f p) := by
    intro n
    have hdiff : DifferentiableOn ℂ h (ball ((a : ℂ) + n) (n : ℝ)) := by
      intro z hz
      exact ((hderiv z).div (hf z) (hne z (hBU n z hz))).differentiableWithinAt
    obtain ⟨P, hP⟩ := hdiff.isExactOn_ball
    refine ⟨fun z => P z - P p + Complex.log (f p), fun z hz => ?_, by ring⟩
    simpa using ((hP z hz).sub_const (P p)).add_const (Complex.log (f p))
  choose G hG hGp using hprim
  -- the primitives agree on overlaps
  have hkey : ∀ (m n : ℕ), m ≤ n → ∀ z ∈ B m, G m z = G n z := by
    intro m n hmn z hz
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact absurd ((hmemB 0 z).1 hz) (by simp)
      · exact hm
    have hdm : DifferentiableOn ℂ (G m) (B m) := fun x hx =>
      (hG m x hx).differentiableAt.differentiableWithinAt
    have hdn : DifferentiableOn ℂ (G n) (B m) := fun x hx =>
      (hG n x (hBmono hmn hx)).differentiableAt.differentiableWithinAt
    have hfd : ∀ x ∈ B m, fderiv ℂ (G m) x = fderiv ℂ (G n) x := by
      intro x hx
      rw [(hG m x hx).hasFDerivAt.fderiv, (hG n x (hBmono hmn hx)).hasFDerivAt.fderiv]
    have hEq : Set.EqOn (G m) (G n) (B m) :=
      isOpen_ball.eqOn_of_fderiv_eq ((convex_ball _ _).isPreconnected) hdm hdn hfd (hpB m hm1)
        (by rw [hGp, hGp])
    exact hEq hz
  have hconsist : ∀ (m n : ℕ) (z : ℂ), z ∈ B m → z ∈ B n → G m z = G n z := by
    intro m n z hzm hzn
    rcases le_total m n with hmn | hnm
    · exact hkey m n hmn z hzm
    · exact (hkey n m hnm z hzn).symm
  -- the glued function
  set F : ℂ → ℂ := fun z => if hz : a < z.re then G (Classical.choose (hcover z hz)) z else 0
    with hFdef
  have hFeq : ∀ (n : ℕ) (z : ℂ), z ∈ B n → F z = G n z := by
    intro n z hz
    have hzU : a < z.re := hBU n z hz
    have hval : F z = G (Classical.choose (hcover z hzU)) z := by simp [hFdef, hzU]
    rw [hval]
    exact hconsist _ _ z (Classical.choose_spec (hcover z hzU)) hz
  have hFderiv : ∀ s : ℂ, a < s.re → HasDerivAt F (h s) s := by
    intro s hs
    obtain ⟨n, hn⟩ := hcover s hs
    have hev : F =ᶠ[nhds s] G n := by
      filter_upwards [isOpen_ball.mem_nhds (show s ∈ ball ((a : ℂ) + n) (n : ℝ) from hn)] with w hw
        using hFeq n w hw
    exact (hG n s hn).congr_of_eventuallyEq hev
  have hFp : F p = Complex.log (f p) := by
    rw [hFeq 1 p (hpB 1 le_rfl), hGp]
  refine ⟨F, hFderiv, ?_⟩
  -- `f · exp (-F)` is constant on the half-plane, with value `1`
  set φ : ℂ → ℂ := fun z => f z * Complex.exp (-F z) with hφ
  have hφderiv : ∀ z : ℂ, a < z.re → HasDerivAt φ 0 z := by
    intro z hz
    have hz0 : f z ≠ 0 := hne z hz
    have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have h3 : HasDerivAt (fun w => Complex.exp (-F w)) (Complex.exp (-F z) * (-(h z))) z :=
      ((hFderiv z hz).neg).cexp
    have h4 : HasDerivAt φ
        (deriv f z * Complex.exp (-F z) + f z * (Complex.exp (-F z) * -(h z))) z := h1.mul h3
    have hzero : deriv f z * Complex.exp (-F z) + f z * (Complex.exp (-F z) * -(h z)) = 0 := by
      rw [hh]
      field_simp
      ring
    rwa [hzero] at h4
  have hUopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconst : ∀ z : ℂ, a < z.re → φ z = φ p := by
    intro z hz
    refine (convex_halfSpace_re_gt a).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) ?_ ?_ hz hpU
    · exact fun x hx => (hφderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [fderivWithin_of_isOpen hUopen hx, (hφderiv x hx).hasFDerivAt.fderiv]
      simp
  have hφp : φ p = 1 := by
    rw [hφ]
    simp only [hFp, Complex.exp_neg, Complex.exp_log (hne p hpU)]
    exact mul_inv_cancel₀ (hne p hpU)
  intro s hs
  have hcs := hconst s hs
  rw [hφp, hφ] at hcs
  simp only at hcs
  have hfs : f s ≠ 0 := hne s hs
  have hinv : Complex.exp (-F s) = (f s)⁻¹ := by
    field_simp at hcs ⊢
    linear_combination hcs
  rw [Complex.exp_neg] at hinv
  have h2 : (Complex.exp (F s))⁻¹ = (f s)⁻¹ := hinv
  simpa using congrArg (·⁻¹) h2

end RiemannHypothesis
