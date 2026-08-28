/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Convexity
import RiemannHypothesis.NearLine
import RiemannHypothesis.Bounds
import RiemannHypothesis.Xi

/-!
# The completed zeta function in the `s`-variable, and its order-one growth bound

This file introduces the entire completed zeta function

`ξ(s) = ½ s (s − 1) Λ(s)`,

written (as in `RiemannHypothesis.Xi`) in the manifestly entire form
`ξ(s) = ½ (s (s − 1) Λ₀(s) + 1)`, and proves the growth estimate that makes the
Riemann–von Mangoldt zero count possible:

`‖ξ(s)‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))`  for an absolute constant `C`.

This says that `ξ` is of order at most `1` (in fact of order `1`, but we do not need the lower
bound).  The proof is elementary given the estimates already in this repository:

* on `re s ≥ 2` the Dirichlet series bound `‖ζ(s)‖ ≤ 1 + 1/(re s − 1) ≤ 2` applies;
* on `1/2 ≤ re s ≤ 2` with `|im s| ≥ 3` the repository's convexity bound
  (`norm_riemannZeta_le_sixteen`) and near-line bound (`norm_riemannZeta_le_log_near_line`) apply;
* the remaining region `1/2 ≤ re s ≤ 2`, `|im s| ≤ 3` is compact and `ξ` is entire;
* the left half-plane is covered by the functional equation `ξ(1 − s) = ξ(s)`.

The Gamma factor is handled by the crude bounds `‖Γ(z)‖ ≤ Γ(re z)` (already in
`RiemannHypothesis.Convexity`) and `Γ(x) ≤ exp ((x+1) log (x+1))`, proved here from the
monotonicity of `Γ` on `[2, ∞)` and `n ! ≤ n ^ n`.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-! ## The function `ξ` in the `s`-variable -/

/-- The completed zeta function `ξ(s) = ½ s (s − 1) Λ(s)`, in the manifestly entire form
`½ (s (s − 1) Λ₀(s) + 1)`. -/
def xiFn (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `Ξ` of `RiemannHypothesis.Xi` is `ξ` composed with `z ↦ ½ + i z`. -/
lemma riemannXi_eq_xiFn (z : ℂ) : riemannXi z = xiFn (xiPoint z) := rfl

theorem differentiable_xiFn : Differentiable ℂ xiFn := by
  unfold xiFn
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- **The functional equation** `ξ(1 − s) = ξ(s)`. -/
theorem xiFn_one_sub (s : ℂ) : xiFn (1 - s) = xiFn s := by
  unfold xiFn
  rw [completedRiemannZeta₀_one_sub]
  ring_nf

/-- Away from `s = 0` and `s = 1`, `ξ(s) = ½ s (s − 1) Λ(s)`. -/
theorem xiFn_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiFn s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h1' : (1 : ℂ) - s ≠ 0 := fun h => h1 (by linear_combination -h)
  rw [xiFn, completedRiemannZeta_eq s]
  field_simp
  ring

/-- Every zero of `ζ` inside the critical strip is a zero of `ξ`. -/
theorem xiFn_eq_zero_of_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : xiFn s = 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  rw [xiFn_eq_completed hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul h0, hz]
  ring

theorem xiFn_two_ne_zero : xiFn (2 : ℂ) ≠ 0 := by
  have h0 : (2 : ℂ) ≠ 0 := by norm_num
  have h1 : (2 : ℂ) ≠ 1 := by norm_num
  have hne : completedRiemannZeta (2 : ℂ) ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hcoef : (2 : ℂ) * (2 - 1) / 2 = 1 := by norm_num
  rw [xiFn_eq_completed h0 h1, hcoef, one_mul]
  exact hne

/-! ## Elementary bounds for the Gamma function -/

/-- `Γ(x) ≤ exp ((x + 1) log (x + 1))` for `x ≥ 1`. -/
theorem Gamma_le_exp_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
  set n : ℕ := ⌈x⌉₊ with hn
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnx : (n : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hfac : Real.Gamma x ≤ (n.factorial : ℝ) := by
    rcases le_or_gt x 2 with h | h
    · have h0 := Gamma_le_one_of_mem_Icc hx h
      have h1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
      linarith
    · have hmem1 : x ∈ Set.Ici (2:ℝ) := by simp; linarith
      have hmem2 : ((n : ℝ) + 1) ∈ Set.Ici (2:ℝ) := by simp; linarith
      have := Real.Gamma_strictMonoOn_Ici.monotoneOn hmem1 hmem2 (by linarith)
      rwa [Real.Gamma_nat_eq_factorial] at this
  have hpow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hlog : (n : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log n) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hmono : (n : ℝ) * Real.log n ≤ (x + 1) * Real.log (x + 1) := by
    have hlogle : Real.log n ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hnx
    have hlognn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
    nlinarith
  calc Real.Gamma x ≤ (n.factorial : ℝ) := hfac
    _ ≤ (n : ℝ) ^ n := hpow
    _ = Real.exp ((n : ℝ) * Real.log n) := hlog
    _ ≤ Real.exp ((x + 1) * Real.log (x + 1)) := Real.exp_le_exp.mpr hmono

/-- `Γ(x) ≤ 4 exp ((x + 1) log (x + 1))` for `x ≥ 1/4`. -/
theorem Gamma_le_exp_of_quarter_le {x : ℝ} (hx : 1 / 4 ≤ x) :
    Real.Gamma x ≤ 4 * Real.exp ((x + 1) * Real.log (x + 1)) := by
  have hexp1 : (1 : ℝ) ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
    refine Real.one_le_exp ?_
    have : (0 : ℝ) ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    nlinarith
  rcases le_or_gt 1 x with h | h
  · have := Gamma_le_exp_of_one_le h
    linarith
  · have hx0 : x ≠ 0 := by intro h0; rw [h0] at hx; linarith
    have hxpos : 0 < x := by linarith
    have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0
    have hle : Real.Gamma (x + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by linarith) (by linarith)
    have : x * Real.Gamma x ≤ 1 := by rw [← hrec]; exact hle
    have hG : Real.Gamma x ≤ 1 / x := by
      rw [le_div_iff₀ hxpos]; linarith [this]
    have h4 : 1 / x ≤ 4 := by
      rw [div_le_iff₀ hxpos]; linarith
    linarith

/-- `‖Γ_ℝ(s)‖ ≤ Γ(re s / 2)` for `re s > 0`. -/
theorem norm_Gammaℝ_le {s : ℂ} (hs : 0 < s.re) : ‖Gammaℝ s‖ ≤ Real.Gamma (s.re / 2) := by
  rw [Gammaℝ_def, norm_mul]
  have h1 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp
    linarith
  have h2 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have := norm_Gamma_le_Gamma_re (s := s / 2) (by simp; linarith)
    simpa using this
  have h3 : (0 : ℝ) ≤ Real.Gamma (s.re / 2) := le_trans (norm_nonneg _) h2
  nlinarith [norm_nonneg ((Real.pi : ℂ) ^ (-s / 2)), norm_nonneg (Complex.Gamma (s / 2))]

/-! ## A polynomial bound for `ζ` on `re s ≥ 1/2` -/

/-- For `re s ≥ 1/2`, provided either `re s ≥ 2` or `|im s| ≥ 3`, one has
`‖ζ(s)‖ ≤ 16 ‖s‖² + 2`. -/
theorem norm_riemannZeta_le_sq {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h : 2 ≤ s.re ∨ 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 16 * ‖s‖ ^ 2 + 2 := by
  have hnorm0 : 0 ≤ ‖s‖ := norm_nonneg s
  rcases le_or_gt 2 s.re with hre | hre
  · have := norm_riemannZeta_le_of_one_lt_re (s := s) (by linarith)
    have h1 : 1 / (s.re - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    nlinarith
  · have ht : 3 ≤ |s.im| := by
      rcases h with h | h
      · linarith
      · exact h
    have hs3 : 3 ≤ ‖s‖ := le_trans (by simpa using ht) (Complex.abs_im_le_norm s)
    rcases le_or_gt s.re 1 with hre1 | hre1
    · have := norm_riemannZeta_le_sixteen h0 hre1 ht
      have himle : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      nlinarith
    · have hL : 1 ≤ Real.log |s.im| := one_le_log_of_three_le ht
      have hcond : 1 - 1 / (2 * Real.log |s.im|) ≤ s.re := by
        have : 0 < 2 * Real.log |s.im| := by linarith
        have h1 : 0 ≤ 1 / (2 * Real.log |s.im|) := by positivity
        linarith
      have := norm_riemannZeta_le_log_near_line ht hcond (by linarith)
      have hlogle : Real.log |s.im| ≤ |s.im| := by
        have := Real.log_le_sub_one_of_pos (x := |s.im|) (by linarith)
        linarith
      have himle : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      nlinarith

/-! ## The growth bound for `ξ` -/

/-- The main estimate on the region where the `ζ` bounds apply. -/
theorem norm_xiFn_le_aux {s : ℂ} (h0 : 1 / 2 ≤ s.re) (h : 2 ≤ s.re ∨ 3 ≤ |s.im|) :
    ‖xiFn s‖ ≤ 36 * (1 + ‖s‖) ^ 4 * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) := by
  have hre0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro hcon; rw [hcon] at hre0; simp at hre0
  have hs1 : s ≠ 1 := by
    intro hcon
    rcases h with hh | hh
    · rw [hcon] at hh; simp at hh
    · rw [hcon] at hh; simp at hh; linarith
  have hnorm0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hre_le : s.re ≤ ‖s‖ := Complex.re_le_norm s
  -- the three factors
  have hzeta := norm_riemannZeta_le_sq h0 h
  have hGamma : ‖Gammaℝ s‖ ≤ 4 * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) := by
    refine le_trans (norm_Gammaℝ_le hre0) ?_
    refine le_trans (Gamma_le_exp_of_quarter_le (by linarith)) ?_
    have hmono : (s.re / 2 + 1) * Real.log (s.re / 2 + 1) ≤ (‖s‖ + 1) * Real.log (‖s‖ + 1) := by
      have h1 : s.re / 2 + 1 ≤ ‖s‖ + 1 := by linarith
      have h2 : Real.log (s.re / 2 + 1) ≤ Real.log (‖s‖ + 1) :=
        Real.log_le_log (by linarith) h1
      have h3 : 0 ≤ Real.log (s.re / 2 + 1) := Real.log_nonneg (by linarith)
      nlinarith
    have := Real.exp_le_exp.mpr hmono
    linarith
  have hexp0 : 0 < Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) := Real.exp_pos _
  -- assemble
  rw [xiFn_eq_completed hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul hre0]
  have hsplit : ‖s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s)‖
      = ‖s‖ * ‖s - 1‖ / 2 * (‖Gammaℝ s‖ * ‖riemannZeta s‖) := by
    simp
  rw [hsplit]
  have hs1norm : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    have := norm_sub_le s 1
    simpa using this
  have hzeta0 : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hG0 : 0 ≤ ‖Gammaℝ s‖ := norm_nonneg _
  have hkeypoly : ‖s‖ * (‖s‖ + 1) / 2 * (4 * (16 * ‖s‖ ^ 2 + 2)) ≤ 36 * (1 + ‖s‖) ^ 4 := by
    nlinarith [pow_nonneg hnorm0 2, pow_nonneg hnorm0 3, pow_nonneg hnorm0 4]
  calc ‖s‖ * ‖s - 1‖ / 2 * (‖Gammaℝ s‖ * ‖riemannZeta s‖)
      ≤ ‖s‖ * (‖s‖ + 1) / 2 *
        ((4 * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1))) * (16 * ‖s‖ ^ 2 + 2)) := by
        have h1 : ‖s‖ * ‖s - 1‖ / 2 ≤ ‖s‖ * (‖s‖ + 1) / 2 := by nlinarith
        have h2 : ‖Gammaℝ s‖ * ‖riemannZeta s‖
            ≤ (4 * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1))) * (16 * ‖s‖ ^ 2 + 2) :=
          mul_le_mul hGamma hzeta hzeta0 (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (‖s‖ * (‖s‖ + 1) / 2 * (4 * (16 * ‖s‖ ^ 2 + 2)))
          * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) := by ring
    _ ≤ 36 * (1 + ‖s‖) ^ 4 * Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) :=
        mul_le_mul_of_nonneg_right hkeypoly hexp0.le

/-- Arithmetic step: the polynomial prefactor is absorbed into the exponential. -/
theorem poly_exp_le {u : ℝ} (hu : 0 ≤ u) :
    36 * (1 + u) ^ 4 * Real.exp ((u + 1) * Real.log (u + 1))
      ≤ Real.exp (16 * (1 + u) * Real.log (2 + u)) := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogu : Real.log 2 ≤ Real.log (2 + u) := Real.log_le_log (by norm_num) (by linarith)
  have hlogu0 : 0 ≤ Real.log (2 + u) := le_trans (by linarith) hlogu
  have hbase : (1 : ℝ) / 2 ≤ (1 + u) * Real.log (2 + u) := by nlinarith
  have h36 : Real.log 36 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h4 : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
      rw [Real.exp_one_pow]; norm_num
    rw [h4]
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) he 4
    nlinarith [this]
  have hpow : Real.log (36 * (1 + u) ^ 4) = Real.log 36 + 4 * Real.log (1 + u) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hlog1u : Real.log (1 + u) ≤ Real.log (2 + u) := Real.log_le_log (by linarith) (by linarith)
  have hlog1u0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hfactor : 36 * (1 + u) ^ 4 = Real.exp (Real.log 36 + 4 * Real.log (1 + u)) := by
    rw [← hpow, Real.exp_log (by positivity)]
  rw [hfactor, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : Real.log 36 ≤ 8 * ((1 + u) * Real.log (2 + u)) := by nlinarith
  have h2 : 4 * Real.log (1 + u) ≤ 4 * ((1 + u) * Real.log (2 + u)) := by nlinarith
  have h3 : (u + 1) * Real.log (u + 1) ≤ (1 + u) * Real.log (2 + u) := by
    have : Real.log (u + 1) ≤ Real.log (2 + u) := Real.log_le_log (by linarith) (by linarith)
    nlinarith
  linarith

/-- **Order-one growth of `ξ`**: `‖ξ(s)‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` for an absolute
constant `C`. -/
theorem norm_xiFn_le : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
    ‖xiFn s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  -- a bound on the compact remaining piece
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) 6).exists_bound_of_continuousOn
    differentiable_xiFn.continuous.continuousOn
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hK'0 : 0 < K' := by linarith
  have hlogK : 0 ≤ Real.log K' := Real.log_nonneg hK'1
  refine ⟨4 * (16 + 4 * Real.log K') + 4, by linarith, ?_⟩
  set C : ℝ := 4 * (16 + 4 * Real.log K') + 4 with hC
  -- the bound on the right half-plane
  have half : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖xiFn s‖ ≤ Real.exp ((16 + 4 * Real.log K') * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro s hs
    have hu : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlogu : Real.log 2 ≤ Real.log (2 + ‖s‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hbase : (1 : ℝ) / 2 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by nlinarith
    have hbase0 : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by linarith
    by_cases hcase : 2 ≤ s.re ∨ 3 ≤ |s.im|
    · refine le_trans (norm_xiFn_le_aux hs hcase) (le_trans (poly_exp_le hu) ?_)
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    · -- the compact region
      push Not at hcase
      obtain ⟨h2, h3⟩ := hcase
      have hsnorm : ‖s‖ ≤ 6 := by
        have := Complex.norm_le_abs_re_add_abs_im s
        have h1 : |s.re| ≤ 2 := by rw [abs_le]; constructor <;> linarith
        linarith
      have hmem : s ∈ Metric.closedBall (0 : ℂ) 6 := by
        simp [Metric.mem_closedBall]; linarith
      have hbound : ‖xiFn s‖ ≤ K' := le_trans (hK s hmem) (le_max_left _ _)
      refine le_trans hbound ((Real.log_le_iff_le_exp hK'0).mp ?_)
      nlinarith
  intro s
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · refine le_trans (half s hs) (Real.exp_le_exp.mpr ?_)
    have hu : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hlogu0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
    have hbase0 : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by positivity
    rw [hC]
    nlinarith
  · -- functional equation
    have hre : 1 / 2 ≤ (1 - s).re := by simp; linarith
    have hnorm : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le (1 : ℂ) s
      simpa using this
    have := half (1 - s) hre
    rw [xiFn_one_sub] at this
    refine le_trans this (Real.exp_le_exp.mpr ?_)
    have hu : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have h1 : (1 : ℝ) + ‖1 - s‖ ≤ 2 * (1 + ‖s‖) := by linarith
    have h2 : Real.log (2 + ‖1 - s‖) ≤ 2 * Real.log (2 + ‖s‖) := by
      have hle : 2 + ‖1 - s‖ ≤ (2 + ‖s‖) ^ 2 := by nlinarith
      have := Real.log_le_log (by positivity) hle
      rwa [Real.log_pow] at this
    have hlogu0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
    have hnn : 0 ≤ (16 + 4 * Real.log K') := by linarith
    have hlog0 : 0 ≤ Real.log (2 + ‖1 - s‖) :=
      Real.log_nonneg (by linarith [norm_nonneg (1 - s)])
    have hprod : (1 + ‖1 - s‖) * Real.log (2 + ‖1 - s‖)
        ≤ (2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖)) :=
      mul_le_mul h1 h2 hlog0 (by linarith)
    have hstep : (16 + 4 * Real.log K') * ((1 + ‖1 - s‖) * Real.log (2 + ‖1 - s‖))
        ≤ (16 + 4 * Real.log K') * ((2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖))) :=
      mul_le_mul_of_nonneg_left hprod hnn
    have hbase0 : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by positivity
    rw [hC]
    nlinarith

end RiemannHypothesis
