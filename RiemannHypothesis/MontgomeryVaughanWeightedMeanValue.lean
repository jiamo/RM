/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MontgomeryVaughanWeighted
import RiemannHypothesis.MontgomeryVaughanMeanValue

/-!
# The weighted Montgomery–Vaughan mean value theorem

From the weighted generalized Hilbert inequality of
`RiemannHypothesis/MontgomeryVaughanWeighted.lean` (constant `5 √2`), exactly as
`RiemannHypothesis/MontgomeryVaughanMeanValue.lean` derives the unweighted theorem:

* `abs_integral_normSq_expSum_sub_le_weighted` — for real `λ_r` and weights `δ_r > 0` with
  `δ_r ≤ |λ_r - λ_s|` for every `s ≠ r`,
  `|∫₀ᵀ |∑_r a_r e^{i λ_r t}|² dt - T ∑_r |a_r|²| ≤ 10 √2 ∑_r |a_r|² / δ_r`.
  The difference is `-i (H(x) - H(a))` (`MontgomeryVaughan.integral_normSq_expSum_eq`) and each
  Hilbert form is at most `5 √2 ∑ |a_r|² / δ_r`.
* `abs_integral_normSq_dirichletPoly_sub_le_weighted` — the Dirichlet-polynomial form, with
  `λ_n = -log n`, whose local spacing at `n` is at least `1 / (n + 1)` (`log_local_spacing`):
  `|∫₀ᵀ |∑_{n ≤ N} a_n n^{-it}|² dt - T ∑_{n ≤ N} |a_n|²| ≤ 10 √2 ∑_{n ≤ N} (n + 1) |a_n|²`,
  i.e. `∫₀ᵀ |D(it)|² dt = ∑_{n ≤ N} |a_n|² (T + O(n))` (Montgomery–Vaughan, with `3π` in place
  of `10 √2 ≈ 14.14 ≈ 4.50 π`).
-/

open Complex Finset

namespace RiemannHypothesis

namespace MontgomeryVaughanWeighted

open MontgomeryVaughan

variable {n : ℕ}

/-- **The weighted mean value theorem for exponential sums**: for real `λ_r`, weights `δ_r > 0`
with `δ_r ≤ |λ_r - λ_s|` (`s ≠ r`) and complex `a_r`,
`|∫₀ᵀ |∑_r a_r e^{i λ_r t}|² dt - T ∑_r |a_r|²| ≤ 10 √2 ∑_r |a_r|² / δ_r`. -/
theorem abs_integral_normSq_expSum_sub_le_weighted (lam δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ |lam r - lam s|) (a : Fin n → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2)
        - T * ∑ r, ‖a r‖ ^ 2|
      ≤ 10 * Real.sqrt 2 * ∑ r, ‖a r‖ ^ 2 / δ r := by
  have hinj : ∀ r s, r ≠ s → lam r ≠ lam s := by
    intro r s h he
    have := hsep r s h
    rw [he, sub_self, abs_zero] at this
    linarith [hδ r]
  set x : Fin n → ℂ := fun r => a r * cexp ((T : ℂ) * (lam r : ℂ) * I)
  have hx : ∀ r, ‖x r‖ = ‖a r‖ := fun r => by
    simp only [x, norm_mul]
    rw [show (T : ℂ) * (lam r : ℂ) * I = ((T * lam r : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have key := integral_normSq_expSum_eq lam hinj a T
  have hD : (((∫ t in (0 : ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2)
        - T * ∑ r, ‖a r‖ ^ 2 : ℝ) : ℂ) = -I * (hilbertForm lam x - hilbertForm lam a) := by
    push_cast
    rw [key]
    push_cast
    ring
  have hGx := weightedHilbertInequality lam δ hδ hsep x
  have hGa := weightedHilbertInequality lam δ hδ hsep a
  simp only [hx] at hGx
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hD, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc ‖hilbertForm lam x - hilbertForm lam a‖
      ≤ ‖hilbertForm lam x‖ + ‖hilbertForm lam a‖ := norm_sub_le _ _
    _ ≤ 5 * Real.sqrt 2 * ∑ r, ‖a r‖ ^ 2 / δ r + 5 * Real.sqrt 2 * ∑ r, ‖a r‖ ^ 2 / δ r :=
        add_le_add hGx hGa
    _ = 10 * Real.sqrt 2 * ∑ r, ‖a r‖ ^ 2 / δ r := by ring

/-- `1 - p / q ≤ log q - log p` for `0 < p < q`. -/
lemma one_sub_div_le_log_sub {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    1 - p / q ≤ Real.log q - Real.log p := by
  have hq : 0 < q := hp.trans hpq
  rw [← Real.log_div hq.ne' hp.ne']
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
  rwa [inv_div] at h

/-- **The local spacing of `-log n`**: for `1 ≤ n ≠ m ≤ N` (written `n = k + 1`, `m = l + 1`),
`|log n - log m| ≥ 1 / (n + 1)`. -/
lemma log_local_spacing {N : ℕ} (k l : Fin N) (hkl : k ≠ l) :
    1 / ((k : ℕ) + 2 : ℝ) ≤ |-Real.log ((k : ℕ) + 1 : ℝ) - -Real.log ((l : ℕ) + 1 : ℝ)| := by
  have hk0 : (0 : ℝ) < (k : ℕ) + 1 := by positivity
  have hl0 : (0 : ℝ) < (l : ℕ) + 1 := by positivity
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
  · -- `k < l`
    have hkl' : ((k : ℕ) : ℝ) + 2 ≤ (l : ℕ) + 1 := by
      have : (k : ℕ) + 1 ≤ l := h
      have : ((k : ℕ) : ℝ) + 1 ≤ (l : ℕ) := by exact_mod_cast this
      linarith
    have h1 := one_sub_div_le_log_sub hk0 (by linarith : ((k : ℕ) + 1 : ℝ) < (l : ℕ) + 1)
    have h2 : 1 / ((k : ℕ) + 2 : ℝ) ≤ 1 - ((k : ℕ) + 1) / ((l : ℕ) + 1) := by
      rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div,
        le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hl0]
      nlinarith
    rw [abs_of_nonneg (by linarith [show (0 : ℝ) ≤ 1 / ((k : ℕ) + 2) by positivity])]
    linarith
  · -- `l < k`
    have hlk' : ((l : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by
      have : (l : ℕ) + 1 ≤ k := h
      exact_mod_cast this
    have h1 := one_sub_div_le_log_sub hl0 (by linarith : ((l : ℕ) + 1 : ℝ) < (k : ℕ) + 1)
    have h2 : 1 / ((k : ℕ) + 2 : ℝ) ≤ 1 - ((l : ℕ) + 1) / ((k : ℕ) + 1) := by
      rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div,
        le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hk0]
      nlinarith
    rw [abs_of_nonpos (by linarith [show (0 : ℝ) ≤ 1 / ((k : ℕ) + 2) by positivity])]
    linarith

/-- **The weighted Montgomery–Vaughan mean value theorem for Dirichlet polynomials**, with the
explicit constant `10 √2`:
`|∫₀ᵀ ‖∑_{n ≤ N} a n n^(-i t)‖² dt - T ∑_{n ≤ N} ‖a n‖²| ≤ 10 √2 ∑_{n ≤ N} (n + 1) ‖a n‖²`,
i.e. `∫₀ᵀ |D(it)|² dt = ∑_{n ≤ N} |a_n|² (T + O(n))`. -/
theorem abs_integral_normSq_dirichletPoly_sub_le_weighted (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
        - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
      ≤ 10 * Real.sqrt 2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
  set lam : Fin N → ℝ := fun k => -Real.log ((k : ℕ) + 1 : ℝ)
  set δ : Fin N → ℝ := fun k => 1 / ((k : ℕ) + 2 : ℝ)
  have hpoly : ∀ t : ℝ, dirichletPoly a N ((t : ℂ) * I)
      = ∑ k : Fin N, a ((k : ℕ) + 1) * cexp ((t : ℂ) * (lam k : ℂ) * I) := by
    intro t
    rw [dirichletPoly, sum_Icc_eq_sum_fin N (fun n => a n * (n : ℂ) ^ (-((t : ℂ) * I)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have hne : (((k : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k : ℕ)
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log]
    simp only [lam]
    push_cast
    ring_nf
  have h := abs_integral_normSq_expSum_sub_le_weighted lam δ (fun k => by positivity)
    (fun k l hkl => log_local_spacing k l hkl) (fun k => a ((k : ℕ) + 1)) T
  simp_rw [hpoly]
  rw [sum_Icc_eq_sum_fin N (fun n => ‖a n‖ ^ 2),
    sum_Icc_eq_sum_fin N (fun n => ((n : ℝ) + 1) * ‖a n‖ ^ 2)]
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [δ]
  push_cast
  field_simp
  ring

end MontgomeryVaughanWeighted

end RiemannHypothesis
