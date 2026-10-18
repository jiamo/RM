/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MontgomeryVaughan
import RiemannHypothesis.DirichletPolyMeanSquare

/-!
# The Montgomery–Vaughan mean value theorem

From the generalized Hilbert inequality of `RiemannHypothesis/MontgomeryVaughan.lean`:

* `abs_integral_normSq_expSum_sub_le` — for `δ`-separated real frequencies `λ_r`,
  `|∫₀ᵀ |∑_r a_r e^{i λ_r t}|² dt - T ∑_r |a_r|²| ≤ (2π / δ) ∑_r |a_r|²`.
  Expanding the square, the diagonal gives `T ∑ |a_r|²` and the off-diagonal terms are
  `-i (H(x) - H(a))` (`integral_normSq_expSum_eq`), where `H` is the Hilbert form
  `∑_{r ≠ s} x_r conj(x_s) / (λ_r - λ_s)` and `x_r = a_r e^{i λ_r T}`; each of `H(x)`, `H(a)` is
  at most `(π / δ) ∑ |a_r|²`.
* `abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul` — the Dirichlet-polynomial form, with
  `λ_n = -log n`, which are `1/N`-separated on `1 ≤ n ≤ N` (`log_separated`):
  `|∫₀ᵀ |∑_{n ≤ N} a_n n^{-it}|² dt - T ∑_{n ≤ N} |a_n|²| ≤ 2π N ∑_{n ≤ N} |a_n|²`,
  i.e. `∫₀ᵀ |D(it)|² dt = (T + O(N)) ∑ |a_n|²`.  This improves the `T + O(N log N)` of
  `RiemannHypothesis.integral_normSq_dirichletPoly_mvt_zero` (`DirichletPolyMeanValue.lean`).

The weighted form `∑ |a_n|² (T + O(n))` (Montgomery–Vaughan, Theorem 2) is not proved here.
-/

open Complex Finset

namespace RiemannHypothesis

namespace MontgomeryVaughan

variable {n : ℕ}

/-- The Hilbert form `∑_{r ≠ s} x_r conj(x_s) / (λ_r - λ_s)`, the left side of
`Hilbert.GeneralizedHilbertInequality`. -/
noncomputable def hilbertForm (lam : Fin n → ℝ) (x : Fin n → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) / ((lam r : ℂ) - (lam s : ℂ))

/-- `∫₀ᵀ e^{i d t} dt`. -/
lemma integral_pair (d : ℝ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, cexp ((t : ℂ) * (d : ℂ) * I)
      = if d = 0 then (T : ℂ) else -I * (cexp ((T : ℂ) * (d : ℂ) * I) - 1) / (d : ℂ) := by
  split_ifs with hd
  · subst hd; simp
  have hc : (d : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hd) I_ne_zero
  have := integral_exp_mul_complex (a := 0) (b := T) hc
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at this
  rw [show (fun t : ℝ => cexp ((t : ℂ) * (d : ℂ) * I)) = fun t : ℝ => cexp ((d : ℂ) * I * t) by
    funext t; ring_nf, this]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- The mean square of an exponential sum, exactly: the diagonal `T ∑ |a_r|²` plus
`-i (H(x) - H(a))` with `x_r = a_r e^{i λ_r T}`. -/
theorem integral_normSq_expSum_eq (lam : Fin n → ℝ) (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (a : Fin n → ℂ) (T : ℝ) :
    (((∫ t in (0:ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2 : ℝ)) : ℂ)
      = T * ∑ r, ((‖a r‖ ^ 2 : ℝ) : ℂ)
        + -I * (hilbertForm lam (fun r => a r * cexp ((T : ℂ) * (lam r : ℂ) * I))
          - hilbertForm lam a) := by
  rw [← intervalIntegral.integral_ofReal]
  have hpt : ∀ t : ℝ, ((‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ r, ∑ s, a r * (starRingEnd ℂ) (a s)
          * cexp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I) := by
    intro t
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    ring_nf
  simp_rw [hpt]
  have hint : ∀ r s, IntervalIntegrable
      (fun t : ℝ => a r * (starRingEnd ℂ) (a s)
        * cexp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)) MeasureTheory.volume 0 T :=
    fun r s => (by fun_prop : Continuous fun t : ℝ => a r * (starRingEnd ℂ) (a s)
      * cexp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)).intervalIntegrable _ _
  have hint' : ∀ r, IntervalIntegrable
      (fun t : ℝ => ∑ s, a r * (starRingEnd ℂ) (a s)
        * cexp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)) MeasureTheory.volume 0 T :=
    fun r => (by fun_prop : Continuous fun t : ℝ => ∑ s, a r * (starRingEnd ℂ) (a s)
      * cexp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum fun r _ => hint' r]
  simp_rw [intervalIntegral.integral_finsetSum fun s _ => hint _ s,
    intervalIntegral.integral_const_mul, integral_pair]
  unfold hilbertForm
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), sub_self, if_pos rfl,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Complex.ofReal_pow, ← Complex.mul_conj']; ring
  refine Finset.sum_congr rfl fun s hs => ?_
  have hne : lam r - lam s ≠ 0 := sub_ne_zero.mpr (hinj r s (Finset.ne_of_mem_erase hs).symm)
  have hne' : (lam r : ℂ) - (lam s : ℂ) ≠ 0 := by exact_mod_cast hne
  rw [if_neg hne, map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hexp : cexp ((T : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)
      = cexp ((T : ℂ) * (lam r : ℂ) * I) * cexp ((T : ℂ) * (lam s : ℂ) * -I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hexp]
  push_cast
  field_simp

/-- **The mean value theorem for `δ`-separated frequencies** (Montgomery–Vaughan): for real
`λ_r` with `|λ_r - λ_s| ≥ δ` (`r ≠ s`) and complex `a_r`,
`|∫₀ᵀ |∑_r a_r e^{i λ_r t}|² dt - T ∑_r |a_r|²| ≤ (2π / δ) ∑_r |a_r|²`. -/
theorem abs_integral_normSq_expSum_sub_le (lam : Fin n → ℝ) (a : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ r, a r * cexp ((t : ℂ) * (lam r : ℂ) * I)‖ ^ 2)
        - T * ∑ r, ‖a r‖ ^ 2|
      ≤ 2 * Real.pi / δ * ∑ r, ‖a r‖ ^ 2 := by
  have hinj : ∀ r s, r ≠ s → lam r ≠ lam s := by
    intro r s h he
    have := hsep r s h
    rw [he, sub_self, abs_zero] at this
    linarith
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
  have hGx := generalizedHilbertInequality n lam x δ hδ hsep
  have hGa := generalizedHilbertInequality n lam a δ hδ hsep
  simp only [hx] at hGx
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hD, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc ‖hilbertForm lam x - hilbertForm lam a‖
      ≤ ‖hilbertForm lam x‖ + ‖hilbertForm lam a‖ := norm_sub_le _ _
    _ ≤ Real.pi / δ * ∑ r, ‖a r‖ ^ 2 + Real.pi / δ * ∑ r, ‖a r‖ ^ 2 := add_le_add hGx hGa
    _ = 2 * Real.pi / δ * ∑ r, ‖a r‖ ^ 2 := by ring

/-- The frequencies `-log n`, `1 ≤ n ≤ N`, are `1/N`-separated. -/
lemma log_separated {N : ℕ} (k l : Fin N) (hkl : k ≠ l) :
    1 / (N : ℝ) ≤ |-Real.log ((k : ℕ) + 1 : ℝ) - -Real.log ((l : ℕ) + 1 : ℝ)| := by
  have key : ∀ m n : ℕ, m < n → n < N →
      1 / (N : ℝ) ≤ Real.log ((n : ℝ) + 1) - Real.log ((m : ℝ) + 1) := by
    intro m n hmn hnN
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmn' : (m : ℝ) + 1 < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hmn
    have hnN' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hnN
    rw [← Real.log_div hn.ne' hm.ne']
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
    refine le_trans ?_ h1
    rw [inv_div, one_sub_div hn.ne', div_le_div_iff₀ (by linarith) hn]
    have : (1 : ℝ) ≤ (n : ℝ) + 1 - ((m : ℝ) + 1) := by
      have : m + 1 ≤ n := hmn
      have : ((m : ℝ) + 1) ≤ n := by exact_mod_cast this
      linarith
    nlinarith
  have hk := k.isLt
  have hl := l.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
  · have := key k l h hl
    rw [abs_of_nonneg (by linarith [show 0 ≤ 1 / (N : ℝ) by positivity])]
    linarith
  · have := key l k h hk
    rw [abs_of_nonpos (by linarith [show 0 ≤ 1 / (N : ℝ) by positivity])]
    linarith

lemma sum_Icc_eq_sum_fin (N : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ k : Fin N, f ((k : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k + 1)), Finset.range_eq_Ico,
    Finset.sum_Ico_add']
  rfl

/-- **The Montgomery–Vaughan mean value theorem for Dirichlet polynomials**, with the explicit
constant `2π N`: `∫₀ᵀ |∑_{n ≤ N} a_n n^{-it}|² dt = (T + O(N)) ∑_{n ≤ N} |a_n|²`, precisely
`|∫₀ᵀ ‖∑_{n ≤ N} a n n^(-i t)‖² dt - T ∑_{n ≤ N} ‖a n‖²| ≤ 2π N ∑_{n ≤ N} ‖a n‖²`. -/
theorem abs_integral_normSq_dirichletPoly_sub_le_two_pi_mul (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
        - T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
      ≤ 2 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [dirichletPoly]
  set lam : Fin N → ℝ := fun k => -Real.log ((k : ℕ) + 1 : ℝ)
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
  have h := abs_integral_normSq_expSum_sub_le lam (fun k => a ((k : ℕ) + 1))
    (δ := 1 / (N : ℝ)) (by positivity) (fun k l hkl => log_separated k l hkl) T
  simp_rw [hpoly]
  rw [sum_Icc_eq_sum_fin N (fun n => ‖a n‖ ^ 2)]
  have hc : 2 * Real.pi / (1 / (N : ℝ)) = 2 * Real.pi * N := by field_simp
  rw [hc] at h
  exact h

end MontgomeryVaughan

end RiemannHypothesis
