/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieveFarey

/-!
# The dual large sieve

The large sieve inequality bounds the values of an exponential polynomial at separated points by
its coefficients.  Its *dual* runs the other way: it bounds the coefficients of an exponential
sum over the separated points.  The two are equivalent, by the duality principle for a finite
matrix `φ`: the bound `∑_i ‖∑_n a_n φ_{i,n}‖² ≤ C ∑_n ‖a_n‖²` for all `a` is equivalent to
`∑_n ‖∑_i x_i conj(φ_{i,n})‖² ≤ C ∑_i ‖x_i‖²` for all `x`, because a matrix and its adjoint have
the same norm.

## Main results

* `sum_normSq_adjoint_le` — **the duality principle**: a bound with constant `C` for a finite
  matrix gives the same bound for its adjoint.
* `large_sieve_dual` — **the dual large sieve**: for points `t i` pairwise `δ`-separated modulo
  one, `∑_{n < N} ‖∑_i x i e(n t i)‖² ≤ (δ⁻¹ + π N) ∑_i ‖x i‖²`.
* `large_sieve_dual_farey` — the same at the Farey fractions of order `Q`, with constant
  `Q² + π N`.

## Scope

The constants are those of `RiemannHypothesis.LargeSieveGallagher`, so they carry the same factor
`π` on the `N` term and are not sharp.  As there, the statements are about exponential sums; no
consequence for `ζ` is drawn.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveDual

open KusminLandau LargeSieve LargeSieveGallagher LargeSieveFarey

/-! ## The duality principle -/

/-- `‖z‖²`, as a complex number, is `conj z * z`. -/
private theorem normSq_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
  simp [Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_norm_sq]

/-- **The duality principle for a finite matrix.**  If the linear map `a ↦ (∑_n a n φ i n)_i`
has norm squared at most `C`, then so does its adjoint `x ↦ (∑_i x i conj (φ i n))_n`. -/
theorem sum_normSq_adjoint_le {ι κ : Type*} {s : Finset ι} {u : Finset κ}
    (phi : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a : κ → ℂ, ∑ i ∈ s, ‖∑ n ∈ u, a n * phi i n‖ ^ 2 ≤ C * ∑ n ∈ u, ‖a n‖ ^ 2)
    (x : ι → ℂ) :
    ∑ n ∈ u, ‖∑ i ∈ s, x i * (starRingEnd ℂ) (phi i n)‖ ^ 2 ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  set b : κ → ℂ := fun n => ∑ i ∈ s, x i * (starRingEnd ℂ) (phi i n) with hb
  set A : ι → ℂ := fun i => ∑ n ∈ u, b n * phi i n with hA
  set S : ℝ := ∑ n ∈ u, ‖b n‖ ^ 2 with hS
  set X : ℝ := ∑ i ∈ s, ‖x i‖ ^ 2 with hX
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => by positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => by positivity
  -- the key algebraic identity: `S = ∑_i x i conj (A i)`
  have hkey : (S : ℂ) = ∑ i ∈ s, x i * (starRingEnd ℂ) (A i) := by
    have h1 : (S : ℂ) = ∑ n ∈ u, (starRingEnd ℂ) (b n) * b n := by
      rw [hS, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun n _ => normSq_cast (b n)
    rw [h1]
    have h2 : ∀ n ∈ u, (starRingEnd ℂ) (b n) * b n
        = ∑ i ∈ s, x i * ((starRingEnd ℂ) (b n) * (starRingEnd ℂ) (phi i n)) := by
      intro n _
      rw [hb]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [map_mul]
  -- Cauchy–Schwarz
  have hCS : S ≤ Real.sqrt X * Real.sqrt (∑ i ∈ s, ‖A i‖ ^ 2) := by
    have h1 : S = ‖(S : ℂ)‖ := by
      rw [Complex.norm_real]
      exact (abs_of_nonneg hS0).symm
    have h2 : ‖(S : ℂ)‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖A i‖ := by
      rw [hkey]
      refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_mul, RCLike.norm_conj]
    have h3 : (∑ i ∈ s, ‖x i‖ * ‖A i‖) ≤ Real.sqrt X * Real.sqrt (∑ i ∈ s, ‖A i‖ ^ 2) := by
      have hsq := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖x i‖) (fun i => ‖A i‖)
      have hA0 : 0 ≤ ∑ i ∈ s, ‖A i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      have hprod : Real.sqrt X * Real.sqrt (∑ i ∈ s, ‖A i‖ ^ 2)
          = Real.sqrt (X * ∑ i ∈ s, ‖A i‖ ^ 2) := (Real.sqrt_mul hX0 _).symm
      rw [hprod]
      have hle : (∑ i ∈ s, ‖x i‖ * ‖A i‖) ^ 2 ≤ X * ∑ i ∈ s, ‖A i‖ ^ 2 := hsq
      calc (∑ i ∈ s, ‖x i‖ * ‖A i‖)
          ≤ Real.sqrt ((∑ i ∈ s, ‖x i‖ * ‖A i‖) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
        _ ≤ Real.sqrt (X * ∑ i ∈ s, ‖A i‖ ^ 2) := Real.sqrt_le_sqrt hle
    exact h1.trans_le (h2.trans h3)
  -- the hypothesis applied to the coefficients `b`
  have hAb : ∑ i ∈ s, ‖A i‖ ^ 2 ≤ C * S := h b
  -- conclude
  rcases eq_or_lt_of_le hS0 with hzero | hpos
  · rw [← hzero]
    positivity
  · have hsq : S * S ≤ X * (C * S) := by
      have h1 : Real.sqrt X * Real.sqrt (∑ i ∈ s, ‖A i‖ ^ 2) ≤ Real.sqrt X * Real.sqrt (C * S) :=
        by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          exact Real.sqrt_le_sqrt hAb
      have h2 : S ≤ Real.sqrt (X * (C * S)) := by
        calc S ≤ Real.sqrt X * Real.sqrt (∑ i ∈ s, ‖A i‖ ^ 2) := hCS
          _ ≤ Real.sqrt X * Real.sqrt (C * S) := h1
          _ = Real.sqrt (X * (C * S)) := (Real.sqrt_mul hX0 _).symm
      have h3 : S ^ 2 ≤ X * (C * S) := by
        have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ X * (C * S))
        nlinarith [Real.sqrt_nonneg (X * (C * S))]
      nlinarith
    have : S ≤ C * X := by
      rw [mul_comm X (C * S)] at hsq
      nlinarith
    exact this

/-! ## The dual large sieve -/

/-- **The dual large sieve.**  For points `t i` that are pairwise `δ`-separated modulo one,
`∑_{n < N} ‖∑_i x i e(n t i)‖² ≤ (δ⁻¹ + π N) ∑_i ‖x i‖²`. -/
theorem large_sieve_dual {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  have hC : (0 : ℝ) ≤ δ⁻¹ + Real.pi * N := by positivity
  have hmain := sum_normSq_adjoint_le (s := s) (u := range N)
    (fun i n => e2pi ((n : ℝ) * t i)) hC
    (fun a => large_sieve_gallagher hδ hδ2 hsep a N)
    (fun i => (starRingEnd ℂ) (x i))
  refine le_trans (le_of_eq ?_) (le_trans hmain (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    have : ∑ i ∈ s, (starRingEnd ℂ) (x i) * (starRingEnd ℂ) (e2pi ((n : ℝ) * t i))
        = (starRingEnd ℂ) (∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm
    rw [this, RCLike.norm_conj]
  · exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_conj])

/-- The dual large sieve at the Farey fractions of order `Q`. -/
theorem large_sieve_dual_farey {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ y ∈ s, y ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ y ∈ s, y.den ≤ Q)
    (x : ℚ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ y ∈ s, x y * e2pi ((n : ℝ) * (y : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ y ∈ s, ‖x y‖ ^ 2 := by
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hδ : (0 : ℝ) < 1 / ((Q : ℝ) ^ 2) := by positivity
  have hδ2 : 1 / ((Q : ℝ) ^ 2) ≤ 1 / 2 := by
    have h4 : (2 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) h4
  have hinv : (1 / ((Q : ℝ) ^ 2))⁻¹ = (Q : ℝ) ^ 2 := by rw [one_div, inv_inv]
  have hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z →
      1 / ((Q : ℝ) ^ 2) ≤ intDist ((y : ℝ) - (z : ℝ)) := fun y hy z hz hyz =>
    inv_sq_le_intDist_sub (hmem y hy) (hmem z hz) (hden y hy) (hden z hz) hyz
  have := large_sieve_dual (s := s) (t := fun y : ℚ => (y : ℝ)) hδ hδ2 hsep x N
  rwa [hinv] at this

end LargeSieveDual

end RiemannHypothesis

end
