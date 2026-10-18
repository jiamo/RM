/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.HilbertCosecantWeighted
import RiemannHypothesis.LargeSieveMV

/-!
# The weighted large sieve

For points `t_i`, `i ∈ s`, with local spacings `0 < δ_i ≤ intDist (t_i − t_j)` (`j ≠ i`), and
coefficients `a_0, …, a_{N−1}`,

  `∑_i (N + (5 √2 / π) δ_i⁻¹)⁻¹ ‖∑_{n<N} a_n e(n t_i)‖² ≤ ∑_{n<N} ‖a_n‖²`
  (`large_sieve_weighted`).

This is the weighted large sieve of Montgomery and Vaughan (*Hilbert's inequality*, 1974), who
have `3/2` in place of `5 √2 / π ≈ 2.251`; it is the input of their Brun–Titchmarsh theorem in
progressions, which is not proved here.  The proof follows `LargeSieveMV.large_sieve_mv`:

* `large_sieve_weighted_dual` — expanding the square, the diagonal gives `N ∑ ‖x_i‖²` and the
  off-diagonal part is `(H(v) − H(w)) / (2i)` with `H` the cosecant form
  (`LargeSieveMV.kernel_mul_two_I_sin`); `weightedCosecantInequality_finset` bounds each of
  `‖H(v)‖`, `‖H(w)‖` by `(5 √2/π) ∑ ‖x_i‖²/δ_i`, so
  `∑_{n<N} ‖∑_i x_i e(n t_i)‖² ≤ ∑_i (N + (5 √2/π) δ_i⁻¹) ‖x_i‖²`;
* `large_sieve_weighted` — the duality principle `LargeSieveDual.sum_normSq_adjoint_le` with
  constant `1`, applied to the kernel `(N + (5 √2/π) δ_i⁻¹)^{−1/2} e(−n t_i)`.

No new hypothesis is assumed, and nothing about `ζ` is claimed.
-/

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveWeighted

open KusminLandau LargeSieve LargeSieveDual LargeSieveMV HilbertCosecant
  HilbertCosecantWeighted

/-- **The dual weighted large sieve.**  For points `t i` with local spacings
`δ_i ≤ intDist (t_i − t_j)` (`j ≠ i`),
`∑_{n<N} ‖∑_i x_i e(n t_i)‖² ≤ ∑_i (N + (5 √2 / π) δ_i⁻¹) ‖x_i‖²`. -/
theorem large_sieve_weighted_dual {ι : Type*} {s : Finset ι} {t δ : ι → ℝ}
    (hδ : ∀ i ∈ s, 0 < δ i) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ∑ i ∈ s, ((N : ℝ) + 5 * Real.sqrt 2 / Real.pi / δ i) * ‖x i‖ ^ 2 := by
  classical
  set C : ℝ := 5 * Real.sqrt 2 / Real.pi with hCdef
  set X : ℝ := ∑ i ∈ s, ‖x i‖ ^ 2 with hX
  set Y : ℝ := ∑ i ∈ s, ‖x i‖ ^ 2 / δ i with hY
  set H : (ι → ℂ) → ℂ := fun y => ∑ i ∈ s, ∑ j ∈ s.erase i,
    y i * (starRingEnd ℂ) (y j) / (Real.sin (Real.pi * (t i - t j)) : ℂ) with hH
  set v : ι → ℂ := fun i => x i * e2pi (((N : ℝ) - 1 / 2) * t i) with hv
  set w : ι → ℂ := fun i => x i * e2pi (-(t i / 2)) with hw
  have hnv : ∑ i ∈ s, ‖v i‖ ^ 2 / δ i = Y := by
    simp only [hv, norm_mul, norm_e2pi, mul_one, hY]
  have hnw : ∑ i ∈ s, ‖w i‖ ^ 2 / δ i = Y := by
    simp only [hw, norm_mul, norm_e2pi, mul_one, hY]
  have hHv : ‖H v‖ ≤ C * Y := by
    have := weightedCosecantInequality_finset s t δ v hδ hsep
    rwa [hnv] at this
  have hHw : ‖H w‖ ≤ C * Y := by
    have := weightedCosecantInequality_finset s t δ w hδ hsep
    rwa [hnw] at this
  have hexp : ∀ n : ℕ, ((‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s,
          x i * (starRingEnd ℂ) (x j) * e2pi ((n : ℝ) * (t i - t j)) := by
    intro n
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, LargeSieve.conj_e2pi, mul_sub, sub_eq_add_neg, e2pi_add]
    ring_nf
  have hsumexp :
      ((∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j) := by
    push_cast
    simp only [← Complex.ofReal_pow, hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold kernel
    rw [Finset.mul_sum]
  have hoff : ∀ i ∈ s, ∀ j ∈ s.erase i,
      x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j)
        = (v i * (starRingEnd ℂ) (v j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)
          - w i * (starRingEnd ℂ) (w j) / (Real.sin (Real.pi * (t i - t j)) : ℂ))
            / (2 * I) := by
    intro i hi j hj
    have hij : j ≠ i := Finset.ne_of_mem_erase hj
    have hsin : (Real.sin (Real.pi * (t i - t j)) : ℂ) ≠ 0 := by
      exact_mod_cast sin_pi_mul_ne_zero_of_ne_int
        (ne_int_of_le_intDist (hδ i hi) (hsep i hi j (Finset.mem_of_mem_erase hj) hij.symm))
    have hk := kernel_mul_two_I_sin N (t i - t j)
    have hvv : v i * (starRingEnd ℂ) (v j)
        = x i * (starRingEnd ℂ) (x j) * e2pi (((N : ℝ) - 1 / 2) * (t i - t j)) := by
      simp only [hv, map_mul, LargeSieve.conj_e2pi]
      rw [show ((N : ℝ) - 1 / 2) * (t i - t j)
          = ((N : ℝ) - 1 / 2) * t i + -(((N : ℝ) - 1 / 2) * t j) by ring, e2pi_add]
      ring
    have hww : w i * (starRingEnd ℂ) (w j)
        = x i * (starRingEnd ℂ) (x j) * e2pi (-((t i - t j) / 2)) := by
      simp only [hw, map_mul, LargeSieve.conj_e2pi]
      rw [show -((t i - t j) / 2) = -(t i / 2) + - -(t j / 2) by ring, e2pi_add]
      ring
    have h2I : (2 * I : ℂ) ≠ 0 := by simp
    rw [hvv, hww, ← sub_div, div_div, eq_div_iff (mul_ne_zero hsin h2I)]
    linear_combination (x i * (starRingEnd ℂ) (x j)) * hk
  have hdiag : ∀ i ∈ s, x i * (starRingEnd ℂ) (x i) * kernel N (t i - t i)
      = (N : ℂ) * ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    intro i _
    rw [sub_self, kernel_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    ring
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j)
      = (N : ℂ) * (X : ℂ) + (H v - H w) / (2 * I) := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j)
        = (N : ℂ) * ((‖x i‖ ^ 2 : ℝ) : ℂ)
          + ∑ j ∈ s.erase i, x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j) := by
      intro i hi
      rw [← Finset.add_sum_erase _ _ hi, hdiag i hi]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, hX,
      Complex.ofReal_sum]
    congr 1
    rw [hH, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j hj => hoff i hi j hj
  have hre := congrArg Complex.re (hsumexp.trans hsplit)
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have hreN : ((N : ℂ) * (X : ℂ)).re = (N : ℝ) * X := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.add_re, hreN]
  have hbound : ((H v - H w) / (2 * I)).re ≤ C * Y := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    have := norm_sub_le (H v) (H w)
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have hsum : ∑ i ∈ s, ((N : ℝ) + C / δ i) * ‖x i‖ ^ 2 = (N : ℝ) * X + C * Y := by
    rw [hX, hY, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  linarith

/-- **The weighted large sieve** (Montgomery–Vaughan form, constant `5 √2 / π`).  For points
`t i` with local spacings `0 < δ_i ≤ intDist (t_i − t_j)` (`j ≠ i`),
`∑_i (N + (5 √2 / π) δ_i⁻¹)⁻¹ ‖∑_{n<N} a_n e(n t_i)‖² ≤ ∑_{n<N} ‖a_n‖²`.
Montgomery and Vaughan have `3/2` in place of `5 √2 / π ≈ 2.251`. -/
theorem large_sieve_weighted {ι : Type*} {s : Finset ι} {t δ : ι → ℝ}
    (hδ : ∀ i ∈ s, 0 < δ i) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ((N : ℝ) + 5 * Real.sqrt 2 / Real.pi / δ i)⁻¹
        * ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  classical
  set C : ℝ := 5 * Real.sqrt 2 / Real.pi with hCdef
  have hC0 : 0 ≤ C := by positivity
  set c : ι → ℝ := fun i => (N : ℝ) + C / δ i with hc
  set w : ι → ℝ := fun i => Real.sqrt (c i)⁻¹ with hw
  have hcpos : ∀ i ∈ s, 0 < c i := fun i hi => by
    have : 0 < C / δ i := div_pos (by positivity) (hδ i hi)
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) this
  have hw2 : ∀ i ∈ s, w i ^ 2 = (c i)⁻¹ := fun i hi =>
    Real.sq_sqrt (inv_nonneg.mpr (hcpos i hi).le)
  have hsep' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist ((-t i) - (-t j)) := by
    intro i hi j hj hij
    rw [show (-t i) - (-t j) = -(t i - t j) by ring, intDist_neg]
    exact hsep i hi j hj hij
  have hmain := sum_normSq_adjoint_le (s := range N) (u := s)
    (fun n i => (w i : ℂ) * (starRingEnd ℂ) (e2pi ((n : ℝ) * t i))) zero_le_one
    (fun x => by
      have h := large_sieve_weighted_dual (s := s) (t := fun i => -t i) hδ hsep'
        (fun i => x i * (w i : ℂ)) N
      refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
      · refine Finset.sum_congr rfl fun n _ => ?_
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LargeSieve.conj_e2pi, mul_neg]
        ring
      · rw [one_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hw2 i hi]
        have hci : c i = (N : ℝ) + 5 * Real.sqrt 2 / Real.pi / δ i := rfl
        have hne : c i ≠ 0 := (hcpos i hi).ne'
        rw [← hci]
        field_simp)
    a
  rw [one_mul] at hmain
  refine le_trans (le_of_eq ?_) hmain
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsum : ∑ n ∈ range N, a n * (starRingEnd ℂ)
        ((w i : ℂ) * (starRingEnd ℂ) (e2pi ((n : ℝ) * t i)))
      = (w i : ℂ) * ∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hw2 i hi]

end LargeSieveWeighted

end RiemannHypothesis
