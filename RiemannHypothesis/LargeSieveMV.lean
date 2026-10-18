/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.HilbertCosecant
import RiemannHypothesis.LargeSieveDual

/-!
# The large sieve with the sharp constant `N + δ⁻¹`

For points `t_i` that are `δ`-separated modulo one (`0 < δ ≤ 1/2`) and coefficients
`a_0, …, a_{N-1}`,

  `∑_i ‖∑_{n<N} a_n e(n t_i)‖² ≤ (N + δ⁻¹) ∑_{n<N} ‖a_n‖²`.

This is the theorem of Montgomery and Vaughan (*The large sieve*, Mathematika 20 (1973),
119–134; Iwaniec–Kowalski, *Analytic Number Theory*, Theorem 7.7).  It replaces the constants
`δ⁻¹ + π N` of `LargeSieveGallagher.large_sieve_gallagher` and
`N + δ⁻¹ (1 + log (2δ)⁻¹)` of `LargeSieve.large_sieve`, under the same hypotheses.

## Proof

* By the duality principle `LargeSieveDual.sum_normSq_adjoint_le` it suffices to bound
  `∑_{n<N} ‖∑_i x_i e(n t_i)‖²` (`large_sieve_mv_dual`).
* Expanding the square, the diagonal gives `N ∑ ‖x_i‖²`.  Off the diagonal,
  `∑_{n<N} e(nβ) · 2i sin πβ = e((N − 1/2)β) − e(−β/2)` (`kernel_mul_two_I_sin`),
  so the off-diagonal part is `(H(v) − H(w)) / (2i)`, with
  `H(y) = ∑_{i ≠ j} y_i conj(y_j) csc π(t_i − t_j)`, `v_i = x_i e((N − 1/2) t_i)` and
  `w_i = x_i e(−t_i/2)`.
* The cosecant inequality `HilbertCosecant.cosecantHilbertInequality_finset` bounds each
  of `‖H(v)‖`, `‖H(w)‖` by `δ⁻¹ ∑ ‖x_i‖²`, so the off-diagonal part is at most
  `δ⁻¹ ∑ ‖x_i‖²`.

## Main results

* `RiemannHypothesis.LargeSieveMV.large_sieve_mv` — the large sieve with the constant
  `N + δ⁻¹`.
* `RiemannHypothesis.LargeSieveMV.large_sieve_mv_dual` — its dual form.
* `RiemannHypothesis.LargeSieveMV.admissibleConstant_large_sieve_mv` — `N + δ⁻¹` is an
  `AdmissibleConstant`.

Selberg's constant `N − 1 + δ⁻¹` is not proved here.  No hypothesis is assumed, and nothing
about `ζ` is claimed.
-/

open Complex Finset

namespace RiemannHypothesis

namespace LargeSieveMV

open KusminLandau LargeSieve LargeSieveDual HilbertCosecant

/-- `2 i sin πβ = e(β/2) − e(−β/2)`. -/
theorem two_I_mul_sin (β : ℝ) :
    2 * I * (Real.sin (Real.pi * β) : ℂ) = e2pi (β / 2) - e2pi (-(β / 2)) := by
  unfold e2pi
  rw [Complex.ofReal_sin, Complex.sin]
  push_cast
  have h1 : (2 * (Real.pi : ℂ) * (β / 2)) * I = (Real.pi : ℂ) * β * I := by ring
  have h2 : (2 * (Real.pi : ℂ) * -(β / 2)) * I = -((Real.pi : ℂ) * β * I) := by ring
  rw [h1, h2]
  have h3 : -((Real.pi : ℂ) * β) * I = -((Real.pi : ℂ) * β * I) := by ring
  rw [h3]
  linear_combination
    (Complex.exp (-((Real.pi : ℂ) * β * I)) - Complex.exp ((Real.pi : ℂ) * β * I))
      * Complex.I_sq

/-- **The Dirichlet kernel through the sine**:
`(∑_{n<N} e(nβ)) · 2 i sin πβ = e((N − 1/2)β) − e(−β/2)`. -/
theorem kernel_mul_two_I_sin (N : ℕ) (β : ℝ) :
    kernel N β * (2 * I * (Real.sin (Real.pi * β) : ℂ))
      = e2pi (((N : ℝ) - 1 / 2) * β) - e2pi (-(β / 2)) := by
  rw [two_I_mul_sin]
  have hgeom : kernel N β * (e2pi β - 1) = e2pi β ^ N - 1 := by
    unfold kernel
    simp only [e2pi_nat_mul]
    exact geom_sum_mul _ _
  have hsplit : e2pi (β / 2) - e2pi (-(β / 2)) = e2pi (-(β / 2)) * (e2pi β - 1) := by
    rw [mul_sub, ← e2pi_add, mul_one]
    ring_nf
  have hN : e2pi (((N : ℝ) - 1 / 2) * β) = e2pi (-(β / 2)) * e2pi β ^ N := by
    rw [← e2pi_nat_mul, ← e2pi_add]
    ring_nf
  rw [hsplit, hN]
  linear_combination e2pi (-(β / 2)) * hgeom

/-- **The dual form of the sharp large sieve.**  For points `t i` that are `δ`-separated modulo
one, `∑_{n<N} ‖∑_i x_i e(n t_i)‖² ≤ (N + δ⁻¹) ∑_i ‖x_i‖²`. -/
theorem large_sieve_mv_dual {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  set X : ℝ := ∑ i ∈ s, ‖x i‖ ^ 2 with hX
  -- the cosecant form of the bilinear form
  set H : (ι → ℂ) → ℂ := fun y => ∑ i ∈ s, ∑ j ∈ s.erase i,
    y i * (starRingEnd ℂ) (y j) / (Real.sin (Real.pi * (t i - t j)) : ℂ) with hH
  set v : ι → ℂ := fun i => x i * e2pi (((N : ℝ) - 1 / 2) * t i) with hv
  set w : ι → ℂ := fun i => x i * e2pi (-(t i / 2)) with hw
  have hnv : ∑ i ∈ s, ‖v i‖ ^ 2 = X := by
    simp only [hv, norm_mul, norm_e2pi, mul_one, hX]
  have hnw : ∑ i ∈ s, ‖w i‖ ^ 2 = X := by
    simp only [hw, norm_mul, norm_e2pi, mul_one, hX]
  have hHv : ‖H v‖ ≤ δ⁻¹ * X := by
    have := cosecantHilbertInequality_finset s t v hδ hδ2 hsep
    rwa [hnv] at this
  have hHw : ‖H w‖ ≤ δ⁻¹ * X := by
    have := cosecantHilbertInequality_finset s t w hδ hδ2 hsep
    rwa [hnw] at this
  -- expanding the square
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
  -- the off-diagonal terms through the sine
  have hoff : ∀ i ∈ s, ∀ j ∈ s.erase i,
      x i * (starRingEnd ℂ) (x j) * kernel N (t i - t j)
        = (v i * (starRingEnd ℂ) (v j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)
          - w i * (starRingEnd ℂ) (w j) / (Real.sin (Real.pi * (t i - t j)) : ℂ))
            / (2 * I) := by
    intro i hi j hj
    have hij : j ≠ i := Finset.ne_of_mem_erase hj
    have hsin : (Real.sin (Real.pi * (t i - t j)) : ℂ) ≠ 0 := by
      exact_mod_cast sin_pi_mul_ne_zero_of_ne_int
        (ne_int_of_le_intDist hδ (hsep i hi j (Finset.mem_of_mem_erase hj) hij.symm))
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
  -- the real part
  have hre := congrArg Complex.re (hsumexp.trans hsplit)
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have hreN : ((N : ℂ) * (X : ℂ)).re = (N : ℝ) * X := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.add_re, hreN]
  have hbound : ((H v - H w) / (2 * I)).re ≤ δ⁻¹ * X := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    have := norm_sub_le (H v) (H w)
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have : ((N : ℝ) + δ⁻¹) * X = (N : ℝ) * X + δ⁻¹ * X := by ring
  linarith

/-- **The large sieve inequality with the sharp constant `N + δ⁻¹`** (Montgomery–Vaughan).
For points `t i` that are `δ`-separated modulo one,
`∑_i ‖∑_{n<N} a_n e(n t_i)‖² ≤ (N + δ⁻¹) ∑_{n<N} ‖a_n‖²`.  The hypotheses are those of
`LargeSieveGallagher.large_sieve_gallagher`, so this is a drop-in replacement for it. -/
theorem large_sieve_mv {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  classical
  have hC : (0 : ℝ) ≤ (N : ℝ) + δ⁻¹ := by positivity
  have hsep' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist ((-t i) - (-t j)) := by
    intro i hi j hj hij
    rw [show (-t i) - (-t j) = -(t i - t j) by ring, intDist_neg]
    exact hsep i hi j hj hij
  have hmain := sum_normSq_adjoint_le (s := range N) (u := s)
    (fun n i => (starRingEnd ℂ) (e2pi ((n : ℝ) * t i))) hC
    (fun x => by
      have h := large_sieve_mv_dual hδ hδ2 hsep' x N
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LargeSieve.conj_e2pi, mul_neg])
    a
  refine le_trans (le_of_eq ?_) hmain
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.conj_conj]

/-- The constant `N + δ⁻¹` is an admissible large-sieve constant. -/
theorem admissibleConstant_large_sieve_mv : AdmissibleConstant (fun δ N => (N : ℝ) + δ⁻¹) :=
  fun hδ hδ2 hsep a N => large_sieve_mv hδ hδ2 hsep a N

end LargeSieveMV

end RiemannHypothesis
