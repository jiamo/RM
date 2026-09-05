/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib
import RiemannHypothesis.DirichletPolyMeanSquare

/-!
# The Halász–Montgomery inequality and large values of Dirichlet polynomials

The Halász–Montgomery inequality is the Bessel-type bound that converts *almost orthogonality*
into a large-values estimate: if `ξ` and `φ_1, …, φ_R` are vectors of a complex inner product
space, then

`∑_r |⟨φ_r, ξ⟩|² ≤ Δ ‖ξ‖²`,  where `Δ ≥ max_r ∑_s |⟨φ_r, φ_s⟩|`

is any bound for the row sums of the Gram matrix of the `φ_r`.  The proof is a duality argument:
`∑_r |⟨φ_r, ξ⟩|² = ⟨v, ξ⟩` for `v = ∑_r ⟨φ_r, ξ⟩ φ_r`, Cauchy–Schwarz bounds this by `‖v‖ ‖ξ‖`,
and expanding `‖v‖²` produces the Gram matrix, which the arithmetic-geometric mean inequality
(a Schur test) bounds by `Δ ∑_r |⟨φ_r, ξ⟩|²`.

## Main results

* `RiemannHypothesis.HalaszMontgomery.sum_normSq_le_of_rowSum_le` — the inequality in coordinate
  form, for finitely many vectors `φ i : κ → ℂ` and `ξ : κ → ℂ` indexed by a finite set of
  frequencies.  This is the form used elsewhere in the repository.
* `RiemannHypothesis.HalaszMontgomery.halasz_montgomery` — the same inequality in an arbitrary
  complex inner product space.
* `RiemannHypothesis.HalaszMontgomery.sum_normSq_dirichletPoly_le` — the specialization to a
  Dirichlet polynomial `D(t) = ∑_{n ≤ N} a_n n^{-it}` sampled at points `t_r`: the Gram matrix is
  the matrix of the sums `∑_{n ≤ N} n^{i(t_s − t_r)}`, so

      `∑_r |D(t_r)|² ≤ Δ ∑_{n ≤ N} |a_n|²`  whenever  `∑_s |∑_{n ≤ N} n^{i(t_s − t_r)}| ≤ Δ`.

* `RiemannHypothesis.HalaszMontgomery.card_le_of_dirichletPoly_large` — the resulting **large
  values estimate**: the number of sampled points at which `|D(t_r)| ≥ V` is at most
  `Δ (∑_n |a_n|²) / V²`.

* `RiemannHypothesis.HalaszMontgomery.exists_sharp_rowSum`,
  `RiemannHypothesis.HalaszMontgomery.largeValues_constant_ge_one` — **the ceiling**: the
  orthonormal configuration attains the inequality, so no constant better than `1` is admissible
  in the large-values bound.  Improving the count therefore requires more information about the
  vectors than a bound on the Gram row sums.

Bounding the Gram row sums `∑_s |∑_{n ≤ N} n^{i(t_s − t_r)}|` for separated points `t_r` is a
separate matter and is not carried out here; the results above take that bound as a hypothesis.
No consequence for `ζ` is drawn in this file.
-/

open Finset Complex
open scoped InnerProductSpace

namespace RiemannHypothesis

namespace HalaszMontgomery

/-- `‖z‖²`, as a complex number, is `z · conj z`. -/
theorem ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']
  norm_cast

/-! ## The inequality in coordinate form -/

/-- **The Halász–Montgomery inequality**, in coordinate form.  For vectors `φ i` and `ξ` in `ℂ^m`,

`∑_i |⟨φ i, ξ⟩|² ≤ Δ ∑_n |ξ n|²`

whenever `Δ` bounds every row sum `∑_j |⟨φ i, φ j⟩|` of the Gram matrix. -/
theorem sum_normSq_le_of_rowSum_le {ι κ : Type*} (s : Finset ι) (m : Finset κ)
    (φ : ι → κ → ℂ) (ξ : κ → ℂ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * φ j n‖ ≤ Δ) :
    ∑ i ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * ξ n‖ ^ 2 ≤ Δ * ∑ n ∈ m, ‖ξ n‖ ^ 2 := by
  classical
  set S : ι → ℂ := fun i => ∑ n ∈ m, (starRingEnd ℂ) (φ i n) * ξ n with hS
  set G : ι → ι → ℂ := fun i j => ∑ n ∈ m, (starRingEnd ℂ) (φ i n) * φ j n with hG
  set c : ι → ℂ := fun i => (starRingEnd ℂ) (S i) with hc
  set Q : ℝ := ∑ i ∈ s, ‖S i‖ ^ 2 with hQ
  set A : ℝ := ∑ n ∈ m, ‖ξ n‖ ^ 2 with hA
  set B : κ → ℂ := fun n => ∑ i ∈ s, c i * (starRingEnd ℂ) (φ i n) with hB
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => sq_nonneg _
  -- the duality identity
  have claim1 : (Q : ℂ) = ∑ n ∈ m, ξ n * B n := by
    have hQc : (Q : ℂ) = ∑ i ∈ s, c i * S i := by
      rw [hQ, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, ofReal_normSq]
      ring
    rw [hQc, hB, hS]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring
  -- the Gram bound
  have claim3 : ∑ n ∈ m, ‖B n‖ ^ 2 ≤ Δ * Q := by
    have hXc : ((∑ n ∈ m, ‖B n‖ ^ 2 : ℝ) : ℂ)
        = ∑ i ∈ s, ∑ j ∈ s, c i * (starRingEnd ℂ) (c j) * G i j := by
      have h1 : ∀ n ∈ m, ((‖B n‖ ^ 2 : ℝ) : ℂ)
          = ∑ i ∈ s, ∑ j ∈ s, c i * (starRingEnd ℂ) (c j)
              * ((starRingEnd ℂ) (φ i n) * φ j n) := by
        intro n _
        rw [ofReal_normSq, hB, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul, Complex.conj_conj]
        ring
      rw [Complex.ofReal_sum, Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG, Finset.mul_sum]
    have hX0 : (0 : ℝ) ≤ ∑ n ∈ m, ‖B n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
    have hXle : ∑ n ∈ m, ‖B n‖ ^ 2 ≤ ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ * ‖c j‖ * ‖G i j‖ := by
      have h1 : ∑ n ∈ m, ‖B n‖ ^ 2 = ‖((∑ n ∈ m, ‖B n‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
      rw [h1, hXc]
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      exact le_of_eq (by simp only [norm_mul, RCLike.norm_conj])
    refine hXle.trans ?_
    have hsymm : ∀ i j : ι, ‖G i j‖ = ‖G j i‖ := by
      intro i j
      have hji : G j i = (starRingEnd ℂ) (G i j) := by
        rw [hG, map_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [map_mul, Complex.conj_conj]
        ring
      rw [hji, RCLike.norm_conj]
    have hcnorm : ∀ i : ι, ‖c i‖ = ‖S i‖ := fun i => by rw [hc]; exact RCLike.norm_conj _
    have hAM : ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ * ‖c j‖ * ‖G i j‖
        ≤ ∑ i ∈ s, ∑ j ∈ s, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖G i j‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      have h1 : ‖c i‖ * ‖c j‖ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    refine hAM.trans ?_
    have hsplit : ∑ i ∈ s, ∑ j ∈ s, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖G i j‖
        = (∑ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖G i j‖)
          + ∑ i ∈ s, ∑ j ∈ s, (‖c j‖ ^ 2 / 2) * ‖G i j‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit]
    have hQsum : ∑ i ∈ s, ‖c i‖ ^ 2 / 2 = Q / 2 := by
      rw [hQ, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hcnorm i]
    have hfirst : ∑ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖G i j‖ ≤ Δ * Q / 2 := by
      have hstep : ∀ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖G i j‖ ≤ (‖c i‖ ^ 2 / 2) * Δ := by
        intro i hi
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hΔ i hi) (by positivity)
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.sum_mul, hQsum]
      ring_nf
      exact le_rfl
    have hsecond : ∑ i ∈ s, ∑ j ∈ s, (‖c j‖ ^ 2 / 2) * ‖G i j‖ ≤ Δ * Q / 2 := by
      rw [Finset.sum_comm]
      have hstep : ∀ j ∈ s, ∑ i ∈ s, (‖c j‖ ^ 2 / 2) * ‖G i j‖ ≤ (‖c j‖ ^ 2 / 2) * Δ := by
        intro j hj
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hrw : ∑ i ∈ s, ‖G i j‖ = ∑ i ∈ s, ‖G j i‖ :=
          Finset.sum_congr rfl fun i _ => hsymm i j
        rw [hrw]
        exact hΔ j hj
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.sum_mul, hQsum]
      ring_nf
      exact le_rfl
    linarith
  -- Cauchy–Schwarz and the conclusion
  have hfinal : Q ^ 2 ≤ (A * Δ) * Q := by
    have h1 : Q ≤ ∑ n ∈ m, ‖ξ n‖ * ‖B n‖ := by
      have h2 : Q = ‖((Q : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
      rw [h2, claim1]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun n _ => by rw [norm_mul]
    have h3 : (∑ n ∈ m, ‖ξ n‖ * ‖B n‖) ^ 2 ≤ A * ∑ n ∈ m, ‖B n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h6 : Q ^ 2 ≤ (∑ n ∈ m, ‖ξ n‖ * ‖B n‖) ^ 2 := by
      have hnn : 0 ≤ ∑ n ∈ m, ‖ξ n‖ * ‖B n‖ := Finset.sum_nonneg fun n _ => by positivity
      nlinarith
    nlinarith [claim3, hA0]
  rcases eq_or_lt_of_le hQ0 with h | h
  · rw [← h]
    exact mul_nonneg hΔ0 hA0
  · nlinarith [hfinal, h]

/-! ## The inequality in a Hilbert space -/

/-- **The Halász–Montgomery inequality** in a complex inner product space: if `Δ` bounds the row
sums `∑_j ‖⟪φ i, φ j⟫‖` of the Gram matrix of the vectors `φ i`, then
`∑_i ‖⟪φ i, ξ⟫‖² ≤ Δ ‖ξ‖²` for every vector `ξ`. -/
theorem halasz_montgomery {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (φ : ι → E) (ξ : E) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖⟪φ i, φ j⟫_ℂ‖ ≤ Δ) :
    ∑ i ∈ s, ‖⟪φ i, ξ⟫_ℂ‖ ^ 2 ≤ Δ * ‖ξ‖ ^ 2 := by
  classical
  set c : ι → ℂ := fun i => ⟪φ i, ξ⟫_ℂ with hc
  set Q : ℝ := ∑ i ∈ s, ‖c i‖ ^ 2 with hQ
  set v : E := ∑ i ∈ s, c i • φ i with hv
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQv : (Q : ℂ) = ⟪v, ξ⟫_ℂ := by
    rw [hv, sum_inner, hQ]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, ← Complex.mul_conj']
    ring
  have hnv : Q ≤ ‖v‖ * ‖ξ‖ := by
    have h1 : Q = ‖(Q : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
    rw [h1, hQv]
    exact norm_inner_le_norm _ _
  have hvv : ‖v‖ ^ 2 ≤ Δ * Q := by
    have hexp : ((‖v‖ ^ 2 : ℝ) : ℂ)
        = ∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j * ⟪φ i, φ j⟫_ℂ := by
      have hself : ((‖v‖ ^ 2 : ℝ) : ℂ) = ⟪v, v⟫_ℂ := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      rw [hself, hv, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right]
      ring
    have hle : ‖v‖ ^ 2 ≤ ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖ := by
      have h1 : ‖v‖ ^ 2 = ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, hexp]
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      exact le_of_eq (by simp only [norm_mul, RCLike.norm_conj])
    refine hle.trans ?_
    have hsymm : ∀ i j : ι, ‖⟪φ i, φ j⟫_ℂ‖ = ‖⟪φ j, φ i⟫_ℂ‖ := by
      intro i j
      rw [← inner_conj_symm (𝕜 := ℂ), RCLike.norm_conj]
    have hAM : ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖
        ≤ ∑ i ∈ s, ∑ j ∈ s, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖⟪φ i, φ j⟫_ℂ‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      have h1 : ‖c i‖ * ‖c j‖ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    refine hAM.trans ?_
    have hsplit : ∑ i ∈ s, ∑ j ∈ s, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖⟪φ i, φ j⟫_ℂ‖
        = (∑ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖)
          + ∑ i ∈ s, ∑ j ∈ s, (‖c j‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit]
    have hfirst : ∑ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ ≤ Δ * Q / 2 := by
      have hstep : ∀ i ∈ s, ∑ j ∈ s, (‖c i‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ ≤ (‖c i‖ ^ 2 / 2) * Δ := by
        intro i hi
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hΔ i hi) (by positivity)
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.sum_mul]
      have hhalf : ∑ i ∈ s, ‖c i‖ ^ 2 / 2 = Q / 2 := by rw [hQ, Finset.sum_div]
      rw [hhalf]
      ring_nf
      exact le_rfl
    have hsecond : ∑ i ∈ s, ∑ j ∈ s, (‖c j‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ ≤ Δ * Q / 2 := by
      rw [Finset.sum_comm]
      have hstep : ∀ j ∈ s, ∑ i ∈ s, (‖c j‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ ≤ (‖c j‖ ^ 2 / 2) * Δ := by
        intro j hj
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hrw : ∑ i ∈ s, ‖⟪φ i, φ j⟫_ℂ‖ = ∑ i ∈ s, ‖⟪φ j, φ i⟫_ℂ‖ :=
          Finset.sum_congr rfl fun i _ => hsymm i j
        rw [hrw]
        exact hΔ j hj
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.sum_mul]
      have hhalf : ∑ j ∈ s, ‖c j‖ ^ 2 / 2 = Q / 2 := by rw [hQ, Finset.sum_div]
      rw [hhalf]
      ring_nf
      exact le_rfl
    linarith
  have hQsq : Q ^ 2 ≤ (Δ * Q) * ‖ξ‖ ^ 2 := by
    have h1 : Q ^ 2 ≤ (‖v‖ * ‖ξ‖) ^ 2 := by nlinarith [hQ0, norm_nonneg v, norm_nonneg ξ]
    calc Q ^ 2 ≤ (‖v‖ * ‖ξ‖) ^ 2 := h1
      _ = ‖v‖ ^ 2 * ‖ξ‖ ^ 2 := by ring
      _ ≤ (Δ * Q) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hvv (sq_nonneg _)
  rcases eq_or_lt_of_le hQ0 with h | h
  · rw [← h]
    positivity
  · nlinarith [hQsq, h]

/-! ## Large values of Dirichlet polynomials -/

/-- For a positive integer `n`, the complex logarithm of `n` is the real logarithm. -/
theorem log_natCast (n : ℕ) : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by positivity)]

/-- Conjugating `n^{iu}` inverts the exponent: `conj (n^{iu}) = n^{-iu}`. -/
theorem conj_cpow_I_mul {n : ℕ} (hn : 0 < n) (u : ℝ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (Complex.I * (u : ℂ))) = (n : ℂ) ^ (-((u : ℂ) * Complex.I)) := by
  have hne : (n : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_conj,
    log_natCast]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The Gram entries of the vectors `n ↦ n^{i t}`: `conj (n^{i u}) · n^{i v} = n^{i (v − u)}`. -/
theorem conj_cpow_mul_cpow {n : ℕ} (hn : 0 < n) (u v : ℝ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (Complex.I * (u : ℂ))) * (n : ℂ) ^ (Complex.I * (v : ℂ))
      = (n : ℂ) ^ (Complex.I * ((v - u : ℝ) : ℂ)) := by
  have hne : (n : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [conj_cpow_I_mul hn u, Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
    Complex.cpow_def_of_ne_zero hne, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The Halász–Montgomery large-values inequality for Dirichlet polynomials.**  If `Δ` bounds
the row sums `∑_j ‖∑_{n ≤ N} n^{i(t_j − t_i)}‖`, then the values of the Dirichlet polynomial
`D(t) = ∑_{n ≤ N} a_n n^{-it}` at the sampled points satisfy
`∑_i |D(t_i)|² ≤ Δ ∑_{n ≤ N} |a_n|²`. -/
theorem sum_normSq_dirichletPoly_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ℕ → ℂ) (N : ℕ)
    {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s,
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ ≤ Δ) :
    ∑ i ∈ s, ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖ ^ 2
      ≤ Δ * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  set φ : ι → ℕ → ℂ := fun i n => (n : ℂ) ^ (Complex.I * (t i : ℂ)) with hφ
  have hval : ∀ i : ι, ∑ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (φ i n) * a n
      = dirichletPoly a N ((t i : ℂ) * Complex.I) := by
    intro i
    rw [dirichletPoly]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [hφ, conj_cpow_I_mul hn1]
    ring
  have hgram : ∀ i j : ι, ∑ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (φ i n) * φ j n
      = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ)) := by
    intro i j
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
    exact conj_cpow_mul_cpow hn1 (t i) (t j)
  have h := sum_normSq_le_of_rowSum_le s (Finset.Icc 1 N) φ a hΔ0
    (by
      intro i hi
      have hrw : ∀ j : ι, ‖∑ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (φ i n) * φ j n‖
          = ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ :=
        fun j => by rw [hgram i j]
      rw [Finset.sum_congr rfl (fun j _ => hrw j)]
      exact hΔ i hi)
  rw [Finset.sum_congr rfl (fun i _ => by rw [hval i])] at h
  exact h

/-- **The large-values estimate.**  If a Dirichlet polynomial of length `N` with coefficients `a`
has `|D(t_i)| ≥ V > 0` at each of the sampled points, then the number of points is at most
`Δ (∑_{n ≤ N} |a_n|²) / V²`, where `Δ` bounds the Gram row sums. -/
theorem card_le_of_dirichletPoly_large {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ℕ → ℂ) (N : ℕ)
    {Δ V : ℝ} (hΔ0 : 0 ≤ Δ) (hV : 0 < V)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s,
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ ≤ Δ)
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖) :
    (s.card : ℝ) ≤ Δ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / V ^ 2 := by
  have hsum := sum_normSq_dirichletPoly_le s t a N hΔ0 hΔ
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ i ∈ s, ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _i ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖ ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hbig i hi
          nlinarith [hV.le, norm_nonneg (dirichletPoly a N ((t i : ℂ) * Complex.I))]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-! ## Sharpness

The inequality cannot be improved: the orthonormal configuration attains it, with `Δ = 1`.  So
the large-values bound `R ≤ Δ (∑ |a_n|²) / V²` is exactly the best that follows from a bound on
the Gram row sums alone — any further gain has to come from extra information about the
vectors, not from a better inequality. -/

/-- **The Halász–Montgomery inequality is attained.**  For the orthonormal system `φ i n = [i = n]`
and the constant vector `ξ n = V`, the Gram row sums are all `1`, every value `⟪φ i, ξ⟫` has
modulus `V`, and `∑_n ‖ξ n‖² = R V²`; so the bound `∑_i ‖⟪φ i, ξ⟫‖² ≤ Δ ∑_n ‖ξ n‖²` holds with
equality at `Δ = 1`. -/
theorem exists_sharp_rowSum (R : ℕ) {V : ℝ} (hV : 0 < V) :
    ∃ (φ : Fin R → Fin R → ℂ) (ξ : Fin R → ℂ),
      (∀ i, ∑ j, ‖∑ n, (starRingEnd ℂ) (φ i n) * φ j n‖ = 1) ∧
      (∀ i, ‖∑ n, (starRingEnd ℂ) (φ i n) * ξ n‖ = V) ∧
      ∑ n, ‖ξ n‖ ^ 2 = R * V ^ 2 := by
  classical
  refine ⟨fun i n => if i = n then 1 else 0, fun _ => (V : ℂ), ?_, ?_, ?_⟩
  · intro i
    have key : ∀ j, ∑ n, (starRingEnd ℂ) (if i = n then (1 : ℂ) else 0) *
        (if j = n then (1 : ℂ) else 0) = if i = j then 1 else 0 := by
      intro j
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun n _ => ?_
        rcases eq_or_ne i n with rfl | h1
        · simp [Ne.symm h]
        · simp [h1]
    simp only [key, apply_ite norm, norm_one, norm_zero]
    simp
  · intro i
    simp [Complex.norm_real, abs_of_pos hV]
  · simp [Complex.norm_real, abs_of_pos hV]

/-- **The ceiling of the large-values estimate.**  If a constant `c` makes the counting bound
`R ≤ c Δ (∑_n ‖ξ n‖²) / V²` valid for every configuration whose Gram row sums are bounded by `Δ`,
then `c ≥ 1`: the estimate `card_le_of_dirichletPoly_large` has the best possible constant, and
improving the large-values count requires more than a Gram row-sum bound. -/
theorem largeValues_constant_ge_one {c : ℝ}
    (hc : ∀ (R : ℕ) (φ : Fin R → Fin R → ℂ) (ξ : Fin R → ℂ) (Δ V : ℝ), 0 ≤ Δ → 0 < V →
      (∀ i, ∑ j, ‖∑ n, (starRingEnd ℂ) (φ i n) * φ j n‖ ≤ Δ) →
      (∀ i, V ≤ ‖∑ n, (starRingEnd ℂ) (φ i n) * ξ n‖) →
      (R : ℝ) ≤ c * Δ * (∑ n, ‖ξ n‖ ^ 2) / V ^ 2) :
    1 ≤ c := by
  obtain ⟨φ, ξ, hgram, hval, hnorm⟩ := exists_sharp_rowSum 1 one_pos
  have h := hc 1 φ ξ 1 1 zero_le_one one_pos (fun i => (hgram i).le) (fun i => (hval i).ge)
  rw [hnorm] at h
  norm_num at h
  linarith

end HalaszMontgomery

end RiemannHypothesis
