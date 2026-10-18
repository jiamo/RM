/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MontgomeryVaughan
import RiemannHypothesis.LocalSpacingMaximal

/-!
# The weighted Montgomery–Vaughan inequality

For real frequencies `λ_1, …, λ_n` and weights `δ_r > 0` with `|λ_r - λ_s| ≥ δ_r` for every
`s ≠ r` (for instance `δ_r = min_{s ≠ r} |λ_r - λ_s|`), and complex `u_1, …, u_n`,

  `|∑_{r ≠ s} u_r conj(u_s) / (λ_r - λ_s)| ≤ 5 √2 ∑_r |u_r|² / δ_r`
  (`weightedHilbertInequality`).

This is the weighted generalized Hilbert inequality of H. L. Montgomery and R. C. Vaughan
(*Hilbert's inequality*, J. London Math. Soc. (2) 8 (1974), 73–82), who prove it with the constant
`3π/2 ≈ 4.712`.  The constant proved here is `5 √2 ≈ 7.071 ≈ 2.251 π`, about `1.5` times theirs.
With all `δ_r = δ` it gives `(5√2 / δ) ∑ |u_r|²` (`hilbertInequality_of_uniform`), weaker than the
sharp `π / δ` of `RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality`.

## The argument

Put `u_r = √δ_r x_r`; the form becomes `∑ x_r conj(x_s) B r s` with the real skew-symmetric matrix
`B r s = √δ_r √δ_s / (λ_r - λ_s)` (`wkernel`), so it suffices to bound the eigenvalues `i μ` of `B`.

* `weighted_eigen_identity` — Montgomery and Vaughan's eigenvector argument with the weights:
  expanding `‖B v‖² = μ² ‖v‖²` with the partial-fraction identity
  `∑_r δ_r K r s K r t = K s t (a_s - a_t) + (δ_s + δ_t) K s t² + [s = t] b_s`
  (`sum_delta_kernel_mul_kernel`, `K r s = 1/(λ_r - λ_s)`, `a_s = ∑_r δ_r K r s`), the terms with
  `a_s`, `a_t` cancel because `v` is an eigenvector, and
  `μ² ‖v‖² = ∑_{s,t} v_s conj(v_t) √δ_s √δ_t (δ_s + δ_t) K s t² + ∑_s δ_s b_s |v_s|²`.
* In the unweighted case the first sum is bounded with `|v_s v_t| ≤ (|v_s|² + |v_t|²)/2`.  With
  weights this is no longer possible: the positive kernel `δ_s^{3/2} δ_t^{1/2} K s t²` is not
  bounded by Schur's test with any power weight.  It is bounded instead by the maximal inequality
  of `RiemannHypothesis/LocalSpacingMaximal.lean` (Vitali covering, layer cake):
  `∑_{s ≠ t} a_s a_t δ_s^{3/2} δ_t^{1/2} K s t² ≤ 2 √120 ∑ a_t²`
  (`LocalSpacing.sum_sum_mul_div_sq_le`), and `δ_s b_s ≤ 6`
  (`LocalSpacing.delta_mul_sum_delta_div_sq_le`).  Hence `μ² ≤ 6 + 4 √120 < 50`
  (`weighted_eigenvalue_sq_le`).
* The spectral theorem for the Hermitian matrix `i B` and Cauchy–Schwarz, as in
  `RiemannHypothesis/MontgomeryVaughan.lean`.

## Main results

* `weightedHilbertInequality` — the inequality above, for any weights `δ_r > 0` with
  `δ_r ≤ |λ_r - λ_s|` for all `s ≠ r`;
* `hilbertInequality_of_uniform` — the unweighted consequence `(5 √2 / δ) ∑ |u_r|²`.

No new hypothesis is assumed.  The constant `3π/2` of Montgomery and Vaughan is not proved.
-/

open Complex Finset Matrix

namespace RiemannHypothesis

namespace MontgomeryVaughanWeighted

open MontgomeryVaughan LocalSpacing

variable {n : ℕ}

/-- The weighted kernel `√δ_r √δ_s / (λ_r - λ_s)` (`0` on the diagonal). -/
noncomputable def wkernel (lam δ : Fin n → ℝ) (r s : Fin n) : ℝ :=
  Real.sqrt (δ r) * Real.sqrt (δ s) * kernel lam r s

lemma wkernel_swap (lam δ : Fin n → ℝ) (r s : Fin n) :
    wkernel lam δ s r = - wkernel lam δ r s := by
  unfold wkernel; rw [kernel_swap lam r s]; ring

/-- `a_s = ∑_r δ_r / (λ_r - λ_s)`. -/
noncomputable def wcolSum (lam δ : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, δ r * kernel lam r s

/-- `b_s = ∑_r δ_r / (λ_r - λ_s)²`. -/
noncomputable def wcolSq (lam δ : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, δ r * kernel lam r s ^ 2

/-- The weighted partial-fraction identity. -/
lemma sum_delta_kernel_mul_kernel {lam : Fin n → ℝ} (δ : Fin n → ℝ)
    (hinj : ∀ r s, r ≠ s → lam r ≠ lam s) (s t : Fin n) :
    ∑ r, δ r * kernel lam r s * kernel lam r t
      = kernel lam s t * (wcolSum lam δ s - wcolSum lam δ t)
        + (δ s + δ t) * kernel lam s t ^ 2 + (if s = t then wcolSq lam δ s else 0) := by
  by_cases hst : s = t
  · subst hst
    simp [kernel_self, wcolSq, sq, mul_assoc]
  rw [Finset.sum_congr rfl fun r _ => by rw [mul_assoc, kernel_mul_kernel hinj r hst]]
  simp only [mul_add, Finset.sum_add_distrib, if_neg hst, add_zero]
  have h1 : ∑ r, δ r * (if r = s then kernel lam s t ^ 2 else 0) = δ s * kernel lam s t ^ 2 := by
    simp
  have h2 : ∑ r, δ r * (if r = t then kernel lam s t ^ 2 else 0) = δ t * kernel lam s t ^ 2 := by
    simp
  rw [h1, h2]
  unfold wcolSum
  have : ∑ r, δ r * (kernel lam s t * (kernel lam r s - kernel lam r t))
      = kernel lam s t * (∑ r, δ r * kernel lam r s - ∑ r, δ r * kernel lam r t) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [this]
  ring

/-- **The weighted eigenvector identity.**  If `B v = i μ v` for `B r s = √δ_r √δ_s / (λ_r - λ_s)`
then `μ² ‖v‖² = ∑_{s,t} v_s conj(v_t) √δ_s √δ_t (δ_s + δ_t) K s t² + ∑_s δ_s b_s |v_s|²`: the
terms with `a_s` cancel. -/
theorem weighted_eigen_identity {lam δ : Fin n → ℝ} (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (hδ : ∀ r, 0 ≤ δ r) (v : Fin n → ℂ) (μ : ℝ)
    (hv : ∀ r, ∑ s, (wkernel lam δ r s : ℂ) * v s = I * μ * v r) :
    ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ)
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
          * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2 : ℝ) : ℂ)
        + ((∑ s, δ s * wcolSq lam δ s * ‖v s‖ ^ 2 : ℝ) : ℂ) := by
  set W : Fin n → Fin n → ℝ := wkernel lam δ with hW
  set K : Fin n → Fin n → ℝ := kernel lam with hK
  set a := wcolSum lam δ with ha
  set b := wcolSq lam δ with hb
  set w : Fin n → ℝ := fun r => Real.sqrt (δ r) with hw
  have hww : ∀ r, w r * w r = δ r := fun r => Real.mul_self_sqrt (hδ r)
  have hWdef : ∀ r s, W r s = w r * w s * K r s := fun r s => rfl
  have hvc : ∀ r, ∑ s, (W r s : ℂ) * (starRingEnd ℂ) (v s)
      = -(I * μ) * (starRingEnd ℂ) (v r) := by
    intro r
    have := congrArg (starRingEnd ℂ) (hv r)
    simpa [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] using this
  have hcol : ∀ t, ∑ s, (W s t : ℂ) * v s = -(I * μ * v t) := by
    intro t
    rw [← hv t, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hW, wkernel_swap lam δ t s]; push_cast; ring
  have hnorm : ∀ r, v r * (starRingEnd ℂ) (v r) = ((‖v r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hL : (∑ r, (∑ s, (W r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (W r t : ℂ) * v t))
      = ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hv r, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have := hnorm r
    push_cast at this
    linear_combination (μ:ℂ)^2 * this - (μ:ℂ)^2 * v r * (starRingEnd ℂ) (v r) * Complex.I_sq
  have hE : (∑ r, (∑ s, (W r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (W r t : ℂ) * v t))
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
          * ((w s * w t * ∑ r, δ r * K r s * K r t : ℝ) : ℂ) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hWdef, hWdef, ← hww r]
    push_cast
    ring
  have hX1 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have := hvc s
    rw [← hnorm s]
    calc ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
        = v s * (a s : ℂ) * ∑ t, (W s t : ℂ) * (starRingEnd ℂ) (v t) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
      _ = _ := by rw [this]; ring
  have hX2 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := hcol t
    rw [← hnorm t]
    calc ∑ s, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
        = (starRingEnd ℂ) (v t) * (a t : ℂ) * ∑ s, (W s t : ℂ) * v s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
      _ = _ := by rw [this]; ring
  rw [← hL, hE]
  have hterm : ∀ s t, v s * (starRingEnd ℂ) (v t)
      * ((w s * w t * ∑ r, δ r * K r s * K r t : ℝ) : ℂ)
      = v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
        - v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
        + v s * (starRingEnd ℂ) (v t)
          * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2 : ℝ) : ℂ)
        + (if s = t then ((δ s * b s * ‖v s‖ ^ 2 : ℝ) : ℂ) else 0) := by
    intro s t
    rw [sum_delta_kernel_mul_kernel δ hinj s t]
    split_ifs with h
    · subst h
      have h1 := hnorm s
      have h2 : ((w s * w s : ℝ) : ℂ) = (δ s : ℂ) := by rw [hww s]
      have hk : K s s = 0 := kernel_self lam s
      have hk' : kernel lam s s = 0 := kernel_self lam s
      rw [hWdef, hk, hk']
      push_cast at h1 h2 ⊢
      linear_combination ((w s : ℂ) * w s * b s) * h1 + (b s : ℂ) * (‖v s‖ : ℂ) ^ 2 * h2
    · simp only [hWdef, hw]
      push_cast
      ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hX1, hX2]
  push_cast
  ring

lemma kernel_sq_eq (lam : Fin n → ℝ) (s t : Fin n) :
    kernel lam s t ^ 2 = 1 / (lam s - lam t) ^ 2 := by
  rw [kernel, div_pow, one_pow]

lemma kernel_sq_swap (lam : Fin n → ℝ) (s t : Fin n) :
    kernel lam t s ^ 2 = kernel lam s t ^ 2 := by
  rw [kernel_swap lam s t, neg_sq]

/-- `√120 < 11`. -/
lemma sqrt_120_lt : Real.sqrt 120 < 11 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The weighted eigenvalue bound.**  Every eigenvalue `i μ` of the weighted matrix
`B r s = √δ_r √δ_s / (λ_r - λ_s)` has `μ² ≤ 50`. -/
theorem weighted_eigenvalue_sq_le {lam δ : Fin n → ℝ} (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ |lam r - lam s|)
    (v : Fin n → ℂ) (μ : ℝ) (hv0 : ∃ r, v r ≠ 0)
    (hv : ∀ r, ∑ s, (wkernel lam δ r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 ≤ 50 := by
  have hinj : ∀ r s, r ≠ s → lam r ≠ lam s := by
    intro r s h he
    have := hsep r s h
    rw [he, sub_self, abs_zero] at this
    linarith [hδ r]
  have hid := weighted_eigen_identity hinj (fun r => (hδ r).le) v μ hv
  set a : Fin n → ℝ := fun t => ‖v t‖ with hadef
  have ha : ∀ t, 0 ≤ a t := fun t => norm_nonneg _
  set g : Fin n → Fin n → ℝ := fun s t =>
    a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) * kernel lam s t ^ 2 with hgdef
  -- the off-diagonal term
  have hA : (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
      * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2 : ℝ) : ℂ)).re
      ≤ ∑ s, ∑ t, (g s t + g t s) := by
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Complex.re_mul_ofReal]
    have hc : 0 ≤ Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2 := by
      have := hδ s; have := hδ t; positivity
    have hre : (v s * (starRingEnd ℂ) (v t)).re ≤ a s * a t := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, RCLike.norm_conj]
    calc (v s * (starRingEnd ℂ) (v t)).re
          * (Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2)
        ≤ a s * a t * (Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) * kernel lam s t ^ 2) :=
          mul_le_mul_of_nonneg_right hre hc
      _ = g s t + g t s := by
          simp only [hgdef]; rw [kernel_sq_swap lam s t]; ring
  have hB : ∑ s, ∑ t, (g s t + g t s) = 2 * ∑ s, ∑ t, g s t := by
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_comm (f := fun s t => g t s)]
    ring
  have hC : ∑ s, ∑ t, g s t ≤ 2 * Real.sqrt 120 * ∑ t, a t ^ 2 := by
    refine le_trans (le_of_eq ?_) (sum_sum_mul_div_sq_le hδ hsep ha)
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_erase (s := Finset.univ) (a := s) (by simp [hgdef, kernel_self])]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hgdef]
    rw [kernel_sq_eq]
    ring
  -- the diagonal term
  have hD : ∑ s, δ s * wcolSq lam δ s * ‖v s‖ ^ 2 ≤ 6 * ∑ t, a t ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h6 := delta_mul_sum_delta_div_sq_le hδ hsep s
    have heq : wcolSq lam δ s = ∑ t ∈ univ.erase s, δ t / (lam s - lam t) ^ 2 := by
      unfold wcolSq
      rw [← Finset.sum_erase (s := Finset.univ) (a := s) (by simp [kernel_self])]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [kernel_sq_swap, kernel_sq_eq]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
  have hre := congrArg Complex.re hid
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  have htot : μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ 50 * ∑ t, a t ^ 2 := by
    have h11 := sqrt_120_lt
    have hS : 0 ≤ ∑ t, a t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
    nlinarith
  obtain ⟨r0, hr0⟩ := hv0
  have hpos : 0 < ∑ r, ‖v r‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun r => ‖v r‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ r0))
  exact le_of_mul_le_mul_right htot hpos

/-! ## The spectral theorem -/

/-- The Hermitian matrix `i B`, `(i B) r s = i √δ_r √δ_s / (λ_r - λ_s)`. -/
noncomputable def wMatrix (lam δ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r s => I * (wkernel lam δ r s : ℂ)

lemma wMatrix_isHermitian (lam δ : Fin n → ℝ) : (wMatrix lam δ).IsHermitian := by
  ext r s
  simp only [wMatrix, conjTranspose_apply, of_apply, star_mul', Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, wkernel_swap lam δ r s]
  push_cast; ring

lemma wMatrix_isSymmetric (lam δ : Fin n → ℝ) :
    (Matrix.toEuclideanLin (wMatrix lam δ)).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (wMatrix_isHermitian lam δ)

lemma toEuclideanLin_wMatrix_apply (lam δ : Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n))
    (r : Fin n) :
    (Matrix.toEuclideanLin (wMatrix lam δ) x).ofLp r
      = I * ∑ s, (wkernel lam δ r s : ℂ) * x.ofLp s := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, wMatrix, Finset.mul_sum,
    mul_assoc]

/-- A bound `μ² ≤ C` on the eigenvalues of `B` gives `‖(i B) x‖² ≤ C ‖x‖²`. -/
lemma norm_wMatrix_apply_le {lam δ : Fin n → ℝ} (C : ℝ)
    (heig : ∀ (v : Fin n → ℂ) (μ : ℝ), (∃ r, v r ≠ 0) →
      (∀ r, ∑ s, (wkernel lam δ r s : ℂ) * v s = I * μ * v r) → μ ^ 2 ≤ C)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (wMatrix lam δ) x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  set T := Matrix.toEuclideanLin (wMatrix lam δ)
  have hT : T.IsSymmetric := wMatrix_isSymmetric lam δ
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  set b := hT.eigenvectorBasis hn
  set ν := hT.eigenvalues hn
  have hν : ∀ i, ν i ^ 2 ≤ C := by
    intro i
    have hu := hT.apply_eigenvectorBasis hn i
    rw [← neg_sq]
    refine heig (b i).ofLp (-ν i) ?_ ?_
    · by_contra h
      push Not at h
      have : b i = 0 := by ext r; simp [h r]
      have h1 := b.orthonormal.1 i
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
    · intro r
      have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y.ofLp r) hu
      simp only [toEuclideanLin_wMatrix_apply, T] at this
      rw [PiLp.smul_apply] at this
      push_cast
      linear_combination (-I) * this
        + (∑ s, (wkernel lam δ r s : ℂ) * (b i).ofLp s) * Complex.I_sq
  have hrepr : ∀ i, b.repr (T x) i = (ν i : ℂ) * b.repr x i := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hT,
      hT.apply_eigenvectorBasis hn i, inner_smul_left, RCLike.conj_ofReal]
    rfl
  rw [← b.repr.norm_map (T x), ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hrepr, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (hν i) (by positivity)

/-! ## The theorem -/

/-- **The weighted generalized Hilbert inequality** (Montgomery–Vaughan form, constant `5 √2`).
For real `λ_r`, weights `δ_r > 0` with `δ_r ≤ |λ_r - λ_s|` for every `s ≠ r`, and complex `u_r`,
`|∑_{r ≠ s} u_r conj(u_s) / (λ_r - λ_s)| ≤ 5 √2 ∑_r |u_r|² / δ_r`.
Montgomery and Vaughan prove the constant `3π/2 ≈ 4.712`; `5 √2 ≈ 7.071 ≈ 2.251 π`. -/
theorem weightedHilbertInequality {n : ℕ} (lam δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ |lam r - lam s|) (u : Fin n → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 5 * Real.sqrt 2 * ∑ r, ‖u r‖ ^ 2 / δ r := by
  have hinj : ∀ r s, r ≠ s → lam r ≠ lam s := by
    intro r s h he
    have := hsep r s h
    rw [he, sub_self, abs_zero] at this
    linarith [hδ r]
  set w : Fin n → ℝ := fun r => Real.sqrt (δ r) with hwdef
  have hwpos : ∀ r, 0 < w r := fun r => Real.sqrt_pos.mpr (hδ r)
  have hww : ∀ r, w r * w r = δ r := fun r => Real.mul_self_sqrt (hδ r).le
  set x : Fin n → ℂ := fun r => u r / (w r : ℂ) with hxdef
  have hxu : ∀ r, u r = (w r : ℂ) * x r := by
    intro r
    have : (w r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos r).ne'
    simp only [hxdef]; field_simp
  set T := Matrix.toEuclideanLin (wMatrix lam δ)
  set xe : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have h50 : (5 * Real.sqrt 2) ^ 2 = 50 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hop : ‖T xe‖ ≤ 5 * Real.sqrt 2 * ‖xe‖ := by
    have h := norm_wMatrix_apply_le (lam := lam) (δ := δ) 50
      (fun v μ hv0 hv => weighted_eigenvalue_sq_le hδ hsep v μ hv0 hv) xe
    rw [← h50, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hxe : ‖xe‖ ^ 2 = ∑ r, ‖u r‖ ^ 2 / δ r := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hx : xe.ofLp r = x r := rfl
    rw [hx, hxdef]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos r), div_pow,
      sq (w r), hww r]
  have hform : ∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
      ((lam r : ℂ) - (lam s : ℂ)) = I * inner ℂ (T xe) xe := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toEuclideanLin_wMatrix_apply]
    have hdiag : ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        ((lam r : ℂ) - (lam s : ℂ))
        = ∑ s, x r * (starRingEnd ℂ) (x s) * (wkernel lam δ r s : ℂ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      simp only [wkernel, kernel_self, mul_zero, Complex.ofReal_zero, zero_add]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hne : (lam r : ℂ) - (lam s : ℂ) ≠ 0 := by
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]
        exact hinj r s (Finset.ne_of_mem_erase hs).symm
      rw [hxu r, hxu s]
      simp only [kernel, map_mul, Complex.conj_ofReal]
      push_cast
      field_simp
      simp only [hwdef]
      ring
    rw [hdiag]
    have hx : ∀ i, xe.ofLp i = x i := fun i => rfl
    simp only [RCLike.inner_apply, map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal, hx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    linear_combination (x r * (starRingEnd ℂ) (x s) * (wkernel lam δ r s : ℂ)) * Complex.I_sq
  rw [hform, norm_mul, Complex.norm_I, one_mul, ← hxe]
  calc ‖inner ℂ (T xe) xe‖ ≤ ‖T xe‖ * ‖xe‖ := norm_inner_le_norm _ _
    _ ≤ 5 * Real.sqrt 2 * ‖xe‖ * ‖xe‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = 5 * Real.sqrt 2 * ‖xe‖ ^ 2 := by ring

/-- **The unweighted check.**  With all `δ_r = δ`, `weightedHilbertInequality` gives the constant
`5 √2 / δ`; this is weaker than the sharp `π / δ` of
`RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality`, as expected. -/
theorem hilbertInequality_of_uniform {n : ℕ} (lam : Fin n → ℝ) (u : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 5 * Real.sqrt 2 / δ * ∑ r, ‖u r‖ ^ 2 := by
  have h := weightedHilbertInequality lam (fun _ => δ) (fun _ => hδ) hsep u
  rw [← Finset.sum_div] at h
  calc _ ≤ _ := h
    _ = 5 * Real.sqrt 2 / δ * ∑ r, ‖u r‖ ^ 2 := by ring

end MontgomeryVaughanWeighted

end RiemannHypothesis
