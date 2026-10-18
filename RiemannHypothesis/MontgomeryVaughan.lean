/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.HilbertInequality
import RiemannHypothesis.MeanValueWellSpaced

/-!
# Montgomery and Vaughan's generalized Hilbert inequality

For real frequencies `λ_1, …, λ_n` that are `δ`-separated (`|λ_r - λ_s| ≥ δ` for `r ≠ s`) and
complex `x_1, …, x_n`,

  `|∑_{r ≠ s} x_r conj(x_s) / (λ_r - λ_s)| ≤ (π / δ) ∑_r |x_r|²`.

This is the theorem of H. L. Montgomery and R. C. Vaughan (*Hilbert's inequality*, J. London
Math. Soc. (2) 8 (1974), 73–82), with the sharp constant `π / δ`.  It proves the statement
`RiemannHypothesis.Hilbert.GeneralizedHilbertInequality` recorded in
`RiemannHypothesis/HilbertInequality.lean`, whose definition is not changed.

## The argument

Write `A` for the real skew-symmetric matrix `A r s = 1 / (λ_r - λ_s)` (`kernel`; on the
diagonal it is `1 / 0 = 0` in Lean).  Then `H = i A` (`hilbertMatrix`) is Hermitian, and the
bilinear form is `i ⟪H x, x⟫`, so it suffices to bound the eigenvalues of `H`.

* `eigen_bound` — the heart of the proof.  If `A v = i μ v`, expand `‖A v‖² = μ² ‖v‖²` as
  `∑_{s,t} v_s conj(v_t) ∑_r A r s A r t` and use the partial-fraction identity
  `sum_kernel_mul_kernel`:
  `∑_r A r s A r t = A s t (a_s - a_t) + 2 A s t² + [s = t] b_s`, with `a_s = ∑_r A r s`,
  `b_s = ∑_r A r s²`.  The terms with `a_s` and `a_t` both equal `-i μ ∑_s a_s |v_s|²`
  *because `v` is an eigenvector*, and cancel.  (For a general vector this cancellation is
  false; that is the error of the circulated "elementary" proof.)  What is left gives
  `μ² ‖v‖² ≤ 3 ∑_s b_s |v_s|²`.
* `colSq_le` — `b_s = ∑_{r ≠ s} (λ_r - λ_s)⁻² ≤ 2 ∑_{k ≥ 1} (k δ)⁻² = π² / (3 δ²)`: the map
  `r ↦ ⌊|λ_r - λ_s| / δ⌋` has fibres of size at most two
  (`RiemannHypothesis.WellSpaced.card_fiber_le_two`), and Basel's sum `hasSum_zeta_two`.
* `eigenvalue_sq_le` — hence `μ² ≤ (π / δ)²` for every eigenvalue.
* `norm_apply_le` — the spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`) turns the
  eigenvalue bound into `‖H x‖ ≤ (π / δ) ‖x‖`.
* `generalizedHilbertInequality` — Cauchy–Schwarz.

## Main results

* `RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality` :
  `RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`.

No new hypothesis is assumed; the optimality of the constant `π` is not proved here.
-/

open Complex Finset Matrix

namespace RiemannHypothesis

namespace MontgomeryVaughan

variable {n : ℕ}

/-- The Hilbert kernel `1 / (λ_r - λ_s)`.  On the diagonal it is `1 / 0 = 0`. -/
noncomputable def kernel (lam : Fin n → ℝ) (r s : Fin n) : ℝ := 1 / (lam r - lam s)

lemma kernel_self (lam : Fin n → ℝ) (r : Fin n) : kernel lam r r = 0 := by
  simp [kernel]

lemma kernel_swap (lam : Fin n → ℝ) (r s : Fin n) : kernel lam s r = - kernel lam r s := by
  unfold kernel
  rw [← neg_sub, div_neg]

/-- The partial-fraction identity, with the two correction terms at `r = s` and `r = t`. -/
lemma kernel_mul_kernel {lam : Fin n → ℝ} (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (r : Fin n) {s t : Fin n} (hst : s ≠ t) :
    kernel lam r s * kernel lam r t
      = kernel lam s t * (kernel lam r s - kernel lam r t)
        + (if r = s then kernel lam s t ^ 2 else 0)
        + (if r = t then kernel lam s t ^ 2 else 0) := by
  by_cases hrs : r = s
  · subst hrs
    simp [kernel_self, hst]; ring
  by_cases hrt : r = t
  · subst hrt
    simp [kernel_self, hrs, kernel_swap lam r s]; ring
  simp only [hrs, hrt, if_false, add_zero]
  have h1 : lam r - lam s ≠ 0 := sub_ne_zero.mpr (hinj _ _ hrs)
  have h2 : lam r - lam t ≠ 0 := sub_ne_zero.mpr (hinj _ _ hrt)
  have h3 : lam s - lam t ≠ 0 := sub_ne_zero.mpr (hinj _ _ hst)
  unfold kernel
  field_simp
  ring

/-- `a_s = ∑_r 1 / (λ_r - λ_s)`. -/
noncomputable def colSum (lam : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, kernel lam r s

/-- `b_s = ∑_r 1 / (λ_r - λ_s)²`. -/
noncomputable def colSq (lam : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, kernel lam r s ^ 2

/-- Summed over `r`, the partial-fraction identity holds for all `s`, `t`. -/
lemma sum_kernel_mul_kernel {lam : Fin n → ℝ} (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (s t : Fin n) :
    ∑ r, kernel lam r s * kernel lam r t
      = kernel lam s t * (colSum lam s - colSum lam t) + 2 * kernel lam s t ^ 2
        + (if s = t then colSq lam s else 0) := by
  by_cases hst : s = t
  · subst hst
    simp [kernel_self, colSq, sq]
  rw [Finset.sum_congr rfl fun r _ => kernel_mul_kernel hinj r hst]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hst, if_false, colSum]
  ring

/-- The row sums of the squared kernel: `∑_{r ≠ s} (λ_r - λ_s)⁻² ≤ 2 ζ(2) δ⁻² = π² / (3 δ²)`. -/
lemma colSq_le {lam : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) (s : Fin n) :
    colSq lam s ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  set g : Fin n → ℕ := fun r => ⌊|lam s - lam r| / δ⌋₊ with hg
  have hsep' : WellSpaced.Separated Finset.univ lam δ :=
    fun r _ s _ h => hsep r s h
  have hterm : ∀ r ∈ Finset.univ.erase s,
      kernel lam r s ^ 2 ≤ 1 / δ ^ 2 * (1 / (g r : ℝ) ^ 2) := by
    intro r hr
    have hne : r ≠ s := Finset.ne_of_mem_erase hr
    have hd : δ ≤ |lam s - lam r| := hsep s r hne.symm
    have hq : (1 : ℝ) ≤ |lam s - lam r| / δ := by rw [le_div_iff₀ hδ]; linarith
    have hg1 : (1 : ℝ) ≤ g r := by
      have : 1 ≤ g r := Nat.le_floor (by exact_mod_cast hq)
      exact_mod_cast this
    have hgle : (g r : ℝ) * δ ≤ |lam s - lam r| := by
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ |lam s - lam r| / δ)
      rw [le_div_iff₀ hδ] at this; exact this
    have hk : kernel lam r s ^ 2 = 1 / |lam s - lam r| ^ 2 := by
      unfold kernel; rw [div_pow, sq_abs, ← neg_sub, neg_sq]; ring
    rw [hk, show 1 / δ ^ 2 * (1 / (g r : ℝ) ^ 2) = 1 / ((g r : ℝ) * δ) ^ 2 by ring]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) hgle 2
  have hsplit : colSq lam s = ∑ r ∈ Finset.univ.erase s, kernel lam r s ^ 2 := by
    unfold colSq
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
    simp [kernel]
  have hsumm : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := hasSum_zeta_two.summable
  set T := (Finset.univ.erase s).image g
  calc colSq lam s ≤ ∑ r ∈ Finset.univ.erase s, 1 / δ ^ 2 * (1 / (g r : ℝ) ^ 2) := by
        rw [hsplit]; exact Finset.sum_le_sum hterm
    _ = 1 / δ ^ 2 * ∑ k ∈ T, ∑ r ∈ Finset.univ.erase s with g r = k, (1 / (g r : ℝ) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to]
        intro r hr; exact Finset.mem_image_of_mem g hr
    _ ≤ 1 / δ ^ 2 * ∑ k ∈ T, 2 * (1 / (k : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
        rw [Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2],
          Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast WellSpaced.card_fiber_le_two hδ hsep' s k
    _ ≤ 1 / δ ^ 2 * (2 * (Real.pi ^ 2 / 6)) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          (by positivity)
        rw [← hasSum_zeta_two.tsum_eq]
        exact hsumm.sum_le_tsum T (fun _ _ => by positivity)
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := by field_simp; ring

/-- The heart of Montgomery and Vaughan's argument: for an eigenvector `A v = i μ v` of the
real skew-symmetric matrix `A = (1 / (λ_r - λ_s))`, the terms with `a_s` cancel and
`μ² ‖v‖² ≤ 3 ∑_s b_s |v_s|²`. -/
theorem eigen_bound {lam : Fin n → ℝ} (hinj : ∀ r s, r ≠ s → lam r ≠ lam s)
    (v : Fin n → ℂ) (μ : ℝ)
    (hv : ∀ r, ∑ s, (kernel lam r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ 3 * ∑ s, colSq lam s * ‖v s‖ ^ 2 := by
  set K : Fin n → Fin n → ℝ := kernel lam with hK
  set a := colSum lam with ha
  set b := colSq lam with hb
  have hvc : ∀ r, ∑ s, (K r s : ℂ) * (starRingEnd ℂ) (v s)
      = -(I * μ) * (starRingEnd ℂ) (v r) := by
    intro r
    have := congrArg (starRingEnd ℂ) (hv r)
    simpa [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] using this
  have hcol : ∀ t, ∑ s, (K s t : ℂ) * v s = -(I * μ * v t) := by
    intro t
    rw [← hv t, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hK, kernel_swap lam t s]; push_cast; ring
  have hnorm : ∀ r, v r * (starRingEnd ℂ) (v r) = ((‖v r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- `‖A v‖² = μ² ‖v‖²`
  have hL : (∑ r, (∑ s, (K r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (K r t : ℂ) * v t))
      = ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hv r, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have := hnorm r
    push_cast at this
    linear_combination (μ:ℂ)^2 * this - (μ:ℂ)^2 * v r * (starRingEnd ℂ) (v r) * Complex.I_sq
  -- expanding `‖A v‖²` as a triple sum
  have hE : (∑ r, (∑ s, (K r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (K r t : ℂ) * v t))
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  -- the two `a`-terms are equal, because `v` is an eigenvector
  have hX1 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have := hvc s
    rw [← hnorm s]
    calc ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
        = v s * (a s : ℂ) * ∑ t, (K s t : ℂ) * (starRingEnd ℂ) (v t) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
      _ = _ := by rw [this]; ring
  have hX2 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := hcol t
    rw [← hnorm t]
    calc ∑ s, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
        = (starRingEnd ℂ) (v t) * (a t : ℂ) * ∑ s, (K s t : ℂ) * v s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
      _ = _ := by rw [this]; ring
  -- what is left after the cancellation
  have hmain : ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ)
      = 2 * ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ)
        + ((∑ s, b s * ‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hL, hE]
    have hterm : ∀ s t, v s * (starRingEnd ℂ) (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ)
        = v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
          - v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
          + 2 * (v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ))
          + (if s = t then ((b s * ‖v s‖ ^ 2 : ℝ) : ℂ) else 0) := by
      intro s t
      have hst : ∑ r, K r s * K r t
          = K s t * (a s - a t) + 2 * K s t ^ 2 + (if s = t then b s else 0) :=
        sum_kernel_mul_kernel hinj s t
      rw [hst]
      split_ifs with h
      · subst h; rw [Complex.ofReal_mul, ← hnorm s]; push_cast; ring
      · push_cast; ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hX1, hX2, ← Finset.mul_sum]
    push_cast
    ring
  -- the remaining off-diagonal term, by `|v_s v_t| ≤ (|v_s|² + |v_t|²) / 2`
  have hKs : ∀ s t, K s t ^ 2 = K t s ^ 2 := fun s t => by
    rw [hK, kernel_swap lam s t, neg_sq]
  have h1 : ∑ s, ∑ t, K s t ^ 2 * ‖v s‖ ^ 2 = ∑ s, b s * ‖v s‖ ^ 2 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hKs s t
  have h2 : ∑ s, ∑ t, K s t ^ 2 * ‖v t‖ ^ 2 = ∑ t, b t * ‖v t‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul]
    rfl
  have hY : (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ)).re
      ≤ ∑ s, b s * ‖v s‖ ^ 2 := by
    calc (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ)).re
        ≤ ∑ s, ∑ t, K s t ^ 2 * ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) := by
          rw [Complex.re_sum]
          refine Finset.sum_le_sum fun s _ => ?_
          rw [Complex.re_sum]
          refine Finset.sum_le_sum fun t _ => ?_
          rw [Complex.re_mul_ofReal, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine (Complex.re_le_norm _).trans ?_
          rw [norm_mul, RCLike.norm_conj]
          nlinarith [sq_nonneg (‖v s‖ - ‖v t‖)]
      _ = (∑ s, ∑ t, K s t ^ 2 * ‖v s‖ ^ 2 + ∑ s, ∑ t, K s t ^ 2 * ‖v t‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = ∑ s, b s * ‖v s‖ ^ 2 := by rw [h1, h2]; ring
  have hre := congrArg Complex.re hmain
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  have h2' : (2 * ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ)).re
      = 2 * (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t ^ 2 : ℝ) : ℂ)).re := by
    simp
  rw [h2'] at hre
  linarith

/-- Every eigenvalue `i μ` of `A = (1 / (λ_r - λ_s))` has `μ² ≤ (π / δ)²`. -/
theorem eigenvalue_sq_le {lam : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|)
    (v : Fin n → ℂ) (μ : ℝ) (hv0 : ∃ r, v r ≠ 0)
    (hv : ∀ r, ∑ s, (kernel lam r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 ≤ (Real.pi / δ) ^ 2 := by
  have hinj : ∀ r s, r ≠ s → lam r ≠ lam s := by
    intro r s h he
    have := hsep r s h
    rw [he, sub_self, abs_zero] at this
    linarith
  have h1 := eigen_bound hinj v μ hv
  have h2 : 3 * ∑ s, colSq lam s * ‖v s‖ ^ 2 ≤ (Real.pi / δ) ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have := colSq_le hδ hsep s
    have h3 : 3 * colSq lam s ≤ (Real.pi / δ) ^ 2 := by
      rw [div_pow]
      rw [le_div_iff₀ (by positivity)] at this
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [sq_nonneg ‖v s‖]
  obtain ⟨r0, hr0⟩ := hv0
  have hpos : 0 < ∑ r, ‖v r‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun r => ‖v r‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ r0))
  exact le_of_mul_le_mul_right (h1.trans h2) hpos

/-! ## The spectral theorem -/

/-- The Hermitian matrix `H = i A`, `H r s = i / (λ_r - λ_s)`. -/
noncomputable def hilbertMatrix (lam : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r s => I * (kernel lam r s : ℂ)

lemma hilbertMatrix_isHermitian (lam : Fin n → ℝ) : (hilbertMatrix lam).IsHermitian := by
  ext r s
  simp only [hilbertMatrix, conjTranspose_apply, of_apply, star_mul', Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, kernel_swap lam r s]
  push_cast; ring

lemma hilbertMatrix_isSymmetric (lam : Fin n → ℝ) :
    (Matrix.toEuclideanLin (hilbertMatrix lam)).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (hilbertMatrix_isHermitian lam)

lemma toEuclideanLin_hilbert_apply (lam : Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n))
    (r : Fin n) :
    (Matrix.toEuclideanLin (hilbertMatrix lam) x).ofLp r
      = I * ∑ s, (kernel lam r s : ℂ) * x.ofLp s := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, hilbertMatrix, Finset.mul_sum,
    mul_assoc]

/-- A bound `μ² ≤ C` on the eigenvalues of `A` gives `‖H x‖² ≤ C ‖x‖²`, by expanding `x` in
an orthonormal eigenbasis of the Hermitian matrix `H = i A`. -/
lemma norm_apply_le {lam : Fin n → ℝ} (C : ℝ)
    (heig : ∀ (v : Fin n → ℂ) (μ : ℝ), (∃ r, v r ≠ 0) →
      (∀ r, ∑ s, (kernel lam r s : ℂ) * v s = I * μ * v r) → μ ^ 2 ≤ C)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (hilbertMatrix lam) x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  set T := Matrix.toEuclideanLin (hilbertMatrix lam)
  have hT : T.IsSymmetric := hilbertMatrix_isSymmetric lam
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
      simp only [toEuclideanLin_hilbert_apply, T] at this
      rw [PiLp.smul_apply] at this
      push_cast
      linear_combination (-I) * this + (∑ s, (kernel lam r s : ℂ) * (b i).ofLp s) * Complex.I_sq
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

/-- **Montgomery and Vaughan's generalized Hilbert inequality**, with the sharp constant
`π / δ`: for `δ`-separated real frequencies `λ_r` and complex `x_r`,
`|∑_{r ≠ s} x_r conj(x_s) / (λ_r - λ_s)| ≤ (π / δ) ∑_r |x_r|²`. -/
theorem generalizedHilbertInequality : Hilbert.GeneralizedHilbertInequality := by
  intro n lam x δ hδ hsep
  set T := Matrix.toEuclideanLin (hilbertMatrix lam)
  set xe : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hop : ‖T xe‖ ≤ Real.pi / δ * ‖xe‖ := by
    have h := norm_apply_le (lam := lam) ((Real.pi / δ) ^ 2)
      (fun v μ hv0 hv => eigenvalue_sq_le hδ hsep v μ hv0 hv) xe
    rw [← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hxe : ‖xe‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 := EuclideanSpace.norm_sq_eq xe
  -- the bilinear form is `i ⟪H x, x⟫`
  have hform : ∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
      ((lam r : ℂ) - (lam s : ℂ)) = I * inner ℂ (T xe) xe := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toEuclideanLin_hilbert_apply]
    have hdiag : ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
        ((lam r : ℂ) - (lam s : ℂ))
        = ∑ s, x r * (starRingEnd ℂ) (x s) * (kernel lam r s : ℂ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      simp only [kernel_self, Complex.ofReal_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [kernel]
      push_cast
      ring
    rw [hdiag]
    have hx : ∀ i, xe.ofLp i = x i := fun i => rfl
    simp only [RCLike.inner_apply, map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal, hx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    linear_combination (x r * (starRingEnd ℂ) (x s) * (kernel lam r s : ℂ)) * Complex.I_sq
  rw [hform, norm_mul, Complex.norm_I, one_mul, ← hxe]
  calc ‖inner ℂ (T xe) xe‖ ≤ ‖T xe‖ * ‖xe‖ := norm_inner_le_norm _ _
    _ ≤ Real.pi / δ * ‖xe‖ * ‖xe‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = Real.pi / δ * ‖xe‖ ^ 2 := by ring

end MontgomeryVaughan

end RiemannHypothesis
