/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib
import RiemannHypothesis.KusminLandau
import RiemannHypothesis.DirichletPolyMeanSquare
import RiemannHypothesis.HalaszMontgomery

/-!
# The large sieve inequality

For real points `t_1, …, t_R` that are pairwise separated by at least `δ` *modulo one* and
coefficients `a_0, …, a_{N-1}`, the large sieve inequality bounds the values of the exponential
polynomial `S(t) = ∑_{n < N} a_n e(n t)` at those points by its mean square:

`∑_r ‖S(t_r)‖² ≤ Δ · ∑_{n < N} ‖a_n‖²`.

The sharp admissible constant is `Δ = N + δ⁻¹` (Selberg, Montgomery–Vaughan).  This file proves
the inequality with

`Δ = N + δ⁻¹ (1 + log (2δ)⁻¹)`,

i.e. with a logarithmic loss in the second term.  The proof is the Halász–Montgomery inequality
`RiemannHypothesis.HalaszMontgomery.sum_normSq_le_of_rowSum_le` applied to the vectors
`n ↦ e(−n t_r)`, whose Gram matrix is the Dirichlet kernel,

`⟪φ_r, φ_s⟫ = ∑_{n < N} e(n (t_r − t_s)) = K(t_r − t_s)`, `K(θ) = ∑_{n < N} e(n θ)`,

so that the admissible `Δ` is any bound for the row sums `∑_s ‖K(t_r − t_s)‖` of the kernel.
Those row sums are bounded here by the two standard estimates for the kernel, `‖K(θ)‖ ≤ N`
(used on the diagonal) and
`‖K(θ)‖ ≤ 1/(2‖θ‖)` (used off it, `‖θ‖` being the distance from `θ` to the nearest integer),
together with the separation hypothesis: the points at distance between `kδ` and `(k+1)δ` from a
given one number at most two, so the off-diagonal row sum is at most `δ⁻¹ ∑_{k ≤ K} 1/k` with
`K = ⌊(2δ)⁻¹⌋`, whence the harmonic bound.

## Main results

* `RiemannHypothesis.LargeSieve.intDist` — the distance from a real number to the nearest integer.
* `RiemannHypothesis.LargeSieve.kernel` — the Dirichlet kernel `K(θ) = ∑_{n < N} e(n θ)`.
* `RiemannHypothesis.LargeSieve.norm_kernel_le_inv_intDist` — the kernel bound
  `‖K(θ)‖ ≤ 1/(2 ‖θ‖)`.
* `RiemannHypothesis.LargeSieve.sum_norm_kernel_row_le` — the row-sum bound for `δ`-separated
  points.
* `RiemannHypothesis.LargeSieve.large_sieve` — **the large sieve inequality**, in the form
  `∑_r ‖∑_{n<N} a_n e(n t_r)‖² ≤ (N + δ⁻¹ (1 + log (2δ)⁻¹)) ∑_{n<N} ‖a_n‖²`.
* `RiemannHypothesis.LargeSieve.card_le_of_large_values` — the resulting **large-values bound**:
  at most `(N + δ⁻¹ (1 + log (2δ)⁻¹)) (∑_n ‖a_n‖²) / V²` of the separated points can carry
  `‖S(t_r)‖ ≥ V`.

* `RiemannHypothesis.LargeSieve.le_of_admissibleConstant` — **the ceiling**: *every* admissible
  large-sieve constant is at least `max N (2δ)⁻¹`, so both terms of the constant are necessary
  and only the logarithmic factor separates what is proved here from the optimum.

The constant is not optimal: the sharp `N + δ⁻¹` needs Selberg's majorant, which is not formalized
here.  Nothing in this file is applied to `ζ`.
-/

open Finset Complex

namespace RiemannHypothesis

namespace LargeSieve

open KusminLandau

/-! ## Distance to the nearest integer -/

/-- `intDist θ` is the distance from `θ` to the nearest integer, usually written `‖θ‖`. -/
noncomputable def intDist (θ : ℝ) : ℝ := |θ - round θ|

theorem intDist_nonneg (θ : ℝ) : 0 ≤ intDist θ := abs_nonneg _

theorem intDist_le_half (θ : ℝ) : intDist θ ≤ 1 / 2 := by
  simpa [intDist] using abs_sub_round θ

/-- The nearest integer is nearest: `intDist θ ≤ |θ − m|` for every integer `m`. -/
theorem intDist_le_abs_sub_int (θ : ℝ) (m : ℤ) : intDist θ ≤ |θ - m| := by
  rcases eq_or_ne m (round θ) with rfl | hm
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ |(m : ℝ) - (round θ : ℝ)| := by
      have h : (1 : ℤ) ≤ |m - round θ| := Int.one_le_abs (sub_ne_zero.mpr hm)
      exact_mod_cast h
    have h2 : |(m : ℝ) - (round θ : ℝ)| ≤ |(m : ℝ) - θ| + |θ - (round θ : ℝ)| := by
      simpa using abs_sub_le ((m : ℝ)) θ ((round θ : ℝ))
    have h3 : |θ - (round θ : ℝ)| ≤ 1 / 2 := abs_sub_round θ
    have h4 : (1 : ℝ) / 2 ≤ |(m : ℝ) - θ| := by linarith
    calc intDist θ ≤ 1 / 2 := intDist_le_half θ
      _ ≤ |(m : ℝ) - θ| := h4
      _ = |θ - (m : ℝ)| := abs_sub_comm _ _

theorem intDist_neg (θ : ℝ) : intDist (-θ) = intDist θ := by
  refine le_antisymm ?_ ?_
  · have h := intDist_le_abs_sub_int (-θ) (-round θ)
    rwa [show (-θ) - ((-round θ : ℤ) : ℝ) = -(θ - (round θ : ℝ)) by push_cast; ring,
      abs_neg] at h
  · have h := intDist_le_abs_sub_int θ (-round (-θ))
    rwa [show θ - ((-round (-θ) : ℤ) : ℝ) = -((-θ) - (round (-θ) : ℝ)) by push_cast; ring,
      abs_neg] at h

/-- Half of Jordan's inequality, in the form needed for the Dirichlet kernel:
`2 ‖θ‖ ≤ |sin (π θ)|`. -/
theorem two_mul_intDist_le_abs_sin (θ : ℝ) : 2 * intDist θ ≤ |Real.sin (Real.pi * θ)| := by
  have key : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 → 2 * v ≤ |Real.sin (Real.pi * v)| := by
    intro v hv hv2
    have hx : (0 : ℝ) ≤ Real.pi * v := by positivity
    have hx' : Real.pi * v ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h := Real.mul_le_sin hx hx'
    have he : 2 / Real.pi * (Real.pi * v) = 2 * v := by
      field_simp
    rw [he] at h
    exact h.trans (le_abs_self _)
  set k : ℤ := round θ with hk
  set u : ℝ := θ - (k : ℝ) with hu
  have hdu : intDist θ = |u| := rfl
  have habs : |u| ≤ 1 / 2 := abs_sub_round θ
  have hsin : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * u)| := by
    have hθ : Real.pi * θ = Real.pi * u + (k : ℝ) * Real.pi := by
      rw [hu]; ring
    rw [hθ, Real.sin_add_int_mul_pi, abs_mul]
    simp
  rw [hdu, hsin]
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]
    exact key u h (by rwa [abs_of_nonneg h] at habs)
  · rw [abs_of_nonpos h]
    have h1 : 2 * -u ≤ |Real.sin (Real.pi * (-u))| := by
      refine key (-u) (by linarith) ?_
      rwa [abs_of_nonpos h] at habs
    have h2 : |Real.sin (Real.pi * (-u))| = |Real.sin (Real.pi * u)| := by
      rw [show Real.pi * (-u) = -(Real.pi * u) by ring, Real.sin_neg, abs_neg]
    rwa [h2] at h1

/-! ## The Dirichlet kernel -/

/-- The Dirichlet kernel `K_N(θ) = ∑_{n < N} e(n θ)`. -/
noncomputable def kernel (N : ℕ) (θ : ℝ) : ℂ := ∑ n ∈ Finset.range N, e2pi (n * θ)

theorem e2pi_nat_mul (n : ℕ) (θ : ℝ) : e2pi ((n : ℝ) * θ) = e2pi θ ^ n := by
  induction n with
  | zero => simp [e2pi]
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ := by push_cast; ring
      rw [h, e2pi_add, ih, pow_succ]

theorem conj_e2pi (θ : ℝ) : (starRingEnd ℂ) (e2pi θ) = e2pi (-θ) := by
  simp only [e2pi, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

theorem kernel_zero (N : ℕ) : kernel N 0 = (N : ℂ) := by
  simp [kernel, e2pi]

theorem norm_kernel_le_card (N : ℕ) (θ : ℝ) : ‖kernel N θ‖ ≤ (N : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp

theorem kernel_neg (N : ℕ) (θ : ℝ) : kernel N (-θ) = (starRingEnd ℂ) (kernel N θ) := by
  simp only [kernel, map_sum, conj_e2pi]
  exact Finset.sum_congr rfl fun n _ => by rw [show (n : ℝ) * -θ = -((n : ℝ) * θ) by ring]

theorem norm_kernel_neg (N : ℕ) (θ : ℝ) : ‖kernel N (-θ)‖ = ‖kernel N θ‖ := by
  rw [kernel_neg, RCLike.norm_conj]

theorem norm_e2pi_sub_one_eq (θ : ℝ) : ‖e2pi θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [e2pi_sub_one_eq, norm_mul]
  have h3 : ‖((-Real.sin (Real.pi * θ) : ℝ) : ℂ)
      + (Real.cos (Real.pi * θ) : ℝ) * Complex.I‖ = 1 := by
    rw [Complex.norm_add_mul_I,
      show (-Real.sin (Real.pi * θ)) ^ 2 = Real.sin (Real.pi * θ) ^ 2 by ring,
      Real.sin_sq_add_cos_sq]
    exact Real.sqrt_one
  rw [h3, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- **The Dirichlet kernel bound**: `‖K_N(θ)‖ ≤ 1/(2 ‖θ‖)`, where `‖θ‖` is the distance from `θ`
to the nearest integer. -/
theorem norm_kernel_le_inv_intDist (N : ℕ) {θ : ℝ} (h : 0 < intDist θ) :
    ‖kernel N θ‖ ≤ 1 / (2 * intDist θ) := by
  have hsin : 0 < |Real.sin (Real.pi * θ)| :=
    lt_of_lt_of_le (by linarith) (two_mul_intDist_le_abs_sin θ)
  have hz : e2pi θ ≠ 1 := by
    intro hcon
    have h2 := norm_e2pi_sub_one_eq θ
    rw [hcon, sub_self, norm_zero] at h2
    linarith
  have hgeom : kernel N θ = (e2pi θ ^ N - 1) / (e2pi θ - 1) := by
    rw [kernel, ← geom_sum_eq hz]
    exact Finset.sum_congr rfl fun n _ => e2pi_nat_mul n θ
  rw [hgeom, norm_div]
  have h1 : ‖e2pi θ ^ N - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_e2pi, one_pow, norm_one]
    norm_num
  have h2 : ‖e2pi θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := norm_e2pi_sub_one_eq θ
  rw [h2]
  have h3 : 2 * intDist θ ≤ |Real.sin (Real.pi * θ)| := two_mul_intDist_le_abs_sin θ
  calc ‖e2pi θ ^ N - 1‖ / (2 * |Real.sin (Real.pi * θ)|)
      ≤ 2 / (2 * |Real.sin (Real.pi * θ)|) := by gcongr
    _ = 1 / |Real.sin (Real.pi * θ)| := by
        rw [eq_div_iff (ne_of_gt hsin)]
        field_simp
    _ ≤ 1 / (2 * intDist θ) := one_div_le_one_div_of_le (by linarith) h3

/-! ## The row sums of the kernel at separated points -/

/-- **The row-sum bound.**  If the points `t i`, `i ∈ s`, are pairwise `δ`-separated modulo one,
then for each `i` the sum `∑_j ‖K_N(t i − t j)‖` is at most `N + δ⁻¹ (1 + log (2δ)⁻¹)`. -/
theorem sum_norm_kernel_row_le {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (N : ℕ) {i : ι} (hi : i ∈ s) :
    ∑ j ∈ s, ‖kernel N (t i - t j)‖ ≤ (N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)) := by
  classical
  set K : ℕ := ⌊(2 * δ)⁻¹⌋₊ with hKdef
  set d : ι → ℝ := fun j => (t i - t j) - (round (t i - t j) : ℝ) with hd
  have hdist : ∀ j : ι, intDist (t i - t j) = |d j| := fun j => rfl
  have hdlb : ∀ j ∈ s.erase i, δ ≤ |d j| := by
    intro j hj
    have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have := hsep i hi j (Finset.mem_of_mem_erase hj) hji
    rwa [hdist j] at this
  have hdub : ∀ j : ι, |d j| ≤ 1 / 2 := fun j => by
    have := intDist_le_half (t i - t j)
    rwa [hdist j] at this
  set bucket : ι → ℕ := fun j => ⌊|d j| / δ⌋₊ with hbucket
  set φ : ι → Bool × ℕ := fun j => (decide (0 < d j), bucket j) with hφ
  set g : Bool × ℕ → ℝ := fun p => 1 / (2 * (p.2 : ℝ) * δ) with hg
  have hbucket_ge : ∀ j ∈ s.erase i, 1 ≤ bucket j := by
    intro j hj
    have h1 : (1 : ℝ) ≤ |d j| / δ := (one_le_div hδ).mpr (hdlb j hj)
    exact Nat.one_le_floor_iff _ |>.mpr h1
  have hbucket_le : ∀ j : ι, bucket j ≤ K := by
    intro j
    have : |d j| / δ ≤ (2 * δ)⁻¹ := by
      rw [div_le_iff₀ hδ, inv_mul_eq_div, le_div_iff₀ (by positivity)] at *
      nlinarith [hdub j]
    exact Nat.floor_le_floor this
  have hbucket_mul : ∀ j : ι, (bucket j : ℝ) * δ ≤ |d j| := by
    intro j
    have h := Nat.floor_le (a := |d j| / δ) (by positivity)
    calc (bucket j : ℝ) * δ ≤ (|d j| / δ) * δ := by
            exact mul_le_mul_of_nonneg_right h hδ.le
      _ = |d j| := by field_simp
  -- the diagonal term
  have hdiag : ‖kernel N (t i - t i)‖ = (N : ℝ) := by
    rw [sub_self, kernel_zero, Complex.norm_natCast]
  -- each off-diagonal term is bounded by the bucket value
  have hterm : ∀ j ∈ s.erase i, ‖kernel N (t i - t j)‖ ≤ g (φ j) := by
    intro j hj
    have hpos : 0 < intDist (t i - t j) := by
      rw [hdist j]; exact lt_of_lt_of_le hδ (hdlb j hj)
    refine (norm_kernel_le_inv_intDist N hpos).trans ?_
    rw [hdist j, hg, hφ]
    have hk1 : (1 : ℝ) ≤ (bucket j : ℝ) := by
      exact_mod_cast hbucket_ge j hj
    have hkd : 0 < 2 * (bucket j : ℝ) * δ := by positivity
    refine one_div_le_one_div_of_le hkd ?_
    nlinarith [hbucket_mul j]
  -- the classification map is injective off the diagonal
  have hinj : ∀ x ∈ s.erase i, ∀ y ∈ s.erase i, φ x = φ y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have hsxy : δ ≤ intDist (t x - t y) :=
      hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hne
    have hsign : (0 < d x) = (0 < d y) := by
      have := congrArg Prod.fst hxy
      simpa [hφ, decide_eq_decide] using this
    have hb : bucket x = bucket y := by
      have := congrArg Prod.snd hxy
      simpa [hφ] using this
    have hclose : |d x - d y| < δ := by
      have hsign' : (0 < d x) ↔ (0 < d y) := by rw [hsign]
      have hfx : (bucket x : ℝ) ≤ |d x| / δ := Nat.floor_le (by positivity)
      have hfy : (bucket y : ℝ) ≤ |d y| / δ := Nat.floor_le (by positivity)
      have hfx' : |d x| / δ < (bucket x : ℝ) + 1 := Nat.lt_floor_add_one _
      have hfy' : |d y| / δ < (bucket y : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hb] at hfx hfx'
      rw [le_div_iff₀ hδ] at hfx hfy
      rw [div_lt_iff₀ hδ] at hfx' hfy'
      have hxy1 : |d x| - |d y| < δ := by nlinarith
      have hxy2 : |d y| - |d x| < δ := by nlinarith
      have hdx0 : d x ≠ 0 := by
        intro h0
        have := hdlb x hx
        rw [h0, abs_zero] at this
        linarith
      have hdy0 : d y ≠ 0 := by
        intro h0
        have := hdlb y hy
        rw [h0, abs_zero] at this
        linarith
      rcases lt_or_gt_of_ne hdx0 with hxneg | hxpos
      · have hyneg : d y < 0 := by
          rcases lt_or_gt_of_ne hdy0 with h | h
          · exact h
          · exact absurd (hsign'.mpr h) (by linarith)
        rw [abs_of_neg hxneg] at hxy1 hxy2
        rw [abs_of_neg hyneg] at hxy1 hxy2
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      · have hypos : 0 < d y := hsign'.mp hxpos
        rw [abs_of_pos hxpos] at hxy1 hxy2
        rw [abs_of_pos hypos] at hxy1 hxy2
        rw [abs_sub_lt_iff]
        constructor <;> linarith
    have hle : intDist (t x - t y) ≤ |d x - d y| := by
      have hrep : d x - d y = (t y - t x) - ((round (t i - t x) - round (t i - t y) : ℤ) : ℝ) := by
        rw [hd]; push_cast; ring
      have := intDist_le_abs_sub_int (t y - t x) (round (t i - t x) - round (t i - t y))
      rw [← hrep] at this
      rw [show t x - t y = -(t y - t x) by ring, intDist_neg]
      exact this
    linarith
  -- assemble
  rw [← Finset.sum_erase_add s _ hi, hdiag, add_comm]
  gcongr
  calc ∑ j ∈ s.erase i, ‖kernel N (t i - t j)‖
      ≤ ∑ j ∈ s.erase i, g (φ j) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ (s.erase i).image φ, g p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K, g p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          simp only [Finset.mem_image] at hp
          obtain ⟨j, hj, rfl⟩ := hp
          simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and, hφ]
          exact ⟨hbucket_ge j hj, hbucket_le j⟩
        · intro p _ _
          rw [hg]
          positivity
    _ = δ⁻¹ * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) := by
        rw [Finset.sum_product]
        have hinner : ∀ b : Bool, ∑ k ∈ Finset.Icc 1 K, g (b, k)
            = ∑ k ∈ Finset.Icc 1 K, 1 / (2 * (k : ℝ) * δ) := fun _ => rfl
        rw [Finset.sum_congr rfl (fun b _ => hinner b), Finset.sum_const, Finset.card_univ,
          Fintype.card_bool, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        field_simp
        ring
    _ ≤ δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)) := by
        have hharm : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log K :=
          sum_inv_Icc_le K
        have hKle : (K : ℝ) ≤ (2 * δ)⁻¹ := Nat.floor_le (by positivity)
        have hK1 : 1 ≤ K := by
          refine Nat.one_le_floor_iff _ |>.mpr ?_
          rw [le_inv_comm₀ (by norm_num) (by positivity)]
          linarith
        have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
        have hlog : Real.log K ≤ Real.log ((2 * δ)⁻¹) := Real.log_le_log hKpos hKle
        have : δ⁻¹ > 0 := by positivity
        nlinarith [hharm, hlog]

/-! ## The large sieve inequality -/

/-- **The large sieve inequality** (with a logarithmic loss in the constant).  If the points
`t i`, `i ∈ s`, are pairwise separated by at least `δ` modulo one, then for all coefficients
`a n`,

`∑_i ‖∑_{n<N} a n e(n t i)‖² ≤ (N + δ⁻¹ (1 + log (2δ)⁻¹)) ∑_{n<N} ‖a n‖²`.

The sharp constant is `N + δ⁻¹`; the logarithmic factor is the cost of the elementary
Schur-test proof used here.  The proof is the Halász–Montgomery inequality
`HalaszMontgomery.sum_normSq_le_of_rowSum_le` applied to the vectors `n ↦ e(−n t i)`, whose Gram
matrix is the Dirichlet kernel, together with the row-sum bound `sum_norm_kernel_row_le`. -/
theorem large_sieve {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹))) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  classical
  have hlog : 0 ≤ Real.log ((2 * δ)⁻¹) := by
    refine Real.log_nonneg ?_
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    linarith
  have hΔ0 : (0 : ℝ) ≤ (N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)) := by
    have h1 : (0 : ℝ) < δ⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  set φ : ι → ℕ → ℂ := fun i n => e2pi (-((n : ℝ) * t i)) with hφ
  have hconj : ∀ (i : ι) (n : ℕ), (starRingEnd ℂ) (φ i n) = e2pi ((n : ℝ) * t i) := by
    intro i n
    rw [hφ, conj_e2pi, neg_neg]
  have hgram : ∀ i j : ι,
      ∑ n ∈ Finset.range N, (starRingEnd ℂ) (φ i n) * φ j n = kernel N (t i - t j) := by
    intro i j
    rw [kernel]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hconj i n, hφ, ← e2pi_add]
    congr 1
    ring
  have h := HalaszMontgomery.sum_normSq_le_of_rowSum_le s (Finset.range N) φ a hΔ0
    (by
      intro i hi
      have hrw : ∀ j : ι, ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) (φ i n) * φ j n‖
          = ‖kernel N (t i - t j)‖ := fun j => by rw [hgram i j]
      rw [Finset.sum_congr rfl (fun j _ => hrw j)]
      exact sum_norm_kernel_row_le hδ hδ2 hsep N hi)
  have hval : ∀ i : ι, ∑ n ∈ Finset.range N, (starRingEnd ℂ) (φ i n) * a n
      = ∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i) :=
    fun i => Finset.sum_congr rfl fun n _ => by rw [hconj i n]; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ s) => by rw [hval i])] at h
  exact h

/-- **Large values of an exponential polynomial.**  If `S(t) = ∑_{n<N} a_n e(n t)` has
`|S(t_i)| ≥ V > 0` at each of a family of points that are pairwise `δ`-separated modulo one, then
the number of such points is at most `(N + δ⁻¹ (1 + log (2δ)⁻¹)) (∑_n |a_n|²) / V²`. -/
theorem card_le_of_large_values {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ V : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ i ∈ s, V ≤ ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖) :
    (s.card : ℝ) ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)))
      * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) / V ^ 2 := by
  have hsum := large_sieve hδ hδ2 hsep a N
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ i ∈ s, ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _i ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := hbig i hi
          nlinarith [hV.le, norm_nonneg (∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i))]
  rw [le_div_iff₀ (by positivity)]
  linarith


/-! ## How much room is left in the constant

The constant proved above is `N + δ⁻¹ (1 + log (2δ)⁻¹)`, and the classical sharp one is
`N + δ⁻¹`.  The two results of this section make the gap precise from below: *any* admissible
large-sieve constant is at least `N`, and at least `⌊(2δ)⁻¹⌋ + 1 > (2δ)⁻¹`.  So the constant
proved here is within a factor `O(1 + log (2δ)⁻¹)` of optimal, and no argument can remove either
of the two terms — only the logarithm is open. -/

/-- The distance to the nearest integer is the absolute value itself on `[−1/2, 1/2]`. -/
theorem intDist_eq_abs_of_abs_le_half {θ : ℝ} (h : |θ| ≤ 1 / 2) : intDist θ = |θ| := by
  refine le_antisymm (by simpa using intDist_le_abs_sub_int θ 0) ?_
  rcases eq_or_ne (round θ) 0 with h0 | h0
  · simp [intDist, h0]
  · have h1 : (1 : ℝ) ≤ |(round θ : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    have h2 : |(round θ : ℝ)| - |θ| ≤ |(round θ : ℝ) - θ| := abs_sub_abs_le_abs_sub _ _
    have h3 : |(round θ : ℝ) - θ| = |θ - (round θ : ℝ)| := abs_sub_comm _ _
    have h4 : |θ| ≤ |θ - (round θ : ℝ)| := by rw [← h3]; linarith
    simpa [intDist] using h4

/-- `C` is an **admissible large-sieve constant** if the large sieve inequality with the constant
`C δ N` holds for every family of `δ`-separated points and every coefficient vector of length
`N`. -/
def AdmissibleConstant (C : ℝ → ℕ → ℝ) : Prop :=
  ∀ {ι : Type} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j)) → ∀ (a : ℕ → ℂ) (N : ℕ),
      ∑ i ∈ s, ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
        ≤ C δ N * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2

/-- The constant proved in this file is admissible. -/
theorem admissibleConstant_large_sieve :
    AdmissibleConstant (fun δ N => (N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹))) :=
  fun hδ hδ2 hsep a N => large_sieve hδ hδ2 hsep a N

/-- **The `N` term of the large-sieve constant is necessary.**  A single point with all
coefficients equal to `1` gives `‖∑_{n<N} a_n‖² = N²` against `∑_n ‖a_n‖² = N`. -/
theorem length_le_of_admissibleConstant {C : ℝ → ℕ → ℝ} (hC : AdmissibleConstant C) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {N : ℕ} (hN : 0 < N) : (N : ℝ) ≤ C δ N := by
  have h := hC (ι := Fin 1) (s := Finset.univ) (t := fun _ => 0) hδ hδ2
    (by intro i _ j _ hij; exact absurd (Subsingleton.elim i j) hij) (fun _ => 1) N
  have he : ∀ n : ℕ, (1 : ℂ) * e2pi ((n : ℝ) * 0) = 1 := by intro n; simp [e2pi]
  simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, norm_one,
    one_pow, Finset.card_univ, Fintype.card_fin] at h
  rw [Complex.norm_natCast, Nat.cast_one, one_mul, pow_two] at h
  exact le_of_mul_le_mul_right h (by exact_mod_cast hN)

/-- **The `δ⁻¹` term of the large-sieve constant is necessary.**  The `⌊(2δ)⁻¹⌋ + 1` points
`0, δ, 2δ, …` are `δ`-separated modulo one, and the coefficient vector supported at `n = 0` takes
the value `1` at every one of them, so `∑_i ‖S(t_i)‖² = ⌊(2δ)⁻¹⌋ + 1` against
`∑_n ‖a_n‖² = 1`. -/
theorem separation_le_of_admissibleConstant {C : ℝ → ℕ → ℝ} (hC : AdmissibleConstant C) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {N : ℕ} (hN : 0 < N) :
    ((⌊(2 * δ)⁻¹⌋₊ : ℝ) + 1) ≤ C δ N := by
  classical
  have hfl : (⌊(2 * δ)⁻¹⌋₊ : ℝ) ≤ (2 * δ)⁻¹ := Nat.floor_le (by positivity)
  have hbound : ∀ i : Fin (⌊(2 * δ)⁻¹⌋₊ + 1), (i : ℝ) ≤ (⌊(2 * δ)⁻¹⌋₊ : ℝ) := fun i => by
    exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hsep : ∀ i ∈ (Finset.univ : Finset (Fin (⌊(2 * δ)⁻¹⌋₊ + 1))),
      ∀ j ∈ (Finset.univ : Finset (Fin (⌊(2 * δ)⁻¹⌋₊ + 1))),
      i ≠ j → δ ≤ intDist ((i : ℝ) * δ - (j : ℝ) * δ) := by
    intro i _ j _ hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hone : (1 : ℝ) ≤ |((i : ℝ) - (j : ℝ))| := by
      have hne' : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by exact_mod_cast hne
      rcases lt_or_gt_of_ne hne' with h | h
      · rw [abs_of_nonpos (by linarith)]
        have hlt : (i : ℕ) < (j : ℕ) := by exact_mod_cast h
        have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
        linarith
      · rw [abs_of_nonneg (by linarith)]
        have hlt : (j : ℕ) < (i : ℕ) := by exact_mod_cast h
        have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
        linarith
    have hle : |((i : ℝ) - (j : ℝ))| ≤ (⌊(2 * δ)⁻¹⌋₊ : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [hbound j, (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))],
        by linarith [hbound i, (Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℕ))]⟩
    have hhalf : |((i : ℝ) - (j : ℝ))| * δ ≤ 1 / 2 := by
      have hid : (2 * δ)⁻¹ * δ = 1 / 2 := by field_simp
      nlinarith [hδ.le, abs_nonneg ((i : ℝ) - (j : ℝ))]
    have hrw : (i : ℝ) * δ - (j : ℝ) * δ = ((i : ℝ) - (j : ℝ)) * δ := by ring
    rw [hrw, intDist_eq_abs_of_abs_le_half (by rw [abs_mul, abs_of_pos hδ]; exact hhalf),
      abs_mul, abs_of_pos hδ]
    nlinarith [hδ.le]
  have h := hC (ι := Fin (⌊(2 * δ)⁻¹⌋₊ + 1)) (s := Finset.univ)
    (t := fun i => (i : ℝ) * δ) hδ hδ2 hsep (fun n => if n = 0 then 1 else 0) N
  have hval : ∀ i : Fin (⌊(2 * δ)⁻¹⌋₊ + 1), ∑ n ∈ Finset.range N,
      (if n = 0 then (1 : ℂ) else 0) * e2pi ((n : ℝ) * ((i : ℝ) * δ)) = 1 := by
    intro i
    rw [Finset.sum_eq_single 0]
    · simp [e2pi]
    · intro n _ hn; simp [hn]
    · intro hn; exact absurd (Finset.mem_range.mpr hN) hn
  have hcoef : ∑ n ∈ Finset.range N, ‖(if n = 0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro n _ hn; simp [hn]
    · intro hn; exact absurd (Finset.mem_range.mpr hN) hn
  simp only [hval, norm_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [hcoef, mul_one] at h
  exact_mod_cast h

/-- **The ceiling of the large sieve.**  Every admissible constant is at least `max N (2δ)⁻¹`;
the constant proved here is `N + δ⁻¹ (1 + log (2δ)⁻¹)`, so only the logarithmic factor is
open. -/
theorem le_of_admissibleConstant {C : ℝ → ℕ → ℝ} (hC : AdmissibleConstant C) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {N : ℕ} (hN : 0 < N) :
    max (N : ℝ) ((2 * δ)⁻¹) ≤ C δ N := by
  refine max_le (length_le_of_admissibleConstant hC hδ hδ2 hN) ?_
  have h := separation_le_of_admissibleConstant hC hδ hδ2 hN
  have : (2 * δ)⁻¹ < (⌊(2 * δ)⁻¹⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith


end LargeSieve

end RiemannHypothesis
