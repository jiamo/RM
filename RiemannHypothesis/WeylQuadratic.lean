/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDifferencing

/-!
# Weyl's bound for a quadratic exponential sum

`RiemannHypothesis.WeylDifferencing` proves van der Corput's A process: an exponential sum is
controlled by its *differenced* sums `∑ e(f(n+k) − f(n))`.  For a quadratic phase the differenced
phase is linear, and a linear exponential sum is a geometric series, which is summed exactly.
That gives, with no further machinery, the classical Weyl bound for `∑ e(α n²)`.

This is the first arithmetic consequence drawn from the A process in this repository, and it is
the model case of the method: one differencing step reduces degree `2` to degree `1`.

## Main results

* `intDist` — the distance from a real to the nearest integer, `‖θ‖` in the classical notation.
* `norm_geomSum_e2pi_le` — the geometric-series bound
  `‖∑_{j < M} e(θ j + c)‖ ≤ 1/(2‖θ‖)`, with no dependence on `M`.
* `norm_sq_sum_e2pi_quadratic_le` — **Weyl's inequality for a quadratic phase**: for every
  `H ≥ 1` whose multiples `2αk`, `0 < k < H`, all avoid the integers,

      H ‖∑_{0 ≤ n < N} e(α n²)‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} 1/(2‖2αk‖)).

* `normSq_sum_e2pi_quadratic_le_of_le` — the usable corollary: if `‖2αk‖ ≥ δ > 0` for all
  `0 < k < H`, then

      ‖∑_{0 ≤ n < N} e(α n²)‖² ≤ (N + H − 1)(N + (H − 1)/δ) / H,

  which for `H` of size `N` and `δ` bounded below is `O(N)` — square-root cancellation, against
  the trivial `N²`.

## Proof

`e(θ j + c) = e(c) · e(θ)^j`, so the inner sum is a geometric series with ratio `r = e(θ)`, of
modulus `‖r^M − 1‖/‖r − 1‖ ≤ 2/‖r − 1‖`.  The denominator is `‖e(θ) − 1‖ = 2|sin πθ| ≥ 4‖θ‖` by
Jordan's inequality, after translating `θ` by the nearest integer (which changes nothing, since
`e` is `1`-periodic).  Feeding this into the A process, with the differenced phase
`α(n+k)² − αn² = (2αk) n + αk²`, gives the theorem.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylQuadratic

open KusminLandau WeylDifferencing

/-- The distance from `θ` to the nearest integer, written `‖θ‖` in the classical literature. -/
def intDist (θ : ℝ) : ℝ := |θ - round θ|

theorem intDist_nonneg (θ : ℝ) : 0 ≤ intDist θ := abs_nonneg _

theorem intDist_le_half (θ : ℝ) : intDist θ ≤ 1 / 2 := abs_sub_round θ

/-- `e` does not see the translation of the argument to the nearest integer. -/
theorem e2pi_sub_round (θ : ℝ) : e2pi (θ - round θ) = e2pi θ := e2pi_sub_int θ _

/-- Jordan's inequality in the form needed for a geometric series: `‖e(θ) − 1‖ ≥ 4‖θ‖`. -/
theorem four_mul_intDist_le_norm_e2pi_sub_one (θ : ℝ) :
    4 * intDist θ ≤ ‖e2pi θ - 1‖ := by
  set x : ℝ := θ - round θ with hx
  have hxle : |x| ≤ 1 / 2 := abs_sub_round θ
  have hdist : intDist θ = |x| := rfl
  have hkey : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → 4 * y ≤ ‖e2pi y - 1‖ := by
    intro y hy0 hy1
    rw [norm_e2pi_sub_one hy0 (by linarith)]
    have := two_mul_le_sin_pi_mul hy0 le_rfl (by linarith)
    linarith
  have hconj : ∀ y : ℝ, ‖e2pi (-y) - 1‖ = ‖e2pi y - 1‖ := by
    intro y
    rw [← conj_e2pi y, show (starRingEnd ℂ) (e2pi y) - 1 = (starRingEnd ℂ) (e2pi y - 1) by simp]
    exact RCLike.norm_conj _
  rcases lt_trichotomy x 0 with h | h | h
  · have habs : intDist θ = -x := by rw [hdist, abs_of_neg h]
    have h2 : -x ≤ 1 / 2 := by
      rw [abs_of_neg h] at hxle
      linarith
    have hy := hkey (-x) (by linarith) h2
    rw [habs, ← e2pi_sub_round θ, ← hx, ← hconj x]
    exact hy
  · rw [hdist, h]
    simp
  · rw [hdist, ← e2pi_sub_round θ, ← hx, abs_of_pos h]
    exact hkey x h (by rw [abs_of_pos h] at hxle; exact hxle)

/-- `e(θ j) = e(θ)^j`. -/
theorem e2pi_mul_natCast (θ : ℝ) (j : ℕ) : e2pi (θ * j) = e2pi θ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have : θ * (j + 1 : ℕ) = θ * j + θ := by push_cast; ring
      rw [this, e2pi_add, ih, pow_succ]

/-- **The geometric-series bound.**  A linear exponential sum is bounded by `1/(2‖θ‖)`,
independently of the number of terms. -/
theorem norm_geomSum_e2pi_le {θ : ℝ} (hθ : intDist θ ≠ 0) (M : ℕ) (c : ℝ) :
    ‖∑ j ∈ range M, e2pi (θ * j + c)‖ ≤ 1 / (2 * intDist θ) := by
  have hpos : 0 < intDist θ := lt_of_le_of_ne (intDist_nonneg θ) (Ne.symm hθ)
  have hden : 4 * intDist θ ≤ ‖e2pi θ - 1‖ := four_mul_intDist_le_norm_e2pi_sub_one θ
  have hne : e2pi θ - 1 ≠ 0 := by
    intro hcon
    rw [hcon] at hden
    simp only [norm_zero] at hden
    linarith
  have hr : e2pi θ ≠ 1 := by
    intro hcon
    exact hne (by rw [hcon]; ring)
  have hsum : ∑ j ∈ range M, e2pi (θ * j + c)
      = e2pi c * ((e2pi θ ^ M - 1) / (e2pi θ - 1)) := by
    rw [← geom_sum_eq hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e2pi_add, e2pi_mul_natCast, mul_comm]
  rw [hsum, norm_mul, norm_e2pi, one_mul, norm_div]
  have hnum : ‖e2pi θ ^ M - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_e2pi, one_pow, norm_one]
    norm_num
  have hdpos : 0 < ‖e2pi θ - 1‖ := norm_pos_iff.mpr hne
  have h4pos : (0 : ℝ) < 4 * intDist θ := by positivity
  calc ‖e2pi θ ^ M - 1‖ / ‖e2pi θ - 1‖ ≤ 2 / ‖e2pi θ - 1‖ := by gcongr
    _ ≤ 2 / (4 * intDist θ) := by gcongr
    _ = 1 / (2 * intDist θ) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- A sum over the integer interval `[0, b)` is a sum over `range b.toNat`. -/
theorem sum_Ico_int_eq_sum_range (b : ℤ) (g : ℤ → ℂ) :
    ∑ n ∈ Finset.Ico (0 : ℤ) b, g n = ∑ j ∈ range b.toNat, g (j : ℤ) := by
  refine Finset.sum_nbij' (fun n => n.toNat) (fun j => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_range]
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    omega
  · intro j _
    omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    congr 1
    omega

/-- The differenced phase of `α n²` is linear. -/
theorem quadratic_diff (α : ℝ) (k n : ℤ) :
    α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2 = (2 * α * k) * (n : ℝ) + α * (k : ℝ) ^ 2 := by
  push_cast
  ring

/-- **Weyl's inequality for a quadratic phase.**  One differencing step turns `∑ e(α n²)` into
geometric series, and the bound is `1/(2‖2αk‖)` for each shift `k`. -/
theorem norm_sq_sum_e2pi_quadratic_le (α : ℝ) (N H : ℕ) (hH : 0 < H)
    (hα : ∀ k : ℤ, 0 < k → k < (H : ℤ) → intDist (2 * α * k) ≠ 0) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ ((N : ℝ) + H - 1)
        * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), 1 / (2 * intDist (2 * α * k))) := by
  have hA := norm_sq_sum_e2pi_le (fun n : ℤ => α * (n : ℝ) ^ 2) N H hH
  refine hA.trans ?_
  have hpos : (0 : ℝ) ≤ (N : ℝ) + H - 1 := by
    have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hterm : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
          e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖
        ≤ 1 / (2 * intDist (2 * α * k)) := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hg : ∀ n : ℤ, e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)
        = e2pi ((2 * α * k) * (n : ℝ) + α * (k : ℝ) ^ 2) := by
      intro n
      rw [quadratic_diff]
    simp only [hg]
    rw [sum_Ico_int_eq_sum_range]
    exact norm_geomSum_e2pi_le (hα k hk.1 hk.2) _ _
  have hsum := Finset.sum_le_sum hterm
  linarith

/-- The usable corollary: if the multiples `2αk` all stay at distance at least `δ` from the
integers, the sum exhibits square-root cancellation. -/
theorem normSq_sum_e2pi_quadratic_le_of_le (α δ : ℝ) (N H : ℕ) (hH : 0 < H) (hδ : 0 < δ)
    (hα : ∀ k : ℤ, 0 < k → k < (H : ℤ) → δ ≤ intDist (2 * α * k)) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + ((H : ℝ) - 1) / δ) / H := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hne : ∀ k : ℤ, 0 < k → k < (H : ℤ) → intDist (2 * α * k) ≠ 0 := by
    intro k hk hk'
    have := hα k hk hk'
    intro hcon
    rw [hcon] at this
    linarith
  have hmain := norm_sq_sum_e2pi_quadratic_le α N H hH hne
  have hbound : ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), 1 / (2 * intDist (2 * α * k))
      ≤ ((H : ℝ) - 1) * (1 / (2 * δ)) := by
    have hle : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        1 / (2 * intDist (2 * α * k)) ≤ 1 / (2 * δ) := by
      intro k hk
      rw [Finset.mem_Ioo] at hk
      have hd := hα k hk.1 hk.2
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Int.card_Ioo]
    have hcard : (((H : ℤ) - 0 - 1).toNat : ℝ) = (H : ℝ) - 1 := by
      have h : ((H : ℤ) - 0 - 1).toNat = H - 1 := by omega
      rw [h]
      have h1 : 1 ≤ H := hH
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcard]
  have hpos : (0 : ℝ) ≤ (N : ℝ) + H - 1 := by
    have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  rw [le_div_iff₀ hHpos]
  refine hmain.trans' ?_ |>.trans ?_
  · exact le_of_eq (by ring)
  · refine mul_le_mul_of_nonneg_left ?_ hpos
    have : 2 * (((H : ℝ) - 1) * (1 / (2 * δ))) = ((H : ℝ) - 1) / δ := by
      field_simp
    linarith [hbound, this]

end WeylQuadratic

end RiemannHypothesis
