/-
# Dirichlet polynomials as exponential sums with well-spaced frequencies

Two mean value theorems live in this repository and they had no formal connection.

* `RiemannHypothesis/GaussianMeanValue.lean` proves it for *Dirichlet polynomials*
  `D(s) = ∑_{n ≤ N} a_n n^{-s}` directly, in Montgomery–Vaughan shape with the error inside
  the sum: `∫₋ᵀᵀ ‖D(σ + i t)‖² dt ≤ 58 ∑_{n ≤ N} ‖a_n‖² n^{-2σ} (T + n)` for `T ≥ 6`.
* `RiemannHypothesis/MeanValueWellSpaced.lean` proves it for a *general* exponential sum
  `∑_r x_r e^{i λ_r t}` whose frequencies are `δ`-separated:
  `∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ 18 (T + 1/δ) ∑_r ‖x_r‖²`.

This file supplies the bridge, which is the arithmetic input of Montgomery–Vaughan's
corollary: **the frequencies of a Dirichlet polynomial of length `N` are `1/N`-separated**.
The smallest gap between the logarithms `log 1, …, log N` is `log N − log (N−1)`, and
`log n − log m ≥ 1 − m/n ≥ 1/n ≥ 1/N` for `m < n ≤ N`.

Composing the bridge with the general theorem gives the log-free bound

  `∫₀ᵀ ‖D(σ + i t)‖² dt ≤ 18 (T + N) ∑_{n ≤ N} ‖a_n‖² n^{-2σ}`,

valid for every `T > 0` (the Dirichlet-specific route needs `T ≥ 6`) and with the better
constant, at the price of the uniform `N` in place of the individual `n`.  Neither bound has
a factor `log N`: that logarithm, which the elementary expansion of the square in
`RiemannHypothesis/DirichletPolyMeanSquare.lean` cannot avoid, is what the Gaussian majorant
removes.

What is still *not* here is Montgomery and Vaughan's generalized Hilbert inequality
`|∑_{r ≠ s} x_r \bar x_s / (λ_r − λ_s)| ≤ (π/δ) ∑ ‖x_r‖²` and hence the sharp constant `1` on
the main term; both mean value theorems above carry explicit but non-optimal constants.

## Main results

* `separated_neg_log` — the frequencies `−log n`, `1 ≤ n ≤ N`, are `1/N`-separated.
* `dirichletPoly_line_eq_expSum` — on a vertical line a Dirichlet polynomial *is* an
  exponential sum with those frequencies.
* `integral_normSq_dirichletPoly_le_wellSpaced` — the resulting log-free mean square bound.
* `integral_normSq_dirichletPoly_le_wellSpaced_zero` — its `σ = 0` case,
  `∫₀ᵀ ‖∑ a_n n^{-it}‖² dt ≤ 18 (T + N) ∑ ‖a_n‖²`.
-/
import RiemannHypothesis.DirichletPolyMeanSquare
import RiemannHypothesis.MeanValueWellSpaced

noncomputable section

open Complex Finset
open scoped Topology

namespace RiemannHypothesis

/-! ## The logarithms of `1, …, N` are `1/N`-separated -/

/-- For positive `m, n` one has `log n − log m ≥ 1 − m/n`, by `log x ≤ x − 1` at `x = m/n`. -/
theorem one_sub_div_le_log_sub_log {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    1 - m / n ≤ Real.log n - Real.log m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hm hn)
  rw [Real.log_div hm.ne' hn.ne'] at h
  linarith

/-- **The frequencies of a Dirichlet polynomial of length `N` are `1/N`-separated.**
For distinct `m, n ∈ [1, N]` the gap `|log m − log n|` is at least `1/N`. -/
theorem separated_neg_log {N : ℕ} (hN : 1 ≤ N) :
    WellSpaced.Separated (Finset.Icc 1 N) (fun n : ℕ => -Real.log n) (1 / (N : ℝ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have key : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N, m < n →
      1 / (N : ℝ) ≤ Real.log n - Real.log m := by
    intro m hm n hn hmn
    simp only [Finset.mem_Icc] at hm hn
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
    have h1 : 1 / (N : ℝ) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn0 hnN
    have h2 : 1 / (n : ℝ) ≤ 1 - (m : ℝ) / (n : ℝ) := by
      rw [le_sub_iff_add_le, div_add_div _ _ hn0.ne' hn0.ne', div_le_one (by positivity)]
      nlinarith
    exact h1.trans (h2.trans (one_sub_div_le_log_sub_log hm0 hn0))
  intro r hr s hs hrs
  rcases lt_or_gt_of_ne hrs with h | h
  · have hkey := key r hr s hs h
    have habs : |(-Real.log r) - (-Real.log s)| = Real.log s - Real.log r := by
      rw [show (-Real.log r) - (-Real.log s) = Real.log s - Real.log r by ring]
      exact abs_of_nonneg (by linarith)
    rw [habs]; exact hkey
  · have hkey := key s hs r hr h
    have habs : |(-Real.log r) - (-Real.log s)| = Real.log r - Real.log s := by
      rw [show (-Real.log r) - (-Real.log s) = Real.log s - Real.log r by ring, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [habs]; exact hkey

/-! ## A Dirichlet polynomial on a vertical line is an exponential sum -/

/-- The coefficient of the exponential sum representing `D(σ + i ·)`: `a_n n^{-σ}`. -/
def dirichletLineWeight (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)

/-- **On the vertical line `Re s = σ` a Dirichlet polynomial is an exponential sum** with
frequencies `−log n` and coefficients `a_n n^{-σ}`. -/
theorem dirichletPoly_line_eq_expSum (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)
      = WellSpaced.expSum (Finset.Icc 1 N) (fun n : ℕ => -Real.log n)
          (dirichletLineWeight a σ) t := by
  rw [dirichletPoly, WellSpaced.expSum]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  rw [natCast_cpow_neg_line hn.1 σ t, dirichletLineWeight, ← mul_assoc]
  congr 2
  push_cast
  ring

/-- The squared norm of the exponential-sum coefficient is `‖a_n‖² n^{-2σ}`. -/
theorem norm_dirichletLineWeight_sq {n : ℕ} (hn : 1 ≤ n) (a : ℕ → ℂ) (σ : ℝ) :
    ‖dirichletLineWeight a σ n‖ ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : ‖(((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ = (n : ℝ) ^ (-σ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)]
  rw [dirichletLineWeight, norm_mul, hr, mul_pow,
    show -(2 * σ) = -σ + -σ by ring, Real.rpow_add hn0, sq]
  ring

/-! ## The log-free mean value theorem, via the well-spaced route -/

/-- **The mean value theorem for Dirichlet polynomials via well-spaced frequencies.**

For every `N ≥ 1`, every `T > 0` and every real `σ`,

`∫₀ᵀ ‖∑_{n ≤ N} a_n n^{-σ-it}‖² dt ≤ 18 (T + N) ∑_{n ≤ N} ‖a_n‖² n^{-2σ}`.

The error term is proportional to the same weighted sum of squares as the main term, with no
factor `log N`.  Compared with `integral_normSq_dirichletPoly_le_mv` of
`RiemannHypothesis/GaussianMeanValue.lean` this has the better constant and no lower bound on
`T`, but the coarser `N` in place of the individual `n`. -/
theorem integral_normSq_dirichletPoly_le_wellSpaced (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) {T : ℝ}
    (hT : 0 < T) (σ : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 18 * (T + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  rw [intervalIntegral.integral_congr (g := fun t =>
    ‖WellSpaced.expSum (Finset.Icc 1 N) (fun n : ℕ => -Real.log n)
      (dirichletLineWeight a σ) t‖ ^ 2)
    (fun t _ => by rw [dirichletPoly_line_eq_expSum])]
  have hmv := WellSpaced.integral_Ioc_normSq_expSum_le_mv (dirichletLineWeight a σ) hδ hT
    (separated_neg_log hN)
  have hsum : ∑ n ∈ Finset.Icc 1 N, ‖dirichletLineWeight a σ n‖ ^ 2
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
    Finset.sum_congr rfl fun n hn =>
      norm_dirichletLineWeight_sq (Finset.mem_Icc.mp hn).1 a σ
  rw [hsum] at hmv
  refine hmv.trans_eq ?_
  rw [one_div_one_div]

/-- The `σ = 0` case: `∫₀ᵀ ‖∑_{n ≤ N} a_n n^{-it}‖² dt ≤ 18 (T + N) ∑_{n ≤ N} ‖a_n‖²`.
This is the shape `∫₀ᵀ |D(i t)|² dt = ∑ ‖a_n‖² (T + O(n))` in its upper-bound half, with the
individual `O(n)` replaced by the uniform `O(N)` a length-`N` polynomial admits. -/
theorem integral_normSq_dirichletPoly_le_wellSpaced_zero (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
      ≤ 18 * (T + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := integral_normSq_dirichletPoly_le_wellSpaced a hN hT 0
  have hsum : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * (0 : ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by norm_num
  rw [hsum] at h
  simpa using h

end RiemannHypothesis

end
