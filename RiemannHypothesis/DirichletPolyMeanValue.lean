/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareAsymptotic

/-!
# The mean value theorem for Dirichlet polynomials with arbitrary coefficients

`RiemannHypothesis/DirichletPolyMeanSquare.lean` expands the mean square of a Dirichlet
polynomial `D(s) = ∑_{1 ≤ n ≤ N} a n · n ^ (-s)` into a diagonal term and an off-diagonal
remainder `offDiagSum a N σ`, and `RiemannHypothesis/StripMeanSquareAsymptotic.lean` makes the
comparison two-sided.  Both leave the off-diagonal remainder as an unevaluated double sum, and
so far it has only been estimated for the constant coefficients `a ≡ 1`.

Here the off-diagonal remainder is estimated for *arbitrary* coefficients.  The elementary
separation estimate `1/|log (n/m)| ≤ (m + n)/|n - m|` together with `2 b c ≤ b² + c²` and the
harmonic bound `∑_{n ≠ m, n ≤ N} 1/|n - m| ≤ 2 (1 + log N)` gives

`offDiagSum a N σ ≤ 8 N (1 + log N) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`,

and hence the classical **mean value theorem for Dirichlet polynomials**

`∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`,

with an explicit constant.  This is the elementary predecessor of the Montgomery–Vaughan mean
value theorem, which replaces the factor `N log N` by `n` inside the sum; the sharp form needs
Montgomery and Vaughan's generalized Hilbert inequality and is not proved here.

## Main results

* `sum_inv_abs_sub_le'` — the harmonic bound `∑_{n ≤ N, n ≠ m} 1/|n - m| ≤ 2 (1 + log N)`,
  in the `if`-form used by `offDiagSum`.
* `offDiagSum_le` — `offDiagSum a N σ ≤ 8 N (1 + log N) ∑ ‖a n‖² n^(-2σ)`.
* `abs_integral_normSq_dirichletPoly_sub_diag_le_mvt` — the mean value theorem, two-sided and
  with an explicit constant.
* `integral_normSq_dirichletPoly_mvt_zero` — the same on the imaginary axis `σ = 0`, in the
  familiar shape `∫₀ᵀ ‖∑ a n n^(-i t)‖² dt = (T + O(N log N)) ∑ ‖a n‖²`.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral

namespace RiemannHypothesis

/-! ## The harmonic bound in `if`-form -/

/-- The harmonic bound `∑_{n ≤ N, n ≠ m} 1/|n - m| ≤ 2 (1 + log N)`, written with the `if`
that appears in `offDiagSum`. -/
theorem sum_inv_abs_sub_le' {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 1 / |(n : ℝ) - (m : ℝ)|)
      ≤ 2 * (1 + Real.log N) := by
  classical
  have hrw : ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 1 / |(n : ℝ) - (m : ℝ)|)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≠ m), 1 / |(m : ℝ) - (n : ℝ)| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : m = n
    · simp [h]
    · rw [if_neg h, if_pos (fun hc : n = m => h hc.symm), abs_sub_comm]
  rw [hrw]
  exact sum_inv_abs_sub_le hm hmN

/-! ## The off-diagonal remainder for arbitrary coefficients -/

/-- Each off-diagonal term is at most `2 N (b m ^ 2 + b n ^ 2) / |n - m|`, where
`b k = ‖a k‖ k ^ (-σ)`. -/
theorem offDiag_term_le (a : ℕ → ℂ) (σ : ℝ) {N m n : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hmn : m ≠ n) :
    2 * (‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)))
        / |Real.log ((n : ℝ) / (m : ℝ))|
      ≤ 2 * (N : ℝ) * ((‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)
          + ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / |(n : ℝ) - (m : ℝ)|) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hne : (m : ℝ) ≠ (n : ℝ) := by exact_mod_cast hmn
  have hd : (0 : ℝ) < |(n : ℝ) - (m : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  set B := ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) with hB
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg hm0.le (-σ)
    have := Real.rpow_nonneg hn0.le (-σ)
    positivity
  -- separation of the logarithms
  have hsep : 1 / |Real.log ((n : ℝ) / (m : ℝ))| ≤ ((m : ℝ) + (n : ℝ)) / |(n : ℝ) - (m : ℝ)| :=
    inv_abs_log_div_le hm0 hn0 hne
  have hstep1 : 2 * B / |Real.log ((n : ℝ) / (m : ℝ))|
      ≤ 2 * B * (((m : ℝ) + (n : ℝ)) / |(n : ℝ) - (m : ℝ)|) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hsep (by linarith)
  -- `m + n ≤ 2 N`
  have hstep2 : 2 * B * (((m : ℝ) + (n : ℝ)) / |(n : ℝ) - (m : ℝ)|)
      ≤ 2 * B * ((2 * (N : ℝ)) / |(n : ℝ) - (m : ℝ)|) := by
    refine mul_le_mul_of_nonneg_left (by gcongr; linarith) (by linarith)
  -- `2 b c ≤ b² + c²`
  set b := ‖a m‖ * (m : ℝ) ^ (-σ) with hb
  set c := ‖a n‖ * (n : ℝ) ^ (-σ) with hc
  have hBbc : B = b * c := by rw [hB, hb, hc]; ring
  have hb2 : b ^ 2 = ‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) := by
    rw [hb, mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hm0.le]
    ring_nf
  have hc2 : c ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    rw [hc, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hn0.le]
    ring_nf
  have hamgm : 2 * B ≤ b ^ 2 + c ^ 2 := by
    rw [hBbc]; nlinarith [sq_nonneg (b - c)]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc 2 * B / |Real.log ((n : ℝ) / (m : ℝ))|
      ≤ 2 * B * ((2 * (N : ℝ)) / |(n : ℝ) - (m : ℝ)|) := hstep1.trans hstep2
    _ = (2 * B) * (2 * (N : ℝ)) / |(n : ℝ) - (m : ℝ)| := by ring
    _ ≤ (b ^ 2 + c ^ 2) * (2 * (N : ℝ)) / |(n : ℝ) - (m : ℝ)| := by
        gcongr
    _ = 2 * (N : ℝ) * ((b ^ 2 + c ^ 2) / |(n : ℝ) - (m : ℝ)|) := by ring
    _ = 2 * (N : ℝ) * ((‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)
          + ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / |(n : ℝ) - (m : ℝ)|) := by rw [hb2, hc2]

/-- **The off-diagonal remainder for arbitrary coefficients.**
`offDiagSum a N σ ≤ 8 N (1 + log N) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`. -/
theorem offDiagSum_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    offDiagSum a N σ
      ≤ 8 * (N : ℝ) * (1 + Real.log N)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  classical
  set w : ℕ → ℝ := fun k => ‖a k‖ ^ 2 * (k : ℝ) ^ (-2 * σ) with hw
  have hw0 : ∀ k, 1 ≤ k → 0 ≤ w k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have := Real.rpow_nonneg hk0.le (-2 * σ)
    rw [hw]; positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [offDiagSum]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  -- termwise bound
  have hterm : offDiagSum a N σ
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m = n then 0 else 2 * (N : ℝ) * ((w m + w n) / |(n : ℝ) - (m : ℝ)|)) := by
    rw [offDiagSum]
    refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    by_cases hmn : m = n
    · simp [hmn]
    · rw [if_neg hmn, if_neg hmn]
      exact offDiag_term_le a σ hm1 hmN hn1 hnN hmn
  -- split into the two halves
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 2 * (N : ℝ) * ((w m + w n)
          / |(n : ℝ) - (m : ℝ)|))
        = (∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 2 * (N : ℝ) * w m
            * (1 / |(n : ℝ) - (m : ℝ)|)))
          + ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 2 * (N : ℝ) * w n
            * (1 / |(n : ℝ) - (m : ℝ)|)) := by
    intro m _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hmn : m = n
    · simp [hmn]
    · rw [if_neg hmn, if_neg hmn, if_neg hmn]; ring
  refine hterm.trans ?_
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the first half: `w m` factors out
  have hA : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m = n then 0 else 2 * (N : ℝ) * w m * (1 / |(n : ℝ) - (m : ℝ)|))
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, w n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hfac : ∑ n ∈ Finset.Icc 1 N,
          (if m = n then 0 else 2 * (N : ℝ) * w m * (1 / |(n : ℝ) - (m : ℝ)|))
        = (2 * (N : ℝ) * w m)
            * ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 1 / |(n : ℝ) - (m : ℝ)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hmn : m = n
      · simp [hmn]
      · rw [if_neg hmn, if_neg hmn]
    rw [hfac]
    have hcoef : 0 ≤ 2 * (N : ℝ) * w m := by
      have := hw0 m hm1; positivity
    calc (2 * (N : ℝ) * w m)
          * ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else 1 / |(n : ℝ) - (m : ℝ)|)
        ≤ (2 * (N : ℝ) * w m) * (2 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left (sum_inv_abs_sub_le' hm1 hmN) hcoef
      _ = 4 * (N : ℝ) * (1 + Real.log N) * w m := by ring
  -- the second half: swap the order of summation
  have hB : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m = n then 0 else 2 * (N : ℝ) * w n * (1 / |(n : ℝ) - (m : ℝ)|))
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, w n := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hfac : ∑ m ∈ Finset.Icc 1 N,
          (if m = n then 0 else 2 * (N : ℝ) * w n * (1 / |(n : ℝ) - (m : ℝ)|))
        = (2 * (N : ℝ) * w n)
            * ∑ m ∈ Finset.Icc 1 N, (if n = m then 0 else 1 / |(m : ℝ) - (n : ℝ)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hmn : m = n
      · simp [hmn]
      · rw [if_neg hmn, if_neg (fun hc : n = m => hmn hc.symm), abs_sub_comm]
    rw [hfac]
    have hcoef : 0 ≤ 2 * (N : ℝ) * w n := by
      have := hw0 n hn1; positivity
    calc (2 * (N : ℝ) * w n)
          * ∑ m ∈ Finset.Icc 1 N, (if n = m then 0 else 1 / |(m : ℝ) - (n : ℝ)|)
        ≤ (2 * (N : ℝ) * w n) * (2 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left (sum_inv_abs_sub_le' hn1 hnN) hcoef
      _ = 4 * (N : ℝ) * (1 + Real.log N) * w n := by ring
  have hsum := add_le_add hA hB
  linarith

/-! ## The mean value theorem -/

/-- **The mean value theorem for Dirichlet polynomials.**  For every choice of coefficients,

`|∫₀ᵀ ‖∑_{n ≤ N} a n n^(-σ-i t)‖² dt - T ∑_{n ≤ N} ‖a n‖² n^(-2σ)|`
`  ≤ 8 N (1 + log N) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`,

i.e. `∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)` with an explicit
constant. -/
theorem abs_integral_normSq_dirichletPoly_sub_diag_le_mvt (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))|
      ≤ 8 * (N : ℝ) * (1 + Real.log N)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  (abs_integral_normSq_dirichletPoly_sub_diag_le a N σ T).trans (offDiagSum_le a N σ)

/-- The mean value theorem on the imaginary axis, in its familiar shape:
`∫₀ᵀ ‖∑_{n ≤ N} a n n^(-i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖²`. -/
theorem integral_normSq_dirichletPoly_mvt_zero (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := abs_integral_normSq_dirichletPoly_sub_diag_le_mvt a N 0 T
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * (0 : ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    norm_num
  rw [hsum] at h
  have hline : ((0 : ℝ) : ℂ) + (T : ℂ) * I = (T : ℂ) * I := by norm_num
  simpa [hline] using h

end RiemannHypothesis
