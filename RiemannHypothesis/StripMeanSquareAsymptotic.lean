/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareTrapezoid

/-!
# The asymptotic mean square of `ζ` inside the critical strip

`RiemannHypothesis.StripMeanSquareTrapezoid` proves the *upper bound*
`∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C_σ T` for `3/5 < σ < 1`.  This file upgrades it to the classical
*asymptotic* of Landau,

`∫₀ᵀ ‖ζ(σ + i t)‖² dt = ζ(2σ) T + O_σ(T^(1-c))`   for some `c = c(σ) > 0`,

in the same range.  Two ingredients are added to the ones already available.

* A **two-sided** mean value theorem for Dirichlet polynomials: the mean square of
  `∑_{n ≤ N} a n n^(-s)` differs from the diagonal term `T ∑_{n ≤ N} ‖a n‖² n^(-2σ)` by at most
  the off-diagonal remainder `offDiagSum`.  The existing
  `integral_normSq_dirichletPoly_le_diag_add_offDiag` is only an upper bound, because it
  estimates `re z ≤ ‖z‖`; here `|re z| ≤ ‖z‖` is used instead.
* The length of the Dirichlet polynomial is taken slightly *longer* than the one that optimizes
  the upper bound, namely `N ≍ T^e` with `2/(1+σ) < e < 1/(2-2σ)` — an interval which is
  non-empty exactly when `σ > 3/5`.  Every error term is then a power of `T` below `T`.

## Main results

* `abs_integral_normSq_dirichletPoly_sub_diag_le` — the two-sided mean value theorem.
* `exists_integral_normSq_riemannZeta_asymptotic` — the asymptotic with a power saving.
* `tendsto_integral_normSq_riemannZeta_div` — the asymptotic in limit form:
  `(1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt → ζ(2σ)`.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## A two-sided mean value theorem for Dirichlet polynomials -/

/-- The contribution of an off-diagonal pair `(m, n)` to the mean square, in absolute value. -/
theorem abs_integral_meanSquareTerm_re_le (a : ℕ → ℂ) (σ : ℝ) {T : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    |∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re|
      ≤ 2 * (‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)))
          / |Real.log ((n : ℝ) / (m : ℝ))| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K : ℂ := a m * (starRingEnd ℂ) (a n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hK
  set θ : ℝ := Real.log n - Real.log m with hθdef
  have hcont : Continuous (fun t : ℝ => meanSquareTerm a σ m n t) := by
    unfold meanSquareTerm; fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => meanSquareTerm a σ m n t)
      MeasureTheory.volume 0 T := hcont.intervalIntegrable 0 T
  have h1 : (∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re)
      = (∫ t in (0 : ℝ)..T, meanSquareTerm a σ m n t).re := by
    simpa using ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
  have h2 : (∫ t in (0 : ℝ)..T, meanSquareTerm a σ m n t)
      = K * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I) := by
    rw [← intervalIntegral.integral_const_mul]; rfl
  have hKnorm : ‖K‖ = ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by
    rw [hK]
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.rpow_pos_of_pos hm0 _), abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  have hθ0 : θ ≠ 0 := by
    rw [hθdef, sub_ne_zero]
    intro h
    have hnm : (n : ℝ) = (m : ℝ) := by rw [← Real.exp_log hn0, ← Real.exp_log hm0, h]
    exact hmn (by exact_mod_cast hnm.symm)
  have hlog : |Real.log ((n : ℝ) / (m : ℝ))| = |θ| := by
    rw [Real.log_div hn0.ne' hm0.ne', hθdef]
  have hle : |∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re|
      ≤ ‖K‖ * ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := by
    rw [h1, h2]
    calc |(K * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)).re|
        ≤ ‖K * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := Complex.abs_re_le_norm _
      _ = ‖K‖ * ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := norm_mul _ _
  refine hle.trans ?_
  rw [hlog, hKnorm]
  have hbd := norm_integral_exp_mul_I_le (T := T) hθ0
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hθ0
  have hK0 : (0 : ℝ) ≤ ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by positivity
  calc ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
        * ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖
      ≤ ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) * (2 / |θ|) := by gcongr
    _ = 2 * (‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))) / |θ| := by ring

/-- `n^(-σ) · n^(-σ) = n^(-2σ)`, valid also at `n = 0`. -/
theorem rpow_neg_mul_self (n : ℕ) (σ : ℝ) :
    (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-2 * σ) := by
  rcases eq_or_ne σ 0 with hs | hs
  · simp [hs]
  · rw [show (-2 * σ) = (-σ) + (-σ) by ring,
      Real.rpow_add' (Nat.cast_nonneg n) (by intro h; exact hs (by linarith))]

/-- The diagonal contribution: for `m = n` the oscillating factor is `1`. -/
theorem integral_meanSquareTerm_re_diag (a : ℕ → ℂ) (σ : ℝ) (T : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..T, (meanSquareTerm a σ n n t).re) = T * (‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) := by
  have hval : ∀ t : ℝ, (meanSquareTerm a σ n n t).re
      = ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by
    intro t
    have hz : meanSquareTerm a σ n n t
        = ((‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
      simp only [meanSquareTerm, sub_self, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, mul_one, Complex.mul_conj]
      rw [Complex.sq_norm]
      push_cast
      ring
    rw [hz, Complex.ofReal_re]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ =>
    ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))) fun t _ => hval t,
    intervalIntegral.integral_const, rpow_neg_mul_self]
  simp [smul_eq_mul]

/-- **The two-sided mean value theorem for Dirichlet polynomials.**  The mean square of
`∑_{n ≤ N} a n n^(-s)` over `[0, T]` differs from the diagonal term
`T ∑_{n ≤ N} ‖a n‖² n^(-2σ)` by at most the off-diagonal remainder. -/
theorem abs_integral_normSq_dirichletPoly_sub_diag_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))|
      ≤ offDiagSum a N σ := by
  classical
  have hcont : ∀ m n : ℕ, Continuous (fun t : ℝ => (meanSquareTerm a σ m n t).re) := by
    intro m n
    unfold meanSquareTerm
    fun_prop
  have hstep : (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re := by
    rw [intervalIntegral.integral_congr (g := fun t => ∑ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, (meanSquareTerm a σ m n t).re)
      (fun t _ => normSq_dirichletPoly_eq a N σ t)]
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finset_sum]
      exact fun n _ => (hcont m n).intervalIntegrable 0 T
    · intro m _
      exact (continuous_finset_sum _ fun n _ => hcont m n).intervalIntegrable 0 T
  -- split each inner sum into its diagonal entry and the rest
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 N, ∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re)
        = T * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ))
          + ∑ n ∈ Finset.Icc 1 N, (if m = n then 0 else
              ∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re) := by
    intro m hm
    have hfun : ∀ n ∈ Finset.Icc 1 N,
        (∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re)
          = (if m = n then T * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)) else 0)
            + (if m = n then 0 else ∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re) := by
      intro n _
      by_cases hmn : m = n
      · subst hmn; rw [if_pos rfl, if_pos rfl, add_zero, integral_meanSquareTerm_re_diag]
      · rw [if_neg hmn, if_neg hmn, zero_add]
    rw [Finset.sum_congr rfl hfun, Finset.sum_add_distrib,
      Finset.sum_ite_eq (Finset.Icc 1 N) m (fun _ => T * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ))),
      if_pos hm]
  rw [hstep, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
    add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [offDiagSum]
  refine Finset.sum_le_sum fun m hm => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun n hn => ?_
  by_cases hmn : m = n
  · simp [hmn]
  · rw [if_neg hmn, if_neg hmn]
    exact abs_integral_meanSquareTerm_re_le a σ (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp hn).1 hmn

/-! ## The tail of the `p`-series -/

/-- The sum over `Icc 1 N` is the sum over `range N` of the shifted summand. -/
theorem sum_Icc_eq_sum_range_shift (f : ℝ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f (n : ℝ) = ∑ n ∈ Finset.range N, f ((n : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      push_cast
      ring_nf

/-- The partial sums of `∑ n^(-q)` approach the full sum with a power saving. -/
theorem abs_sum_Icc_rpow_neg_sub_tsum_le {q : ℝ} (hq : 1 < q) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-q)) - ∑' n : ℕ, ((n : ℝ) + 1) ^ (-q)|
      ≤ (N : ℝ) ^ (1 - q) / (q - 1) := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-q)) := summable_natAddOne_rpow_neg hq
  have hrange : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-q)
      = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-q) :=
    sum_Icc_eq_sum_range_shift (fun x => x ^ (-q)) N
  have hsplit : (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-q))
      + ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-q) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-q) := by
    have := hsum.sum_add_tsum_nat_add N
    simpa using this
  have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-q) ≤ (N : ℝ) ^ (1 - q) / (q - 1) :=
    tsum_shift_rpow_neg_le_rpow hq hN
  have htail0 : 0 ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-q) :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  rw [hrange, ← hsplit, abs_sub_comm]
  rw [show (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-q))
      + (∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-q))
      - ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-q)
      = ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-q) by ring, abs_of_nonneg htail0]
  exact htail

/-! ## Comparing the mean square of `ζ` with that of the Dirichlet polynomial -/

/-- The Dirichlet polynomial is continuous along a vertical line. -/
theorem continuous_dirichletPoly_line {σ : ℝ} (N : ℕ) :
    Continuous (fun t : ℝ => dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)) := by
  unfold dirichletPoly
  refine continuous_finset_sum _ fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  have hc : Continuous (fun t : ℝ => ((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
    refine Continuous.cpow continuous_const (by fun_prop) ?_
    intro t
    left
    simpa using hn0
  simpa using hc

/-- The elementary inequality behind the comparison: if `|z - p| ≤ e` then `z²` and `p²`
differ by at most `ε p² + e²/ε + e²`, for every `ε > 0`. -/
theorem abs_sq_sub_sq_le_of_abs_sub_le {p z e ε : ℝ} (hp : 0 ≤ p) (hz : 0 ≤ z)
    (hd : |z - p| ≤ e) (hε : 0 < ε) :
    |z ^ 2 - p ^ 2| ≤ ε * p ^ 2 + e ^ 2 / ε + e ^ 2 := by
  have he : 0 ≤ e := le_trans (abs_nonneg _) hd
  have h1 : z - p ≤ e := (abs_le.mp hd).2
  have h2 : -e ≤ z - p := (abs_le.mp hd).1
  have hkey : 2 * p * e ≤ ε * p ^ 2 + e ^ 2 / ε := by
    rw [← sub_nonneg]
    have hpos : (0 : ℝ) < ε := hε
    have hid : ε * p ^ 2 + e ^ 2 / ε - 2 * p * e = (ε * p - e) ^ 2 / ε := by
      field_simp
      ring
    rw [hid]
    positivity
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z - p), sq_nonneg (z + p), mul_nonneg hp he]

/-- The mean square of the trapezoidal error term. -/
theorem integral_normSq_error_trap_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2))
        + 3 * (((N : ℝ) + 1) ^ (-(2 * σ)) / 4) * T
        + 3 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ))
            / (64 * (1 + σ) ^ 2)) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set B : ℝ := (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2)
    with hB
  set C : ℝ := ((N : ℝ) + 1) ^ (-(2 * σ)) / 4 with hC
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))) + 3 * C + 3 * B := by
    rintro t ⟨ht0, htT⟩
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hs]
      simp [Complex.normSq_apply]
      ring
    have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
      have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
      nlinarith [norm_nonneg (s - 1), hnormsq]
    have hbd := norm_riemannZeta_sub_dirichletPoly_le_trap h0 h1 hN t
    set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
    set E2 : ℝ := ((N : ℝ) + 1) ^ (-σ) / 2 with hE2
    set E3 : ℝ := (σ + |t|) * (1 + σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ)) with hE3
    have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
    have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
    have hE30 : 0 ≤ E3 := by rw [hE3]; positivity
    have hsq : ‖riemannZeta s - dirichletPoly (fun _ => 1) N s‖ ^ 2
        ≤ 3 * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2) := by
      nlinarith [norm_nonneg (riemannZeta s - dirichletPoly (fun _ => 1) N s), hbd,
        sq_nonneg (E1 - E2), sq_nonneg (E1 - E3), sq_nonneg (E2 - E3), hE10, hE20, hE30]
    have hE1sq : E1 ^ 2 = A * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
      rw [hE1, div_pow, hnormsq, hA, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hE2sq : E2 ^ 2 = C := by
      rw [hE2, hC, div_pow, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (-σ)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hE3sq : E3 ^ 2 ≤ B := by
      have hpow : ((N : ℝ) ^ (-(1 + σ))) ^ 2 = (N : ℝ) ^ (-(2 + 2 * σ)) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 + σ))) 2, ← Real.rpow_mul hN0.le]
        norm_num
        ring_nf
      have habs : |t| = t := abs_of_nonneg ht0
      have hCn : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 + σ)) := Real.rpow_nonneg hN0.le _
      rw [hE3, habs, hB]
      calc ((σ + t) * (1 + σ + t) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ))) ^ 2
          = (σ + t) ^ 2 * (1 + σ + t) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / (64 * (1 + σ) ^ 2) := by
            rw [div_pow]
            ring_nf
        _ ≤ (σ + T) ^ 2 * (1 + σ + T) ^ 2 * ((N : ℝ) ^ (-(1 + σ))) ^ 2 / (64 * (1 + σ) ^ 2) := by
            gcongr
        _ = (σ + T) ^ 2 * (1 + σ + T) ^ 2 * (N : ℝ) ^ (-(2 + 2 * σ)) / (64 * (1 + σ) ^ 2) := by
            rw [hpow]
    linarith [hsq, hE1sq, hE2sq, hE3sq]
  -- integrate
  have hdiff : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    (((continuous_riemannZeta_line_of_lt_one h1).sub
      (continuous_dirichletPoly_line N)).norm).pow 2
  have hcont1 : Continuous (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) :=
    Continuous.div continuous_const (by fun_prop) fun t => by
      have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by
        have : (0 : ℝ) < (1 - σ) ^ 2 := pow_pos (by linarith) 2
        nlinarith [sq_nonneg t]
      exact ne_of_gt hpos
  have hi1 : IntervalIntegrable (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))))
      volume 0 T :=
    (continuous_const.mul (continuous_const.mul hcont1)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun _ : ℝ => 3 * C) volume 0 T :=
    intervalIntegrable_const
  have hi3 : IntervalIntegrable (fun _ : ℝ => 3 * B) volume 0 T :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hdiff.intervalIntegrable 0 T)
    ((hi1.add hi2).add hi3) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hphi : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero]
  nlinarith [hphi, hA0]

/-- The integrated comparison of the mean square of `ζ` with that of a Dirichlet polynomial. -/
theorem abs_integral_normSq_riemannZeta_sub_dirichletPoly_le {σ : ℝ} (h1 : σ < 1) (N : ℕ)
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|
      ≤ ε * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / ε
        + ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hz : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    continuous_normSq_riemannZeta_line_of_lt_one h1
  have hp : Continuous (fun t : ℝ => ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    continuous_normSq_dirichletPoly_line N
  have he : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    (((continuous_riemannZeta_line_of_lt_one h1).sub
      (continuous_dirichletPoly_line N)).norm).pow 2
  have hsub : (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      - (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      = ∫ t in (0 : ℝ)..T, (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          - ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    (intervalIntegral.integral_sub (hz.intervalIntegrable 0 T) (hp.intervalIntegrable 0 T)).symm
  rw [hsub]
  have hstep1 : |∫ t in (0 : ℝ)..T, (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        - ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)|
      ≤ ∫ t in (0 : ℝ)..T, |‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          - ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2| :=
    intervalIntegral.abs_integral_le_integral_abs hT
  refine hstep1.trans ?_
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      |‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          - ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|
        ≤ ε * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
              - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / ε
          + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
              - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t _
    refine abs_sq_sub_sq_le_of_abs_sub_le (norm_nonneg _) (norm_nonneg _) ?_ hε
    rw [abs_le]
    constructor
    · have := norm_sub_norm_le (dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I))
        (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
      rw [norm_sub_rev] at this
      linarith
    · have := norm_sub_norm_le (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
        (dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I))
      linarith
  have hi1 : IntervalIntegrable (fun t : ℝ => |‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      - ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|) volume 0 T :=
    ((hz.sub hp).abs).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t : ℝ =>
      ε * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / ε
        + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    (((continuous_const.mul hp).add (he.div_const ε)).add he).intervalIntegrable 0 T
  refine (intervalIntegral.integral_mono_on hT hi1 hi2 hpt).trans_eq ?_
  have hA : IntervalIntegrable
      (fun t : ℝ => ε * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume 0 T := (continuous_const.mul hp).intervalIntegrable 0 T
  have hB : IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / ε)
      volume 0 T := (he.div_const ε).intervalIntegrable 0 T
  have hC : IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume 0 T := he.intervalIntegrable 0 T
  rw [intervalIntegral.integral_add (hA.add hB) hC, intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div]

/-! ## Absorbing a logarithm into a power -/

/-- `1 + log T = O(T^γ)` for every `γ > 0`. -/
theorem exists_one_add_log_le_rpow {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → 1 + Real.log T ≤ C * T ^ γ := by
  set g : ℝ := min γ (1 / 2) with hg
  have hg0 : 0 < g := lt_min hγ (by norm_num)
  have hg1 : g ≤ 1 / 2 := min_le_right _ _
  have hgγ : g ≤ γ := min_le_left _ _
  obtain ⟨C, hC, h⟩ := exists_rpow_mul_one_add_log_le (a := 1 - g) (by linarith)
  refine ⟨C, hC, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hpos : (0 : ℝ) < T ^ (1 - g) := Real.rpow_pos_of_pos hT0 _
  have hTg : T ^ (1 - g) * T ^ g = T := by
    rw [← Real.rpow_add hT0]
    simp
  have hstep : T ^ (1 - g) * (1 + Real.log T) ≤ T ^ (1 - g) * (C * T ^ g) := by
    have := h T hT
    calc T ^ (1 - g) * (1 + Real.log T) ≤ C * T := this
      _ = T ^ (1 - g) * (C * T ^ g) := by
          rw [show T ^ (1 - g) * (C * T ^ g) = C * (T ^ (1 - g) * T ^ g) by ring, hTg]
  have hle : 1 + Real.log T ≤ C * T ^ g := le_of_mul_le_mul_left hstep hpos
  refine hle.trans ?_
  have : T ^ g ≤ T ^ γ := Real.rpow_le_rpow_of_exponent_le hT hgγ
  nlinarith

/-! ## Elementary estimates used in the asymptotic -/

/-- `T^(-r) · T = T^(1-r)`. -/
private theorem rpow_neg_mul_base {T : ℝ} (hT : 0 < T) (r : ℝ) :
    T ^ (-r) * T = T ^ (1 - r) := by
  have h : T ^ (-r) * T ^ (1 : ℝ) = T ^ (-r + 1) := (Real.rpow_add hT _ _).symm
  rw [Real.rpow_one] at h
  rw [h, show -r + 1 = 1 - r by ring]

/-- If `y ≤ c x` with `c ≥ 1` and the exponent `r` lies in `[0, 2]`, then `y^r ≤ c² x^r`. -/
private theorem rpow_le_sq_mul {c x y r : ℝ} (hc : 1 ≤ c) (hx : 0 < x) (hy : 0 ≤ y)
    (hyc : y ≤ c * x) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) : y ^ r ≤ c ^ 2 * x ^ r := by
  have h1 : y ^ r ≤ (c * x) ^ r := Real.rpow_le_rpow hy hyc hr0
  rw [Real.mul_rpow (by linarith) hx.le] at h1
  have h2 : c ^ r ≤ c ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hr2
  have h3 : c ^ (2 : ℝ) = c ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at h2
  have h4 : (0 : ℝ) ≤ x ^ r := Real.rpow_nonneg hx.le r
  nlinarith

/-- Absorbing the factor `2` inside a logarithm. -/
private theorem one_add_log_le_two_add_log {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y)
    (hyx : y ≤ 2 * x) : 1 + Real.log y ≤ 2 + Real.log x := by
  have hlog : Real.log y ≤ Real.log (2 * x) := Real.log_le_log hy hyx
  rw [Real.log_mul (by norm_num) (by linarith)] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

/-- Multiplying a bound `A ≤ a T^(1-g)` by a bound `L ≤ b T^(g/2)`. -/
private theorem prod_le_rpow_of_bounds {T A L a b g : ℝ} (hT : 0 < T) (hA0 : 0 ≤ A)
    (hL0 : 0 ≤ L) (hA : A ≤ a * T ^ (1 - g)) (hL : L ≤ b * T ^ (g / 2)) :
    A * L ≤ a * b * T ^ (1 - g / 2) := by
  have h1 : A * L ≤ a * T ^ (1 - g) * (b * T ^ (g / 2)) :=
    mul_le_mul hA hL hL0 (le_trans hA0 hA)
  have h2 : a * T ^ (1 - g) * (b * T ^ (g / 2)) = a * b * T ^ (1 - g / 2) := by
    rw [show a * T ^ (1 - g) * (b * T ^ (g / 2)) = a * b * (T ^ (1 - g) * T ^ (g / 2)) by ring,
      ← Real.rpow_add hT]
    congr 2
    ring
  linarith

/-- The three contributions to the mean square of the approximation error are all `O(T^(1-cs))`.
This is the arithmetic core of the estimate; it is stated purely in terms of real numbers. -/
private theorem error_terms_le {σ T K cs g1 g2 g3 E B2 B3 B4 : ℝ}
    (hT : 1 ≤ T) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hK : 0 < K)
    (hcs1 : cs ≤ g1) (hcs2 : cs ≤ g2) (hcs3 : cs ≤ g3)
    (hB2 : B2 ≤ 9 * T ^ (1 - g1)) (hB3 : B3 ≤ T ^ (-g2))
    (hB40 : 0 ≤ B4) (hB4 : B4 ≤ T ^ (-(4 + g3)))
    (hE : E ≤ 3 * (B2 * K) + 3 * (B3 / 4) * T
        + 3 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * B4 / (64 * (1 + σ) ^ 2)) * T) :
    E ≤ (27 * K + 1 + 3) * T ^ (1 - cs) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hTnn : ∀ r : ℝ, (0 : ℝ) ≤ T ^ r := fun r => Real.rpow_nonneg hT0.le r
  have hmono : ∀ u v : ℝ, u ≤ v → T ^ (1 - v) ≤ T ^ (1 - u) := fun u v h =>
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have t1 : 3 * (B2 * K) ≤ 27 * K * T ^ (1 - cs) := by
    have hb : B2 ≤ 9 * T ^ (1 - cs) := le_trans hB2 (by linarith [hmono cs g1 hcs1])
    nlinarith [hb, hK]
  have t2 : 3 * (B3 / 4) * T ≤ T ^ (1 - cs) := by
    have h1 : B3 * T ≤ T ^ (-g2) * T := mul_le_mul_of_nonneg_right hB3 hT0.le
    rw [rpow_neg_mul_base hT0] at h1
    have h := hmono cs g2 hcs2
    linarith [hTnn (1 - cs)]
  have t3 : 3 * ((σ + T) ^ 2 * (1 + σ + T) ^ 2 * B4 / (64 * (1 + σ) ^ 2)) * T
      ≤ 3 * T ^ (1 - cs) := by
    have hnum : (σ + T) ^ 2 * (1 + σ + T) ^ 2 ≤ 36 * T ^ (4 : ℕ) := by
      have hsq1 : (σ + T) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
      have hsq2 : (1 + σ + T) ^ 2 ≤ 9 * T ^ 2 := by nlinarith
      nlinarith
    have hstep : (σ + T) ^ 2 * (1 + σ + T) ^ 2 * B4 ≤ 36 * T ^ (4 : ℕ) * T ^ (-(4 + g3)) :=
      mul_le_mul hnum hB4 hB40 (by positivity)
    have hT2 : T ^ (4 : ℕ) * T ^ (-(4 + g3)) = T ^ (-g3) := by
      rw [← Real.rpow_natCast T 4, ← Real.rpow_add hT0]
      congr 1
      push_cast
      ring
    rw [show (36 : ℝ) * T ^ (4 : ℕ) * T ^ (-(4 + g3)) = 36 * (T ^ (4 : ℕ) * T ^ (-(4 + g3)))
      by ring, hT2] at hstep
    have hdiv : (σ + T) ^ 2 * (1 + σ + T) ^ 2 * B4 / (64 * (1 + σ) ^ 2) ≤ T ^ (-g3) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hstep, mul_nonneg (hTnn (-g3)) (by nlinarith : (0 : ℝ) ≤ 64 * (1 + σ) ^ 2 - 36)]
    have hmul := mul_le_mul_of_nonneg_right hdiv hT0.le
    rw [rpow_neg_mul_base hT0] at hmul
    have h := hmono cs g3 hcs3
    linarith
  linarith

/-- Turning the comparison inequality into a power saving, with `ε = T^(-c)` and `cs = 2c`. -/
private theorem comparison_bound {Z P E T a CE c : ℝ} (hT : 1 ≤ T) (hc : 0 < c)
    (hCE : 0 ≤ CE) (hcomp : |Z - P| ≤ T ^ (-c) * P + E / T ^ (-c) + E)
    (hP : P ≤ a * T) (hE : E ≤ CE * T ^ (1 - 2 * c)) :
    |Z - P| ≤ (a + 2 * CE) * T ^ (1 - c) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hε : (0 : ℝ) < T ^ (-c) := Real.rpow_pos_of_pos hT0 _
  have hmul : T ^ (1 - c) * T ^ (-c) = T ^ (1 - 2 * c) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have p1 : T ^ (-c) * P ≤ a * T ^ (1 - c) := by
    have h := mul_le_mul_of_nonneg_left hP hε.le
    rw [show T ^ (-c) * (a * T) = a * (T ^ (-c) * T) by ring, rpow_neg_mul_base hT0] at h
    exact h
  have p2 : E / T ^ (-c) ≤ CE * T ^ (1 - c) := by
    rw [div_le_iff₀ hε, show CE * T ^ (1 - c) * T ^ (-c) = CE * (T ^ (1 - c) * T ^ (-c)) by ring,
      hmul]
    exact hE
  have p3 : E ≤ CE * T ^ (1 - c) := by
    refine hE.trans (mul_le_mul_of_nonneg_left ?_ hCE)
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  linarith

/-- A three-step triangle inequality. -/
private theorem abs_sub_three (A B C D : ℝ) : |A - D| ≤ |A - B| + |B - C| + |C - D| := by
  have h1 := abs_sub_le A B D
  have h2 := abs_sub_le B C D
  linarith

/-! ## The asymptotic mean square of `ζ` -/

/-- The exponent used for the length of the Dirichlet polynomial: the midpoint of the interval
`(2/(1+σ), 1/(2-2σ))`, which is non-empty exactly when `σ > 3/5`. -/
def meanSquareExponent (σ : ℝ) : ℝ := (2 / (1 + σ) + 1 / (2 - 2 * σ)) / 2

theorem meanSquareExponent_gt {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    2 / (1 + σ) < meanSquareExponent σ := by
  have hσ1 : (0 : ℝ) < 1 + σ := by linarith
  have h2σ : (0 : ℝ) < 2 - 2 * σ := by linarith
  have hlt : 2 / (1 + σ) < 1 / (2 - 2 * σ) := by
    rw [div_lt_div_iff₀ hσ1 h2σ]
    nlinarith
  rw [meanSquareExponent]
  linarith

theorem meanSquareExponent_lt {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    meanSquareExponent σ < 1 / (2 - 2 * σ) := by
  have hσ1 : (0 : ℝ) < 1 + σ := by linarith
  have h2σ : (0 : ℝ) < 2 - 2 * σ := by linarith
  have hlt : 2 / (1 + σ) < 1 / (2 - 2 * σ) := by
    rw [div_lt_div_iff₀ hσ1 h2σ]
    nlinarith
  rw [meanSquareExponent]
  linarith

/-- **The asymptotic mean square of `ζ` on a vertical line with `3/5 < σ < 1`.**

`∫₀ᵀ ‖ζ(σ + i t)‖² dt = ζ(2σ) T + O_σ(T^(1-c))` for some `c = c(σ) > 0`; the value `ζ(2σ)` is
written here as the sum of the Dirichlet series `∑_{n ≥ 1} n^(-2σ)`, which converges since
`2σ > 1`. -/
theorem exists_integral_normSq_riemannZeta_asymptotic {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
          - (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))) * T| ≤ C * T ^ (1 - c) := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have hσ1 : (0 : ℝ) < 1 + σ := by linarith
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  set ee : ℝ := meanSquareExponent σ with hee
  have heeL : 2 / (1 + σ) < ee := meanSquareExponent_gt h0 h1
  have heeU : ee < 1 / (2 - 2 * σ) := meanSquareExponent_lt h0 h1
  have hee0 : (0 : ℝ) < ee := lt_trans (by positivity) heeL
  -- the four power savings
  set g1 : ℝ := 1 - ee * (2 - 2 * σ) with hg1def
  set g2 : ℝ := 2 * σ * ee with hg2def
  set g3 : ℝ := ee * (2 + 2 * σ) - 4 with hg3def
  set g4 : ℝ := ee * (2 * σ - 1) with hg4def
  have hg1 : 0 < g1 := by
    rw [hg1def]
    nlinarith [(lt_div_iff₀ (by linarith : (0 : ℝ) < 2 - 2 * σ)).mp heeU]
  have hg2 : 0 < g2 := by rw [hg2def]; positivity
  have hg3 : 0 < g3 := by
    rw [hg3def]
    have h := (div_lt_iff₀ hσ1).mp heeL
    nlinarith
  have hg4 : 0 < g4 := by rw [hg4def]; nlinarith
  set cs : ℝ := min (min (g1 / 2) g2) (min g3 g4) with hcsdef
  have hcs : 0 < cs := by
    rw [hcsdef]
    exact lt_min (lt_min (by linarith) hg2) (lt_min hg3 hg4)
  have hcs1 : cs ≤ g1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcs2 : cs ≤ g2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcs3 : cs ≤ g3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcs4 : cs ≤ g4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set c : ℝ := cs / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  -- the constants
  obtain ⟨C₁, hC₁, hoff⟩ := offDiagSum_one_le (by linarith : (1 : ℝ) / 2 < σ) h1
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le (by linarith : (1 : ℝ) / 2 < σ) h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_one_add_log_le_rpow (γ := g1 / 2) (by linarith)
  set K : ℝ := Real.pi / 2 / (1 - σ) ^ 2 with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    exact div_pos (by positivity) (pow_pos (by linarith) 2)
  set S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) with hSdef
  set CD : ℝ := 4 * ((2 + ee) * C₃) with hCDdef
  have hCD : 0 < CD := by rw [hCDdef]; positivity
  set CE : ℝ := 27 * K + 1 + 3 with hCEdef
  have hCE : 0 < CE := by rw [hCEdef]; positivity
  have hlast : (0 : ℝ) < 1 / (2 * σ - 1) := div_pos one_pos (by linarith)
  refine ⟨C₂ * (1 + CD) + 2 * CE + C₁ * CD + 1 / (2 * σ - 1), c,
    by nlinarith [mul_pos hC₂ (by linarith : (0:ℝ) < 1 + CD), mul_pos hC₁ hCD], hc, ?_⟩
  intro T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hmono : ∀ u v : ℝ, u ≤ v → T ^ (1 - v) ≤ T ^ (1 - u) := fun u v h =>
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  set x : ℝ := T ^ ee with hxdef
  have hpowT : ∀ r : ℝ, x ^ r = T ^ (ee * r) := fun r => by
    rw [hxdef]; exact (Real.rpow_mul hT0.le ee r).symm
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hT hee0.le
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨N, hN1, hxN, hNx⟩ : ∃ N : ℕ, 1 ≤ N ∧ x ≤ (N : ℝ) ∧ (N : ℝ) ≤ x + 1 := by
    refine ⟨⌈x⌉₊, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one hx0.le).le⟩
    have h := le_trans hx1 (Nat.le_ceil x)
    exact_mod_cast h
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- the power estimates
  have hxa : x ^ (2 - 2 * σ) = T ^ (1 - g1) := by
    rw [hpowT]; congr 1; rw [hg1def]; ring
  have hB1 : (N : ℝ) ^ (2 - 2 * σ) ≤ 4 * T ^ (1 - g1) := by
    have h := rpow_le_sq_mul (c := 2) (r := 2 - 2 * σ) (by norm_num) hx0 hN0.le (by linarith)
      (by linarith) (by linarith)
    rw [hxa] at h
    linarith [h]
  have hB2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 9 * T ^ (1 - g1) := by
    have h := rpow_le_sq_mul (c := 3) (y := (N : ℝ) + 1) (r := 2 - 2 * σ) (by norm_num) hx0
      (by linarith) (by linarith) (by linarith) (by linarith)
    rw [hxa] at h
    linarith [h]
  have hB3 : ((N : ℝ) + 1) ^ (-(2 * σ)) ≤ T ^ (-g2) := by
    calc ((N : ℝ) + 1) ^ (-(2 * σ)) ≤ x ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
      _ = T ^ (-g2) := by rw [hpowT]; congr 1; rw [hg2def]; ring
  have hB4 : (N : ℝ) ^ (-(2 + 2 * σ)) ≤ T ^ (-(4 + g3)) := by
    calc (N : ℝ) ^ (-(2 + 2 * σ)) ≤ x ^ (-(2 + 2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
      _ = T ^ (-(4 + g3)) := by rw [hpowT]; congr 1; rw [hg3def]; ring
  have hB5 : (N : ℝ) ^ (1 - 2 * σ) ≤ T ^ (-g4) := by
    calc (N : ℝ) ^ (1 - 2 * σ) ≤ x ^ (1 - 2 * σ) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
      _ = T ^ (-g4) := by rw [hpowT]; congr 1; rw [hg4def]; ring
  have hB6 : 1 + Real.log N ≤ (2 + ee) * C₃ * T ^ (g1 / 2) := by
    have hlogx : Real.log x = ee * Real.log T := by rw [hxdef]; exact Real.log_rpow hT0 ee
    have h := one_add_log_le_two_add_log hx1 hN0 (by linarith)
    rw [hlogx] at h
    have hL := hlog T hT
    have hE : (2 : ℝ) + ee * Real.log T ≤ (2 + ee) * (1 + Real.log T) := by linarith
    calc 1 + Real.log N ≤ (2 + ee) * (1 + Real.log T) := by linarith
      _ ≤ (2 + ee) * (C₃ * T ^ (g1 / 2)) := by
          exact mul_le_mul_of_nonneg_left hL (by linarith)
      _ = (2 + ee) * C₃ * T ^ (g1 / 2) := by ring
  -- the four estimates
  have hD1 : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ CD * T ^ (1 - cs) := by
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
    have hstep := prod_le_rpow_of_bounds (T := T) (A := (N : ℝ) ^ (2 - 2 * σ))
      (L := 1 + Real.log N) (a := 4) (b := (2 + ee) * C₃) (g := g1) hT0
      (Real.rpow_nonneg hN0.le _) (by linarith) hB1 hB6
    rw [show (4 : ℝ) * ((2 + ee) * C₃) = CD from hCDdef.symm] at hstep
    refine hstep.trans (mul_le_mul_of_nonneg_left (hmono cs (g1 / 2) hcs1) hCD.le)
  have hD2 : (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ C₂ * (1 + CD) * T := by
    have hle : T ^ (1 - cs) ≤ T := by
      calc T ^ (1 - cs) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
        _ = T := Real.rpow_one T
    have h2 : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ CD * T :=
      hD1.trans (mul_le_mul_of_nonneg_left hle hCD.le)
    calc (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)) := hpoly N hN1 T hT0.le
      _ ≤ C₂ * (T + CD * T) := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
      _ = C₂ * (1 + CD) * T := by ring
  have hD3 : offDiagSum (fun _ => 1) N σ ≤ C₁ * CD * T ^ (1 - cs) := by
    calc offDiagSum (fun _ => 1) N σ ≤ C₁ * (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) :=
          hoff N hN1
      _ = C₁ * ((N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)) := by ring
      _ ≤ C₁ * (CD * T ^ (1 - cs)) := mul_le_mul_of_nonneg_left hD1 hC₁.le
      _ = C₁ * CD * T ^ (1 - cs) := by ring
  have hD4 : (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ CE * T ^ (1 - cs) := by
    have hmain := integral_normSq_error_trap_le hs0 h1 hN1 hT0.le
    rw [← hKdef] at hmain
    rw [hCEdef]
    exact error_terms_le hT hs0 h1 hK0 (le_trans hcs1 (by linarith)) hcs2 hcs3 hB2 hB3
      (Real.rpow_nonneg hN0.le _) hB4 hmain
  -- the tail of the Dirichlet series
  have hD5 : |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S| ≤ T ^ (-g4) / (2 * σ - 1) := by
    have h := abs_sum_Icc_rpow_neg_sub_tsum_le (q := 2 * σ) h2σ hN1
    have hd : (0 : ℝ) < 2 * σ - 1 := by linarith
    have hle : (N : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) ≤ T ^ (-g4) / (2 * σ - 1) := by
      have hmul := mul_le_mul_of_nonneg_right hB5 (le_of_lt (inv_pos.mpr hd))
      simpa [div_eq_mul_inv] using hmul
    rw [hSdef]
    linarith [h, hle]
  -- assembling
  have hcomp := abs_integral_normSq_riemannZeta_sub_dirichletPoly_le h1 N hT0.le
    (ε := T ^ (-c)) (Real.rpow_pos_of_pos hT0 _)
  have hdiag := abs_integral_normSq_dirichletPoly_sub_diag_le (fun _ => 1) N σ T
  have hone : (∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
      = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (-2 * σ : ℝ) = -(2 * σ) by ring]
    simp
  rw [hone] at hdiag
  have hE3 : T ^ (1 - cs) ≤ T ^ (1 - c) := hmono c cs (by rw [hcdef]; linarith)
  have hstep1 : |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      - ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|
      ≤ (C₂ * (1 + CD) + 2 * CE) * T ^ (1 - c) := by
    refine comparison_bound hT hc hCE.le hcomp hD2 ?_
    rw [show (1 : ℝ) - 2 * c = 1 - cs by rw [hcdef]; ring]
    exact hD4
  have hstep2 : |(∫ t in (0 : ℝ)..T,
      ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      - T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)))| ≤ C₁ * CD * T ^ (1 - c) := by
    refine hdiag.trans (hD3.trans ?_)
    exact mul_le_mul_of_nonneg_left hE3 (by positivity)
  have hstep3 : |T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S * T|
      ≤ 1 / (2 * σ - 1) * T ^ (1 - c) := by
    have heq : T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S * T
        = T * ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S) := by ring
    rw [heq, abs_mul, abs_of_pos hT0]
    have hstep : T * |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ))) - S|
        ≤ T * (T ^ (-g4) / (2 * σ - 1)) := mul_le_mul_of_nonneg_left hD5 hT0.le
    refine hstep.trans ?_
    have hTg4 : T ^ (-g4) * T = T ^ (1 - g4) := rpow_neg_mul_base hT0 g4
    have hle : T ^ (1 - g4) ≤ T ^ (1 - c) := hmono c g4 (by rw [hcdef]; linarith)
    have heq2 : T * (T ^ (-g4) / (2 * σ - 1)) = T ^ (1 - g4) / (2 * σ - 1) := by
      rw [← hTg4]; ring
    have hd : (0 : ℝ) < 2 * σ - 1 := by linarith
    have hne : (2 * σ - 1) ≠ 0 := ne_of_gt hd
    rw [heq2, div_le_iff₀ hd]
    have hfin : 1 / (2 * σ - 1) * T ^ (1 - c) * (2 * σ - 1) = T ^ (1 - c) := by
      field_simp
    rw [hfin]
    exact hle
  have htri := abs_sub_three (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (T * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)))) (S * T)
  linarith [htri, hstep1, hstep2, hstep3]

/-! ## The asymptotic in limit form -/

/-- The constant of the mean square is `ζ(2σ)`: for `2σ > 1` the real series `∑ (n+1)^(-2σ)`
is the value of the Riemann zeta function at `2σ`. -/
theorem ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta {σ : ℝ} (h : 1 < 2 * σ) :
    ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) : ℝ) : ℂ) = riemannZeta ((2 * σ : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using h), Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  rw [one_div, ← Complex.cpow_neg]

/-- **The mean square of `ζ` in limit form**: for `3/5 < σ < 1`,
`(1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt → ζ(2σ)` as `T → ∞`.  The limit is written as the real series
`∑ (n+1)^(-2σ)`, which `ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta` identifies with `ζ(2σ)`. -/
theorem tendsto_integral_normSq_riemannZeta_div {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
      Filter.atTop (nhds (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := exists_integral_normSq_riemannZeta_asymptotic h0 h1
  set S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) with hS
  refine tendsto_sub_nhds_zero_iff.mp ?_
  have hbound : ∀ᶠ T : ℝ in Filter.atTop,
      ‖(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T - S‖
        ≤ C * T ^ (-c) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := by linarith
    set J : ℝ := ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hJ
    have hsplit : J / T - S = (J - S * T) / T := by field_simp
    have hTc : T ^ (1 - c) = T * T ^ (-c) := by
      rw [show (1 : ℝ) - c = 1 + -c by ring, Real.rpow_add hT0, Real.rpow_one]
    rw [Real.norm_eq_abs, hsplit, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
    calc |J - S * T| ≤ C * T ^ (1 - c) := hbd T hT
      _ = C * T ^ (-c) * T := by rw [hTc]; ring
  refine squeeze_zero_norm' hbound ?_
  simpa using (tendsto_rpow_neg_atTop hc).const_mul C

end RiemannHypothesis
