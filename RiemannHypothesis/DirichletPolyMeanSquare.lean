/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The mean value theorem for Dirichlet polynomials

For a finite Dirichlet polynomial `D(s) = ∑_{1 ≤ n ≤ N} a n · n ^ (-s)` this file proves the
classical mean square bound

`∫₀ᵀ ‖D(σ + i t)‖² dt ≤ T ∑_{n ≤ N} ‖a n‖² n^(-2σ) + (off-diagonal terms)`,

where the off-diagonal contribution of a pair `m ≠ n` is
`2 ‖a m‖ ‖a n‖ (m n)^(-σ) / |log (n/m)|`.  The proof is the classical one: expand the square,
integrate term by term, and use `‖∫₀ᵀ e^{i t θ} dt‖ ≤ 2 / |θ|`.

## Main results

* `norm_integral_exp_mul_I_le` : `‖∫₀ᵀ exp (i t θ) dt‖ ≤ 2 / |θ|` for `θ ≠ 0`.
* `integral_normSq_dirichletPoly_le` : the mean square bound in its raw form, a double sum of
  pair kernels.
* `integral_normSq_dirichletPoly_le_diag_add_offDiag` : the same, split into the diagonal term
  `T ∑ ‖a n‖² n^(-2σ)` and the off-diagonal remainder.
-/

noncomputable section

open Complex Finset intervalIntegral
open scoped Topology

namespace RiemannHypothesis

/-- The Dirichlet polynomial `∑_{1 ≤ n ≤ N} a n · n ^ (-s)`. -/
def dirichletPoly (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)

/-! ## The oscillatory integral -/

/-- `∫₀ᵀ exp (i t θ) dt` has norm at most `2 / |θ|` when `θ ≠ 0`. -/
theorem norm_integral_exp_mul_I_le {T θ : ℝ} (hθ : θ ≠ 0) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ ≤ 2 / |θ| := by
  have hc : ((θ : ℂ) * I) ≠ 0 := by simp [hθ, Complex.ext_iff]
  have h := integral_exp_mul_complex (a := 0) (b := T) (c := (θ : ℂ) * I) hc
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  have hrw : (∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I))
      = (Complex.exp ((θ : ℂ) * I * T) - 1) / ((θ : ℂ) * I) := by
    rw [← h]; congr 1; ext t; ring_nf
  rw [hrw, norm_div, show ‖((θ : ℂ) * I)‖ = |θ| by simp]
  have h1 : ‖Complex.exp ((θ : ℂ) * I * T)‖ = 1 := by rw [Complex.norm_exp]; simp
  gcongr
  calc ‖Complex.exp ((θ : ℂ) * I * T) - 1‖ ≤ ‖Complex.exp ((θ : ℂ) * I * T)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ 2 := by rw [h1]; norm_num

/-! ## The expansion of the square -/

/-- On the vertical line `σ + i t`, the power `n ^ (-s)` splits into its modulus and its
oscillating factor. -/
theorem natCast_cpow_neg_line {m : ℕ} (hm : 1 ≤ m) (σ t : ℝ) :
    (m : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
      = (((m : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log m) : ℝ) : ℂ) * I) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne'), ← Complex.natCast_log,
    Real.rpow_def_of_pos hm0, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The summand of the expanded square: the contribution of the pair `(m, n)`. -/
def meanSquareTerm (a : ℕ → ℂ) (σ : ℝ) (m n : ℕ) (t : ℝ) : ℂ :=
  a m * (starRingEnd ℂ) (a n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) *
    Complex.exp (((t : ℂ)) * ((Real.log n - Real.log m : ℝ) : ℂ) * I)

/-- Expanding the square of a Dirichlet polynomial on a vertical line. -/
theorem normSq_dirichletPoly_eq (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (meanSquareTerm a σ m n t).re := by
  classical
  set c : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) with hc
  have h1 : ‖∑ n ∈ Finset.Icc 1 N, c n‖ ^ 2 = ((∑ n ∈ Finset.Icc 1 N, c n) *
      (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 N, c n)).re := by
    rw [Complex.mul_conj]; simp [Complex.sq_norm]
  rw [dirichletPoly, ← hc, h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [hc]
  simp only [meanSquareTerm]
  rw [natCast_cpow_neg_line hm1, natCast_cpow_neg_line hn1]
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
  rw [show (t : ℂ) * ((Real.log n - Real.log m : ℝ) : ℂ) * I
      = ((-(t * Real.log m) : ℝ) : ℂ) * I + (((-(t * Real.log n) : ℝ) : ℂ) * -I) by
        push_cast; ring, Complex.exp_add]
  push_cast
  ring

/-! ## The mean square bound -/

/-- The kernel bounding the contribution of the pair `(m, n)` to the mean square. -/
def meanSquareKernel (a : ℕ → ℂ) (σ T : ℝ) (m n : ℕ) : ℝ :=
  ‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) *
    (if m = n then T else 2 / |Real.log ((n : ℝ) / (m : ℝ))|)

/-- The contribution of a single pair `(m, n)` to the mean square is at most its kernel. -/
theorem integral_meanSquareTerm_re_le (a : ℕ → ℂ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re) ≤ meanSquareKernel a σ T m n := by
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
  have hle : (∫ t in (0 : ℝ)..T, (meanSquareTerm a σ m n t).re)
      ≤ ‖K‖ * ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := by
    rw [h1, h2]
    calc (K * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)).re
        ≤ ‖K * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := Complex.re_le_norm _
      _ = ‖K‖ * ‖∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)‖ := norm_mul _ _
  rw [meanSquareKernel, ← hKnorm]
  refine hle.trans ?_
  by_cases hmn : m = n
  · subst hmn
    simp only [hθdef, sub_self]
    rw [show (∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * ((0 : ℝ) : ℂ) * I)) = (T : ℂ) by simp]
    simp [abs_of_nonneg hT]
  · rw [if_neg hmn]
    have hθ0 : θ ≠ 0 := by
      rw [hθdef, sub_ne_zero]
      intro h
      have hnm : (n : ℝ) = (m : ℝ) := by rw [← Real.exp_log hn0, ← Real.exp_log hm0, h]
      exact hmn (by exact_mod_cast hnm.symm)
    have hlog : |Real.log ((n : ℝ) / (m : ℝ))| = |θ| := by
      rw [Real.log_div hn0.ne' hm0.ne', hθdef]
    rw [hlog]
    have hbd := norm_integral_exp_mul_I_le (T := T) hθ0
    nlinarith [norm_nonneg (∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * θ * I)),
      norm_nonneg K, hKnorm]

/-- **The mean value theorem for Dirichlet polynomials**, raw form: the mean square of a
Dirichlet polynomial over `[0, T]` is bounded by the sum of the pair kernels. -/
theorem integral_normSq_dirichletPoly_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, meanSquareKernel a σ T m n := by
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
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      exact fun n _ => (hcont m n).intervalIntegrable 0 T
    · intro m _
      exact (continuous_finsetSum _ fun n _ => hcont m n).intervalIntegrable 0 T
  rw [hstep]
  refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
  exact integral_meanSquareTerm_re_le a σ hT (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1

/-- The off-diagonal remainder in the mean value theorem. -/
def offDiagSum (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    (if m = n then 0 else
      2 * (‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))) / |Real.log ((n : ℝ) / (m : ℝ))|)

/-- **The mean value theorem for Dirichlet polynomials.**  The mean square of
`∑_{n ≤ N} a n n^(-s)` over the segment `[0, T]` of a vertical line is at most the diagonal
term `T ∑ ‖a n‖² n^(-2σ)` plus the off-diagonal remainder. -/
theorem integral_normSq_dirichletPoly_le_diag_add_offDiag (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) + offDiagSum a N σ := by
  classical
  refine (integral_normSq_dirichletPoly_le a N σ hT).trans ?_
  rw [offDiagSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hsplit : ∀ n ∈ Finset.Icc 1 N, meanSquareKernel a σ T m n
      = (if m = n then T * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)) else 0)
        + (if m = n then 0 else
            2 * (‖a m‖ * ‖a n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)))
              / |Real.log ((n : ℝ) / (m : ℝ))|) := by
    intro n _
    rw [meanSquareKernel]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, if_pos rfl, if_pos rfl, add_zero,
        show (-2 * σ) = (-σ) + (-σ) by ring, Real.rpow_add hm0]
      ring
    · rw [if_neg hmn, if_neg hmn, if_neg hmn, zero_add]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq (Finset.Icc 1 N) m
    (fun _ => T * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ))), if_pos hm]

/-! ## Elementary estimates for the off-diagonal sum -/

/-- The harmonic sum bound `∑_{k ≤ N} 1/k ≤ 1 + log N`. -/
theorem sum_inv_Icc_le (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have hq : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rwa [hq] at h

/-- A lower bound for `|log (y/x)|`: it is at least `|y - x| / max x y`, hence its reciprocal
is at most `(x + y)/|y - x|`. -/
theorem inv_abs_log_div_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    1 / |Real.log (y / x)| ≤ (x + y) / |y - x| := by
  wlog hlt : x < y generalizing x y
  · have h := this hy hx hxy.symm (lt_of_le_of_ne (not_lt.mp hlt) hxy.symm)
    rwa [show Real.log (x / y) = -Real.log (y / x) by rw [← Real.log_inv]; congr 1; field_simp,
      abs_neg, abs_sub_comm, add_comm] at h
  have hd : 0 < y - x := by linarith
  have hlog : (y - x) / y ≤ Real.log (y / x) := by
    have h0 := Real.one_sub_inv_le_log_of_pos (x := y / x) (by positivity)
    have hinv : (y / x)⁻¹ = x / y := by field_simp
    have heq : (y - x) / y = 1 - x / y := by field_simp
    rw [heq, ← hinv]
    exact h0
  have hlogpos : 0 < Real.log (y / x) := lt_of_lt_of_le (by positivity) hlog
  rw [abs_of_pos hlogpos, abs_of_pos hd, div_le_div_iff₀ hlogpos hd]
  have h1 : (y - x) ≤ y * Real.log (y / x) := by
    have := (div_le_iff₀ hy).mp hlog
    linarith
  nlinarith [hlogpos, hx]

/-- Comparing two powers: `x^(-s) ≤ y^(-s) (1 + |y - x|/x)` for `0 ≤ s ≤ 1`. -/
theorem rpow_neg_le_mul_one_add {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    x ^ (-s) ≤ y ^ (-s) * (1 + |y - x| / x) := by
  have key : x ^ (-s) = y ^ (-s) * (y / x) ^ s := by
    rw [Real.div_rpow hy.le hx.le, Real.rpow_neg hy.le, Real.rpow_neg hx.le]
    field_simp
  rw [key]
  have hyx : (0 : ℝ) < y / x := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy.le _)
  have habs : (y - x) / x ≤ |y - x| / x := by gcongr; exact le_abs_self _
  rcases le_or_gt y x with h | h
  · have h2 : (y / x) ^ s ≤ 1 := Real.rpow_le_one hyx.le (by rw [div_le_one hx]; exact h) h0
    have : 0 ≤ |y - x| / x := by positivity
    linarith
  · have hge : (1 : ℝ) ≤ y / x := by rw [le_div_iff₀ hx]; linarith
    have h2 : (y / x) ^ s ≤ (y / x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hge h1
    rw [Real.rpow_one] at h2
    have h4 : y / x = 1 + (y - x) / x := by field_simp; ring
    linarith

/-- The sum of `1/|n - m|` over `m ≤ N`, `m ≠ n`, is at most `2 (1 + log N)`. -/
theorem sum_inv_abs_sub_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ≠ n), 1 / |(n : ℝ) - (m : ℝ)|
      ≤ 2 * (1 + Real.log N) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 N).filter (fun m => m ≠ n))
    (fun m => m < n)]
  have hs1 : ((Finset.Icc 1 N).filter (fun m => m ≠ n)).filter (fun m => m < n)
      = Finset.Icc 1 (n - 1) := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hs2 : ((Finset.Icc 1 N).filter (fun m => m ≠ n)).filter (fun m => ¬ m < n)
      = Finset.Icc (n + 1) N := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hs1, hs2]
  have e1 : ∑ m ∈ Finset.Icc 1 (n - 1), 1 / |(n : ℝ) - (m : ℝ)|
      = ∑ k ∈ Finset.Icc 1 (n - 1), 1 / (k : ℝ) := by
    refine Finset.sum_nbij' (i := fun m => n - m) (j := fun k => n - k) ?_ ?_ ?_ ?_ ?_ <;>
      intro m hm <;> simp only [Finset.mem_Icc] at * <;> try omega
    have hmn : m ≤ n := by omega
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by push_cast [hmn]; ring
    rw [hcast, abs_of_nonneg (by simp; omega : (0 : ℝ) ≤ (n : ℝ) - m)]
  have e2 : ∑ m ∈ Finset.Icc (n + 1) N, 1 / |(n : ℝ) - (m : ℝ)|
      = ∑ k ∈ Finset.Icc 1 (N - n), 1 / (k : ℝ) := by
    refine Finset.sum_nbij' (i := fun m => m - n) (j := fun k => k + n) ?_ ?_ ?_ ?_ ?_ <;>
      intro m hm <;> simp only [Finset.mem_Icc] at * <;> try omega
    have hmn : n ≤ m := by omega
    have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by push_cast [hmn]; ring
    rw [hcast, abs_sub_comm, abs_of_nonneg (by simp; omega : (0 : ℝ) ≤ (m : ℝ) - n)]
  rw [e1, e2]
  have b1 : ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log N := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity))
      (sum_inv_Icc_le N)
    intro k hk; simp only [Finset.mem_Icc] at *; omega
  have b2 : ∑ k ∈ Finset.Icc 1 (N - n), (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log N := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity))
      (sum_inv_Icc_le N)
    intro k hk; simp only [Finset.mem_Icc] at *; omega
  linarith

end RiemannHypothesis
