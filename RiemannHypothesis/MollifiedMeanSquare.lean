/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.DivisorSquareSum
import RiemannHypothesis.DirichletPolyMeanValue

/-!
# The mean square of the mollified partial sum

`RiemannHypothesis/Mollifier.lean` proves the *finite* mollifier identity: for `1 ≤ y ≤ K` and
every `s`,

`M_y(s) · ∑_{k ≤ K} k^{-s} = 1 + ∑_{y < m ≤ yK} c_{y,K}(m) m^{-s}`,

`RiemannHypothesis/DirichletPolyMeanValue.lean` proves the mean value theorem for Dirichlet
polynomials with arbitrary coefficients, and `RiemannHypothesis/DivisorSquareSum.lean` proves
that the mean-square weight `∑_{m > y} d(m)² m^{-2σ}` of the tail coefficients is small for
large `y`, for every fixed `σ > 1/2`.  Putting the three together gives the mean square of the
mollified partial sum on a line in the strip:

`∫₀ᵀ ‖M_y(σ + i t) ∑_{k ≤ K} k^{-σ-i t} - 1‖² dt ≤ (T + 8 yK (1 + log (yK))) · ε`,

for a suitable length `y = y(σ, ε)` and *every* `K ≥ y` and `T ≥ 0`.  This is the analytic core
of the Carlson–Ingham density argument, in the form in which it applies to Dirichlet
polynomials.

## Main results

* `norm_finiteDetectCoeff_le_divisorCount` : `|c_{y,K}(m)| ≤ d(m)`.
* `mollifiedTail_eq` : `M_y · P_K - 1` is the Dirichlet polynomial with coefficients
  `mollifiedTailCoeff y K`, supported on `m > y`.
* `integral_normSq_mollified_partialSum_sub_one_le` : the mean value theorem applied to it.
* `exists_integral_normSq_mollified_partialSum_sub_one_le` : the mean square is at most
  `(T + 8 yK (1 + log (yK))) ε` for a mollifier length `y` depending only on `σ` and `ε`.
* `exists_volume_norm_mollified_partialSum_sub_one_ge_le` : the Chebyshev consequence, a large
  values estimate for `M_y P_K - 1`.

Nothing here is conditional, and nothing here uses the Riemann hypothesis.

## Scope

The statement is about the Dirichlet polynomial `M_y · P_K`, not about `ζ M_y`: replacing the
partial sum `P_K` by `ζ` needs the Euler–Maclaurin (or approximate functional equation)
approximation of `ζ` in the strip together with control of the resulting error against the
mollifier, which is not done here.  In particular **no** zero-density estimate is claimed in
this file.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Finset

namespace RiemannHypothesis

open scoped ArithmeticFunction.Moebius

/-! ## The tail coefficients of the mollified partial sum -/

/-- The coefficients of `M_y · P_K - 1`: the coefficients `c_{y,K}(m)` of the mollified partial
sum, cut down to `m > y` (where they already vanish for `2 ≤ m ≤ y`). -/
def mollifiedTailCoeff (y K m : ℕ) : ℂ :=
  if y < m then Mollifier.finiteDetectCoeff y K m else 0

/-- The coefficients of the mollified partial sum are bounded by the divisor function. -/
theorem norm_finiteDetectCoeff_le_divisorCount (y K m : ℕ) :
    ‖Mollifier.finiteDetectCoeff y K m‖ ≤ divisorCount m := by
  classical
  rw [Mollifier.finiteDetectCoeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K), ‖((μ d : ℤ) : ℂ)‖
      ≤ ∑ _d ∈ m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        have h : |(μ d : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        calc ‖((μ d : ℤ) : ℂ)‖ = |(μ d : ℤ)| := by
              rw [show (((μ d : ℤ)) : ℂ) = ((((μ d : ℤ) : ℝ)) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
          _ ≤ 1 := by exact_mod_cast h
    _ = (m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K)).card := by simp
    _ ≤ divisorCount m := by
        have h : (m.divisors.filter (fun d => d ≤ y ∧ m / d ≤ K)).card ≤ divisorCount m :=
          Finset.card_filter_le _ _
        exact_mod_cast h

/-- The tail coefficients are bounded by the divisor function. -/
theorem norm_mollifiedTailCoeff_le_divisorCount (y K m : ℕ) :
    ‖mollifiedTailCoeff y K m‖ ≤ divisorCount m := by
  rw [mollifiedTailCoeff]
  split
  · exact norm_finiteDetectCoeff_le_divisorCount y K m
  · simp

/-- The tail coefficients vanish on the initial segment `m ≤ y`. -/
theorem mollifiedTailCoeff_eq_zero_of_le {y K m : ℕ} (hm : m ≤ y) :
    mollifiedTailCoeff y K m = 0 := by
  rw [mollifiedTailCoeff, if_neg (by omega)]

/-- **`M_y · P_K - 1` is a Dirichlet polynomial supported on `m > y`.** -/
theorem mollifiedTail_eq {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    Mollifier.mollifier y s * (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s)) - 1
      = dirichletPoly (mollifiedTailCoeff y K) (y * K) s := by
  classical
  have hyyK : y ≤ y * K := Nat.le_mul_of_pos_right y (by omega)
  have hid := Mollifier.mollified_partialSum_eq_one_add_tail hy hyK s
  have hsplit : dirichletPoly (mollifiedTailCoeff y K) (y * K) s
      = ∑ m ∈ Finset.Ioc y (y * K), Mollifier.finiteDetectCoeff y K m * (m : ℂ) ^ (-s) := by
    rw [dirichletPoly]
    have hIcc : Finset.Icc 1 (y * K) = Finset.Ioc 0 (y * K) := by
      ext m; simp [Finset.mem_Icc]; omega
    rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) hyyK]
    have hlow : ∑ m ∈ Finset.Ioc 0 y, mollifiedTailCoeff y K m * (m : ℂ) ^ (-s) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [mollifiedTailCoeff_eq_zero_of_le (Finset.mem_Ioc.mp hm).2, zero_mul]
    rw [hlow, zero_add]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mollifiedTailCoeff, if_pos (Finset.mem_Ioc.mp hm).1]
  rw [hsplit, Mollifier.mollifier, hid]
  ring

/-! ## The mean square -/

/-- The mean-square weight of the tail coefficients, bounded by that of the divisor
function. -/
theorem sum_normSq_mollifiedTailCoeff_le {σ : ℝ} (y K M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ‖mollifiedTailCoeff y K m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) := by
  classical
  have hIcc : Finset.Icc 1 M = Finset.Ioc 0 M := by ext m; simp [Finset.mem_Icc]; omega
  rcases le_total y M with hyM | hMy
  · rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) hyM]
    have hlow : ∑ m ∈ Finset.Ioc 0 y, ‖mollifiedTailCoeff y K m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [mollifiedTailCoeff_eq_zero_of_le (Finset.mem_Ioc.mp hm).2]
      simp
    rw [hlow, zero_add]
    refine Finset.sum_le_sum fun m _ => ?_
    have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedTailCoeff_le_divisorCount y K m) 2) hpow
  · have hzero : ∀ m ∈ Finset.Icc 1 M,
        ‖mollifiedTailCoeff y K m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) = 0 := by
      intro m hm
      rw [mollifiedTailCoeff_eq_zero_of_le
        (le_trans (Finset.mem_Icc.mp hm).2 hMy)]
      simp
    rw [Finset.sum_congr rfl hzero]
    simp only [Finset.sum_const_zero]
    refine Finset.sum_nonneg fun m _ => ?_
    have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
    positivity

/-- The mean value theorem applied to `M_y · P_K - 1`. -/
theorem integral_normSq_mollified_partialSum_sub_one_le {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K)
    (σ T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
      ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)))
          * ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) := by
  classical
  set W := ∑ m ∈ Finset.Icc 1 (y * K), ‖mollifiedTailCoeff y K m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)
    with hW
  have hmvt := abs_integral_normSq_dirichletPoly_sub_diag_le_mvt
    (mollifiedTailCoeff y K) (y * K) σ T
  have hcongr : (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
      = ∫ t in (0 : ℝ)..T,
          ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mollifiedTail_eq hy hyK]
  have hWnn : 0 ≤ W := by
    refine Finset.sum_nonneg fun m _ => ?_
    have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hlog : 0 ≤ Real.log (y * K) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ y * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have hbound : (∫ t in (0 : ℝ)..T,
      ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ T * W + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)) * W := by
    have h := (abs_le.mp hmvt).2
    have hcast : ((y * K : ℕ) : ℝ) = (y : ℝ) * (K : ℝ) := by push_cast; ring
    rw [hcast] at h ⊢
    linarith
  rw [hcongr]
  refine hbound.trans ?_
  have hWle : W ≤ ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) :=
    sum_normSq_mollifiedTailCoeff_le y K (y * K)
  have hfac : 0 ≤ T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)) := by positivity
  calc T * W + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)) * W
      = (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * W := by ring
    _ ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)))
          * ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_left hWle hfac

/-! ## Choosing the mollifier length -/

/-- A finite tail of `∑ d(m)² m^{-2σ}` beyond `y` is bounded by the corresponding infinite
tail. -/
theorem sum_Ioc_divisorCount_sq_le_tsum {σ : ℝ} (hσ : 1 / 2 < σ) (y M : ℕ) :
    ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ ∑' n : ℕ, (divisorCount (n + y + 1) : ℝ) ^ 2 * (((n + y : ℕ) : ℝ) + 1) ^ (-(2 * σ)) := by
  have ha : 1 < 2 * σ := by linarith
  set g : ℕ → ℝ := fun n => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) with hg
  have hgsum : Summable g := summable_divisorCount_sq_rpow ha
  have hshift : Summable (fun n => g (n + y)) := (summable_nat_add_iff y).mpr hgsum
  have hnn : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
    rw [hg]
    positivity
  have hrw : ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      = ∑ n ∈ Finset.range (M - y), g (n + y) := by
    refine Finset.sum_nbij' (i := fun m => m - y - 1) (j := fun n => n + y + 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Ioc] at hm
      simp only [Finset.mem_range]
      omega
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Ioc]
      omega
    · intro m hm
      simp only [Finset.mem_Ioc] at hm
      omega
    · intro n _
      omega
    · intro m hm
      simp only [Finset.mem_Ioc] at hm
      have e1 : m - y - 1 + y + 1 = m := by omega
      have e2 : ((m - y - 1 + y : ℕ) : ℝ) + 1 = (m : ℝ) := by
        have h : ((m - y - 1 + y + 1 : ℕ) : ℝ) = (m : ℝ) := by
          exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) e1
        push_cast at h ⊢
        linarith
      rw [hg]
      simp only
      rw [e1, e2, neg_mul]
  calc ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      = ∑ n ∈ Finset.range (M - y), g (n + y) := hrw
    _ ≤ ∑' n : ℕ, g (n + y) := Summable.sum_le_tsum _ (fun i _ => hnn _) hshift
    _ = ∑' n : ℕ, (divisorCount (n + y + 1) : ℝ) ^ 2
          * (((n + y : ℕ) : ℝ) + 1) ^ (-(2 * σ)) := by
        refine tsum_congr fun n => ?_
        rw [hg]

/-- **The mean square of the mollified partial sum.**  For every `σ > 1/2` and `ε > 0` there is
a mollifier length `y ≥ 1` such that for every `K ≥ y` and every `T ≥ 0`,
`∫₀ᵀ ‖M_y P_K - 1‖² ≤ (T + 8 yK (1 + log (yK))) ε`. -/
theorem exists_integral_normSq_mollified_partialSum_sub_one_le {σ ε : ℝ} (hσ : 1 / 2 < σ)
    (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε := by
  obtain ⟨y, hy1, hylt⟩ := exists_tsum_divisorCount_sq_tail_lt hσ hε
  refine ⟨y, hy1, fun K hK T hT => ?_⟩
  have hK1 : 1 ≤ K := le_trans hy1 hK
  have hlog : 0 ≤ Real.log (y * K) := by
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    nlinarith
  have hfac : 0 ≤ T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K)) := by positivity
  refine (integral_normSq_mollified_partialSum_sub_one_le hy1 hK σ T hT).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hfac
  exact le_trans (sum_Ioc_divisorCount_sq_le_tsum hσ y (y * K)) hylt.le

/-! ## A large values estimate -/

/-- The map `t ↦ ‖∑_{n ≤ N} a n · n^{-σ-i t}‖²` is continuous. -/
theorem continuous_normSq_dirichletPoly_line' (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  refine (Continuous.norm ?_).pow 2
  unfold dirichletPoly
  refine continuous_finsetSum _ fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  have hc : Continuous (fun t : ℝ => ((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
    refine Continuous.cpow continuous_const (by fun_prop) ?_
    intro t
    left
    simpa using hn0
  exact continuous_const.mul hc

/-- **A large values estimate for the mollified partial sum.**  For every `σ > 1/2` and `ε > 0`
there is a mollifier length `y ≥ 1` such that, for every `K ≥ y`, the set of `t ∈ (0, T]` at
which `‖M_y P_K - 1‖ ≥ V` has measure at most `(T + 8 yK (1 + log (yK))) ε / V²`.  This is
Chebyshev's inequality applied to the mean square. -/
theorem exists_volume_norm_mollified_partialSum_sub_one_ge_le {σ ε : ℝ} (hσ : 1 / 2 < σ)
    (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖}).toReal
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε / V ^ 2 := by
  obtain ⟨y, hy1, hmean⟩ := exists_integral_normSq_mollified_partialSum_sub_one_le hσ hε
  refine ⟨y, hy1, fun K hK T hT V hV => ?_⟩
  have hFeq : ∀ t : ℝ, Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1
        = dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I) :=
    fun t => mollifiedTail_eq hy1 hK _
  have hsetEq : {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖}
      = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖} := by
    ext t
    simp only [Set.mem_ofPred_eq, hFeq t]
  rw [hsetEq]
  have hcont : Continuous
      (fun t : ℝ => ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    continuous_normSq_dirichletPoly_line' (mollifiedTailCoeff y K) (y * K) σ
  have hint : IntegrableOn
      (fun t : ℝ => ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Set.Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (hcont.intervalIntegrable 0 T)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      fun t : ℝ =>
        ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (V ^ 2)
  have hset : {t : ℝ |
        V ^ 2 ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2}
        ∩ Set.Ioc (0 : ℝ) T
      = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hle, ht⟩
      refine ⟨ht, ?_⟩
      nlinarith [norm_nonneg (dirichletPoly (mollifiedTailCoeff y K) (y * K)
        ((σ : ℂ) + (t : ℂ) * I))]
    · rintro ⟨ht, hle⟩
      exact ⟨by nlinarith, ht⟩
  have hmeas : MeasurableSet {t : ℝ |
      V ^ 2 ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2} :=
    measurableSet_le measurable_const hcont.measurable
  have hrestrict : (volume.restrict (Set.Ioc (0 : ℝ) T)).real {t : ℝ |
        V ^ 2 ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2}
      = (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply hmeas, hset]
  have hintegral : (∫ t in Set.Ioc (0 : ℝ) T,
        ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε := by
    have h := hmean K hK T hT
    rw [intervalIntegral.integral_of_le hT] at h
    refine le_trans (le_of_eq ?_) h
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [hFeq t]
  rw [hrestrict] at hmarkov
  rw [le_div_iff₀ (by positivity)]
  calc (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖}).toReal
        * V ^ 2
      = V ^ 2 * (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖dirichletPoly (mollifiedTailCoeff y K) (y * K)
          ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by ring
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T,
        ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := hmarkov
    _ ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε := hintegral

end RiemannHypothesis
