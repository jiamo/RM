/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZetaPartialSum
import RiemannHypothesis.MontgomeryVaughanWeightedMeanValue

/-!
# The Hardy–Littlewood mean square of `ζ` on the critical line

  `|∫₀ᵀ |ζ(1/2 + it)|² dt − T log T| ≤ C T` for every `T ≥ 1`
  (`exists_abs_integral_normSq_riemannZeta_sub_le`, existential `C`), and
  `(∫₀ᵀ |ζ(1/2 + it)|² dt) / (T log T) → 1` (`tendsto_integral_normSq_riemannZeta_div`).

The route is the one of Montgomery and Vaughan (*Hilbert's inequality*, J. London Math. Soc. (2)
8 (1974), 73–82): approximate `ζ(1/2 + it)` by a Dirichlet polynomial of length `x ≍ t` and
apply the weighted mean value theorem.  The approximate functional equation is not used.

## The argument

* **The polynomial on a dyadic block.**  For `T ≥ 1` let `N = ⌊2T⌋` and
  `P(t) = ∑_{n ≤ N} n^(-1/2-it)` (`criticalPoly`).  The weighted mean value theorem
  (`MontgomeryVaughanWeighted.abs_integral_normSq_dirichletPoly_sub_le_weighted`, constant
  `10 √2`) gives `∫₀^{T'} |P|² = T' ∑_{n ≤ N} 1/n + O(N)` for every `T'`
  (`abs_integral_criticalPoly_sub_le`, error at most `20 √2 N`); subtracting `T' = T` from
  `T' = 2T` and `log T ≤ ∑_{n ≤ N} 1/n ≤ 1 + log 2 + log T` gives
  `|∫_T^{2T} |P|² − T log T| ≤ 122 T` (`abs_integral_block_criticalPoly_sub_le`).
* **The approximation.**  Theorem 4.11 (`RiemannHypothesis/ZetaPartialSum.lean`) with `x = 2T`,
  the same polynomial for every `t ∈ [T, 2T]`, gives `|ζ(1/2 + it) − P(t)| ≤ 13/√T`
  (`norm_zeta_sub_criticalPoly_le`): `11 (2T)^(-1/2)` from the theorem and `√(2T)/T` from the
  term `x^(1/2-it)/(1/2 − it)`.
* **The cross terms.**  With `E = ζ − P`, pointwise
  `| |ζ|² − |P|² | ≤ 2|P||E| + |E|² ≤ |P|²/√T + (√T + 1)|E|²` (the inequality
  `2ab ≤ a²/r + r b²`, the pointwise form of Cauchy–Schwarz).  Integrated over `[T, 2T]` this is
  `O(T)`, so `|∫_T^{2T} |ζ(1/2 + it)|² dt − T log T| ≤ 584 T`
  (`abs_integral_block_zeta_sub_le`).
* **Dyadic summation.**  `F(T) = ∫₀ᵀ |ζ|² − T log T` satisfies
  `|F(2T) − F(T)| ≤ (584 + 2 log 2) T ≤ 586 T`, and `|F| ≤ ∫₀² |ζ|² + 2` on `[1, 2]`; induction
  over `[1, 2^(k+1)]` gives `|F(T)| ≤ (∫₀² |ζ|² + 2) + 586 T`.

## Scope

Only the first term is proved.  Ingham's second term, `∫₀ᵀ |ζ(1/2 + it)|² dt =
T log T + (2γ − 1 − log 2π) T + O(T^(1/2) log T)`, is **not** proved here, and the constant `C`
is existential (it contains `∫₀² |ζ(1/2 + it)|² dt`).  No hypothesis is assumed.
-/

noncomputable section

open Complex Real Finset Filter MeasureTheory intervalIntegral

namespace RiemannHypothesis

namespace HardyLittlewood

/-- The coefficients `n^(-1/2)`. -/
def halfCoeff (n : ℕ) : ℂ := (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ))

/-- The partial sum `∑_{n ≤ N} n^(-1/2-it)`. -/
def criticalPoly (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))

/-- The harmonic sum `∑_{n ≤ N} 1/n`. -/
def harm (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹

theorem criticalPoly_eq (N : ℕ) (t : ℝ) :
    criticalPoly N t = dirichletPoly halfCoeff N ((t : ℂ) * I) := by
  unfold criticalPoly dirichletPoly halfCoeff
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  rw [← Complex.cpow_add _ _ hn0]
  congr 1
  ring

theorem norm_halfCoeff_sq {n : ℕ} (hn : 1 ≤ n) : ‖halfCoeff n‖ ^ 2 = ((n : ℝ))⁻¹ := by
  rw [halfCoeff, Complex.norm_natCast_cpow_of_pos (by omega)]
  have hre : (-((1 / 2 : ℝ) : ℂ)).re = -(1 / 2 : ℝ) := by simp
  rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num
  exact Real.rpow_neg_one _

theorem continuous_criticalPoly (N : ℕ) : Continuous (criticalPoly N) := by
  unfold criticalPoly
  refine continuous_finsetSum _ fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact (by fun_prop : Continuous fun t : ℝ => -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).const_cpow
    (Or.inl hn0)

theorem continuous_riemannZeta_criticalLine :
    Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
    (x := t) (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)

/-- The mean value theorem for `criticalPoly`:
`|∫₀^{T'} |∑_{n ≤ N} n^(-1/2-it)|² dt − T' ∑_{n ≤ N} 1/n| ≤ 20 √2 N`. -/
theorem abs_integral_criticalPoly_sub_le (N : ℕ) (T' : ℝ) :
    |(∫ t in (0 : ℝ)..T', ‖criticalPoly N t‖ ^ 2) - T' * harm N|
      ≤ 20 * Real.sqrt 2 * N := by
  have h := MontgomeryVaughanWeighted.abs_integral_normSq_dirichletPoly_sub_le_weighted
    halfCoeff N T'
  have h1 : ∑ n ∈ Icc 1 N, ‖halfCoeff n‖ ^ 2 = harm N :=
    sum_congr rfl fun n hn => norm_halfCoeff_sq (mem_Icc.mp hn).1
  have h2 : ∑ n ∈ Icc 1 N, ((n : ℝ) + 1) * ‖halfCoeff n‖ ^ 2 ≤ (2 : ℝ) * N := by
    calc ∑ n ∈ Icc 1 N, ((n : ℝ) + 1) * ‖halfCoeff n‖ ^ 2 ≤ ∑ n ∈ Icc 1 N, (2 : ℝ) := by
          refine sum_le_sum fun n hn => ?_
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
          rw [norm_halfCoeff_sq (mem_Icc.mp hn).1]
          rw [add_mul, mul_inv_cancel₀ (by positivity)]
          have : ((n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
          linarith
      _ = (2 : ℝ) * N := by simp; ring
  simp_rw [← criticalPoly_eq] at h
  rw [h1] at h
  have hs : 0 ≤ 10 * Real.sqrt 2 := by positivity
  calc _ ≤ 10 * Real.sqrt 2 * ∑ n ∈ Icc 1 N, ((n : ℝ) + 1) * ‖halfCoeff n‖ ^ 2 := h
    _ ≤ 10 * Real.sqrt 2 * ((2 : ℝ) * N) := mul_le_mul_of_nonneg_left h2 hs
    _ = 20 * Real.sqrt 2 * N := by ring

/-- `log T ≤ ∑_{n ≤ ⌊2T⌋} 1/n ≤ 1 + log 2 + log T` for `T ≥ 1`. -/
theorem harm_floor_two_mul_bounds {T : ℝ} (hT : 1 ≤ T) :
    Real.log T ≤ harm ⌊2 * T⌋₊ ∧ harm ⌊2 * T⌋₊ ≤ 1 + Real.log 2 + Real.log T := by
  set N := ⌊2 * T⌋₊ with hN
  have hharm : harm N = (harmonic N : ℝ) := by
    rw [harm, harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hNle : (N : ℝ) ≤ 2 * T := Nat.floor_le (by linarith)
  have hNlt : 2 * T < N + 1 := Nat.lt_floor_add_one _
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  rw [hharm]
  constructor
  · refine le_trans ?_ (log_add_one_le_harmonic N)
    push_cast
    exact Real.log_le_log (by linarith) (by linarith)
  · refine (harmonic_le_one_add_log N).trans ?_
    have := Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith

/-- **The mean square of the polynomial on a dyadic block**:
`|∫_T^{2T} |∑_{n ≤ 2T} n^(-1/2-it)|² dt − T log T| ≤ 122 T` for `T ≥ 1`. -/
theorem abs_integral_block_criticalPoly_sub_le {T : ℝ} (hT : 1 ≤ T) :
    |(∫ t in T..2 * T, ‖criticalPoly ⌊2 * T⌋₊ t‖ ^ 2) - T * Real.log T| ≤ 122 * T := by
  set N := ⌊2 * T⌋₊ with hN
  have hNle : (N : ℝ) ≤ 2 * T := Nat.floor_le (by linarith)
  have hcont : Continuous fun t => ‖criticalPoly N t‖ ^ 2 :=
    (continuous_criticalPoly N).norm.pow 2
  have hsplit : (∫ t in (0 : ℝ)..2 * T, ‖criticalPoly N t‖ ^ 2)
      - ∫ t in (0 : ℝ)..T, ‖criticalPoly N t‖ ^ 2 = ∫ t in T..2 * T, ‖criticalPoly N t‖ ^ 2 :=
    intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [← hsplit]
  have h1 := abs_le.mp (abs_integral_criticalPoly_sub_le N (2 * T))
  have h2 := abs_le.mp (abs_integral_criticalPoly_sub_le N T)
  obtain ⟨hH1, hH2⟩ := harm_floor_two_mul_bounds hT
  rw [← hN] at hH1 hH2
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hsqrt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hNs : 20 * Real.sqrt 2 * N ≤ 60 * T := by
    have : 20 * Real.sqrt 2 * N ≤ 20 * (3 / 2) * (2 * T) := by
      gcongr
    linarith
  have hTH1 : T * Real.log T ≤ T * harm N := mul_le_mul_of_nonneg_left hH1 (by linarith)
  have hTH2 : T * harm N ≤ T * Real.log T + 2 * T := by
    have := mul_le_mul_of_nonneg_left hH2 (by linarith : (0 : ℝ) ≤ T)
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- **The approximation on a dyadic block**: for `T ≥ 1` and `T ≤ t ≤ 2T`,
`‖ζ(1/2 + it) − ∑_{n ≤ 2T} n^(-1/2-it)‖ ≤ 13/√T` (Theorem 4.11 with `x = 2T`). -/
theorem norm_zeta_sub_criticalPoly_le {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc T (2 * T)) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - criticalPoly ⌊2 * T⌋₊ t‖
      ≤ 13 / Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hx : (0 : ℝ) < 2 * T := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hxt : |t| ≤ 2 * T := by rw [abs_of_nonneg ht0]; exact ht.2
  have h := ZetaPartialSum.norm_riemannZeta_criticalLine_sub_partialSum_le hx hxt
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I with hw
  set Z := riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hP : ∑ n ∈ Icc 1 ⌊2 * T⌋₊, (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
      = criticalPoly ⌊2 * T⌋₊ t := rfl
  rw [hP] at h
  set r := Real.sqrt T with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hT0
  have hrr : r * r = T := Real.mul_self_sqrt hT0.le
  -- the main error term
  have hA : 11 * (2 * T) ^ (-(1 / 2 : ℝ)) ≤ 11 / r := by
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    gcongr
    exact Real.sqrt_le_sqrt (by linarith)
  -- the term `x^(1/2-it)/(1/2 − it)`
  have hB : ‖(((2 * T : ℝ)) : ℂ) ^ w / w‖ ≤ 2 / r := by
    have hwre : w.re = 1 / 2 := by simp [hw]
    have hwim : w.im = -t := by simp [hw]
    have hwn : T ≤ ‖w‖ := by
      have := Complex.abs_im_le_norm w
      rw [hwim, abs_neg, abs_of_nonneg ht0] at this
      linarith [ht.1]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hwre, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num), ← hr]
    have hs2 : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rw [div_le_div_iff₀ (by linarith) hr0]
    have h2 : Real.sqrt 2 * r * r ≤ 2 * T := by
      rw [mul_assoc, hrr]; nlinarith [Real.sqrt_nonneg 2]
    calc Real.sqrt 2 * r * r ≤ 2 * T := h2
      _ ≤ 2 * ‖w‖ := by linarith
  have hsplit : Z - criticalPoly ⌊2 * T⌋₊ t
      = (Z - criticalPoly ⌊2 * T⌋₊ t + (((2 * T : ℝ)) : ℂ) ^ w / w)
        - (((2 * T : ℝ)) : ℂ) ^ w / w := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have h13 : 11 / r + 2 / r = 13 / r := by ring
  linarith [h.trans hA]

/-- **The mean square of `ζ` on a dyadic block**:
`|∫_T^{2T} |ζ(1/2 + it)|² dt − T log T| ≤ 584 T` for `T ≥ 1`. -/
theorem abs_integral_block_zeta_sub_le {T : ℝ} (hT : 1 ≤ T) :
    |(∫ t in T..2 * T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * Real.log T| ≤ 584 * T := by
  have hT0 : 0 < T := by linarith
  set N := ⌊2 * T⌋₊ with hN
  set r := Real.sqrt T with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hT0
  have hrr : r * r = T := Real.mul_self_sqrt hT0.le
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hT
  have hrT : r ≤ T := by nlinarith
  set c : ℝ := (r + 1) * (169 / T) with hc
  set f1 : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf1
  set f2 : ℝ → ℝ := fun t => ‖criticalPoly N t‖ ^ 2 with hf2
  have hc1 : Continuous f1 := continuous_riemannZeta_criticalLine.norm.pow 2
  have hc2 : Continuous f2 := (continuous_criticalPoly N).norm.pow 2
  -- the pointwise comparison
  have hpt : ∀ t ∈ Set.Icc T (2 * T),
      f2 t - f2 t / r - c ≤ f1 t ∧ f1 t ≤ f2 t + f2 t / r + c := by
    intro t ht
    set z := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
    set p := ‖criticalPoly N t‖
    set e := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - criticalPoly N t‖
    have he : e ≤ 13 / r := norm_zeta_sub_criticalPoly_le hT ht
    have he0 : 0 ≤ e := norm_nonneg _
    have hp0 : 0 ≤ p := norm_nonneg _
    have hz0 : 0 ≤ z := norm_nonneg _
    have hzu : z ≤ p + e := by
      have := norm_add_le (criticalPoly N t)
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - criticalPoly N t)
      rw [add_sub_cancel] at this
      exact this
    have hzl : p ≤ z + e := by
      have := norm_sub_le (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - criticalPoly N t)
      rw [sub_sub_cancel] at this
      exact this
    have he2 : e ^ 2 ≤ 169 / T := by
      have : e ^ 2 ≤ (13 / r) ^ 2 := pow_le_pow_left₀ he0 he 2
      rw [div_pow, show r ^ 2 = T by rw [sq]; exact hrr] at this
      norm_num at this ⊢
      linarith
    have hcross : 2 * p * e ≤ p ^ 2 / r + r * e ^ 2 := by
      rw [div_add' _ _ _ hr0.ne', le_div_iff₀ hr0]
      nlinarith [sq_nonneg (p - r * e)]
    have hre2 : r * e ^ 2 + e ^ 2 ≤ c := by
      rw [hc]; nlinarith
    have hf1t : f1 t = z ^ 2 := rfl
    have hf2t : f2 t = p ^ 2 := rfl
    rw [hf1t, hf2t]
    constructor
    · have hlow : p ^ 2 - 2 * p * e ≤ z ^ 2 := by
        rcases le_total e p with hep | hep
        · have : p - e ≤ z := by linarith
          nlinarith
        · nlinarith
      nlinarith
    · nlinarith
  -- integrating
  have hTT : T ≤ 2 * T := by linarith
  have hint_g : ∀ α : ℝ, (∫ t in T..2 * T, (α * f2 t + c))
      = α * (∫ t in T..2 * T, f2 t) + c * T := by
    intro α
    rw [intervalIntegral.integral_add ((hc2.intervalIntegrable _ _).const_mul α)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hup : (∫ t in T..2 * T, f1 t) ≤ (1 + 1 / r) * (∫ t in T..2 * T, f2 t) + c * T := by
    rw [← hint_g]
    refine intervalIntegral.integral_mono_on hTT (hc1.intervalIntegrable _ _)
      (((hc2.intervalIntegrable _ _).const_mul _).add intervalIntegrable_const) fun t ht => ?_
    have := (hpt t ht).2
    have : (1 + 1 / r) * f2 t = f2 t + f2 t / r := by ring
    linarith
  have hlow : (1 - 1 / r) * (∫ t in T..2 * T, f2 t) + (-c) * T ≤ (∫ t in T..2 * T, f1 t) := by
    have hint_g' : (∫ t in T..2 * T, ((1 - 1 / r) * f2 t + -c))
        = (1 - 1 / r) * (∫ t in T..2 * T, f2 t) + (-c) * T := by
      rw [intervalIntegral.integral_add ((hc2.intervalIntegrable _ _).const_mul _)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hint_g']
    refine intervalIntegral.integral_mono_on hTT
      (((hc2.intervalIntegrable _ _).const_mul _).add intervalIntegrable_const)
      (hc1.intervalIntegrable _ _) fun t ht => ?_
    have := (hpt t ht).1
    have : (1 - 1 / r) * f2 t = f2 t - f2 t / r := by ring
    linarith
  -- the polynomial block and the size of the corrections
  have hP := abs_le.mp (abs_integral_block_criticalPoly_sub_le hT)
  rw [← hN] at hP
  set IP := ∫ t in T..2 * T, f2 t with hIP
  have hIP0 : 0 ≤ IP := intervalIntegral.integral_nonneg hTT fun t _ => by positivity
  have hlogT : Real.log T ≤ 2 * r := by
    have h := Real.log_le_sub_one_of_pos hr0
    have : Real.log T = 2 * Real.log r := by
      rw [← hrr, Real.log_mul hr0.ne' hr0.ne']; ring
    linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hIPr : IP / r ≤ 124 * T := by
    rw [div_le_iff₀ hr0]
    have h1 : IP ≤ T * Real.log T + 122 * T := by linarith [hP.2]
    have h2 : T * Real.log T ≤ T * (2 * r) := mul_le_mul_of_nonneg_left hlogT hT0.le
    have h3 : T * (2 * r) ≤ 2 * T * r := by ring_nf; exact le_rfl
    nlinarith
  have hcT : c * T ≤ 338 * T := by
    rw [hc]
    have : (r + 1) * (169 / T) * T = 169 * (r + 1) := by field_simp
    rw [this]
    nlinarith
  have hup' := hup
  have hlow' := hlow
  rw [show (1 + 1 / r) * IP = IP + IP / r by ring] at hup'
  rw [show (1 - 1 / r) * IP = IP - IP / r by ring] at hlow'
  rw [abs_le]
  constructor <;> nlinarith [hP.1, hP.2]

/-- **The Hardy–Littlewood mean square of `ζ` on the critical line**:
there is a constant `C` with
`|∫₀ᵀ |ζ(1/2 + it)|² dt − T log T| ≤ C T` for every `T ≥ 1`,
i.e. `∫₀ᵀ |ζ(1/2 + it)|² dt = T log T + O(T)`. -/
theorem exists_abs_integral_normSq_riemannZeta_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * Real.log T| ≤ C * T := by
  set f1 : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf1
  have hc1 : Continuous f1 := continuous_riemannZeta_criticalLine.norm.pow 2
  set F : ℝ → ℝ := fun T => (∫ t in (0 : ℝ)..T, f1 t) - T * Real.log T with hF
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- one dyadic step
  have hstep : ∀ T : ℝ, 1 ≤ T → |F (2 * T) - F T| ≤ 586 * T := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hsplit : (∫ t in (0 : ℝ)..2 * T, f1 t) - ∫ t in (0 : ℝ)..T, f1 t
        = ∫ t in T..2 * T, f1 t :=
      intervalIntegral.integral_interval_sub_left (hc1.intervalIntegrable _ _)
        (hc1.intervalIntegrable _ _)
    have hblock := abs_le.mp (abs_integral_block_zeta_sub_le hT)
    have hlog : Real.log (2 * T) = Real.log 2 + Real.log T :=
      Real.log_mul (by norm_num) hT0.ne'
    have heq : F (2 * T) - F T
        = (∫ t in T..2 * T, f1 t) - T * Real.log T - 2 * T * Real.log 2 := by
      simp only [hF]
      rw [← hsplit, hlog]
      ring
    rw [heq, abs_le]
    constructor <;> nlinarith [hblock.1, hblock.2]
  -- the initial segment
  set M0 : ℝ := (∫ t in (0 : ℝ)..2, f1 t) + 2 with hM0
  have hI2 : 0 ≤ ∫ t in (0 : ℝ)..2, f1 t :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity
  have hbase : ∀ S : ℝ, 1 ≤ S → S ≤ 2 → |F S| ≤ M0 := by
    intro S hS1 hS2
    have hI0 : 0 ≤ ∫ t in (0 : ℝ)..S, f1 t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
    have hIS : (∫ t in (0 : ℝ)..S, f1 t) ≤ ∫ t in (0 : ℝ)..2, f1 t :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) hS2
        (Filter.Eventually.of_forall fun t => by positivity) (hc1.intervalIntegrable _ _)
    have hl0 : 0 ≤ Real.log S := Real.log_nonneg hS1
    have hl2 : Real.log S ≤ Real.log 2 := Real.log_le_log (by linarith) hS2
    have hSl : S * Real.log S ≤ 2 := by nlinarith
    have hSl0 : 0 ≤ S * Real.log S := by positivity
    simp only [hF]
    rw [abs_le]
    constructor <;> linarith
  -- induction over dyadic ranges
  have hind : ∀ k : ℕ, ∀ S : ℝ, 1 ≤ S → S ≤ 2 ^ (k + 1) → |F S| ≤ M0 + 586 * S := by
    intro k
    induction k with
    | zero =>
      intro S hS1 hS2
      have := hbase S hS1 (by simpa using hS2)
      linarith
    | succ k ih =>
      intro S hS1 hS2
      rcases le_or_gt S (2 ^ (k + 1)) with h | h
      · exact ih S hS1 h
      · have h2k : (2 : ℝ) ≤ 2 ^ (k + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hS2' : 1 ≤ S / 2 := by linarith
        have hS2'' : S / 2 ≤ 2 ^ (k + 1) := by
          rw [pow_succ] at hS2; linarith
        have h1 := ih (S / 2) hS2' hS2''
        have h2 := hstep (S / 2) hS2'
        rw [show 2 * (S / 2) = S by ring] at h2
        have : |F S| ≤ |F (S / 2)| + |F S - F (S / 2)| := by
          have := abs_add_le (F (S / 2)) (F S - F (S / 2))
          simpa using this
        linarith
  have hM0pos : 0 < M0 := by linarith
  refine ⟨M0 + 586, by linarith, fun T hT => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
  have hk' : T ≤ 2 ^ (k + 1) := by
    rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have h := hind k T hT hk'
  have : M0 ≤ M0 * T := le_mul_of_one_le_right hM0pos.le hT
  simp only [hF] at h
  calc _ ≤ M0 + 586 * T := h
    _ ≤ (M0 + 586) * T := by nlinarith

/-- **The Hardy–Littlewood asymptotic**:
`(∫₀ᵀ |ζ(1/2 + it)|² dt) / (T log T) → 1` as `T → ∞`. -/
theorem tendsto_integral_normSq_riemannZeta_div :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T * Real.log T))
      atTop (nhds 1) := by
  obtain ⟨C, hC, hbd⟩ := exists_abs_integral_normSq_riemannZeta_sub_le
  set I : ℝ → ℝ := fun T => ∫ t in (0 : ℝ)..T,
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hI
  have hg : Tendsto (fun T : ℝ => (I T - T * Real.log T) / (T * Real.log T)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := C)).div_atTop Real.tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hT0 hlog), div_le_div_iff₀
      (mul_pos hT0 hlog) hlog]
    have := hbd T (by linarith)
    nlinarith
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add hg
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hne : T * Real.log T ≠ 0 := (mul_pos hT0 hlog).ne'
  field_simp
  ring

end HardyLittlewood

end RiemannHypothesis
