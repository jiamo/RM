/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroExponent
import RiemannHypothesis.ZeroInfinite
import RiemannHypothesis.BohrLandau

/-!
# The exponent of convergence of the nontrivial zeroes is exactly `1`

`RiemannHypothesis.ZeroExponent` proves the upper half of the statement: for every `e > 0` the
sum `∑_ρ ‖ρ‖^(-(1+e))` over the nontrivial zeroes of `ζ`, counted without multiplicity,
converges.  Here the complementary half is proved: **no exponent `e ≤ 1` works**, and in
particular `∑_ρ 1/‖ρ‖ = ∞`.

The two inputs are both available in the repository:

* the Riemann–von Mangoldt lower bound `N(0, T) ≫ T log T`, counted *with* multiplicity
  (`exists_mul_le_windowCount_zero`), and
* the theorem that at least five sixths of the zeroes are distinct
  (`five_sixths_distinct_cumulative`),

which together give the same lower bound for the number of *distinct* nontrivial zeroes of
ordinate in `(0, T]` (`exists_mul_le_windowCountDistinct_zero`).  Every such zero has
`‖ρ‖ ≤ 1 + T`, so the partial sum of `‖ρ‖^(-e)` over that window is at least
`c (T log T) (1 + T)^(-e) ≥ (c/2) log T` for `0 < e ≤ 1`, which tends to infinity.

## Main results

* `exists_mul_le_windowCountDistinct_zero` — `N_d(0, T) ≫ T log T`.
* `tendsto_sum_rpow_neg_windowZeros_atTop` — the partial sums `∑_{0 < γ ≤ T} ‖ρ‖^(-e)` tend to
  infinity, for every `0 < e ≤ 1`.
* `not_summable_rpow_neg`, `not_summable_inv_norm` — the divergence statements.
* `sInf_exponent_summable_eq_one` — the exponent of convergence of the nontrivial zeroes is
  exactly `1`.

Zeroes are counted *without* multiplicity throughout, as in `RiemannHypothesis.ZeroExponent`.
The *rate* of divergence, `∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²`, is determined in
`RiemannHypothesis.ZeroSumLogSq`.  Nothing here bears on the Riemann hypothesis itself.
-/

noncomputable section

open Complex Filter Set

open scoped Topology

namespace RiemannHypothesis

/-! ## The lower bound for the number of distinct zeroes -/

/-- **The Riemann–von Mangoldt lower bound for the distinct zeroes.**  The number of *distinct*
nontrivial zeroes of `ζ` of ordinate in `(0, T]` is `≫ T log T`: at least five sixths of the
zeroes counted with multiplicity are distinct points. -/
theorem exists_mul_le_windowCountDistinct_zero :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (windowCountDistinct 0 T : ℝ) := by
  obtain ⟨c, hc, T₀, hcount⟩ := exists_mul_le_windowCount_zero
  obtain ⟨T₁, hdist⟩ := five_sixths_distinct_cumulative (1 / 6) (by norm_num)
  refine ⟨2 / 3 * c, by positivity, max (max T₀ T₁) 1, fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have h1 : c * (T * Real.log T) ≤ (windowCount 0 T : ℝ) := hcount T hT₀
  have h2 : (5 / 6 - 1 / 6 : ℝ) * (windowCount 0 T : ℝ) ≤ (windowCountDistinct 0 T : ℝ) :=
    hdist T hT₁
  have h3 : (5 / 6 - 1 / 6 : ℝ) = 2 / 3 := by norm_num
  rw [h3] at h2
  nlinarith [hc.le]

/-! ## The partial sums over a window -/

/-- A nontrivial zero of ordinate in `(0, T]` has norm at most `1 + T`. -/
theorem norm_le_of_mem_windowZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ windowZeros 0 T) : ‖ρ‖ ≤ 1 + T := by
  obtain ⟨⟨_, hre0, hre1⟩, him0, him1⟩ := hρ
  have h := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_pos hre0, abs_of_pos him0] at h
  linarith

/-- A nontrivial zero has positive norm. -/
theorem norm_pos_of_mem_windowZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ windowZeros 0 T) : 0 < ‖ρ‖ := by
  obtain ⟨⟨_, hre0, _⟩, _, _⟩ := hρ
  refine norm_pos_iff.mpr fun h => ?_
  rw [h] at hre0
  simp at hre0

/-- The partial sum of `‖ρ‖^(-e)` over the nontrivial zeroes of ordinate in `(0, T]` is at least
the number of those zeroes times `(1 + T)^(-e)`. -/
theorem mul_rpow_le_sum_rpow_neg_windowZeros {e T : ℝ} (he : 0 ≤ e) :
    (windowCountDistinct 0 T : ℝ) * (1 + T) ^ (-e)
      ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e) := by
  have hcard : (windowCountDistinct 0 T : ℝ) = ((windowZeros_finite 0 T).toFinset.card : ℝ) := by
    rw [windowCountDistinct, Set.ncard_eq_toFinset_card _ (windowZeros_finite 0 T)]
  have hterm : ∀ ρ ∈ (windowZeros_finite 0 T).toFinset, (1 + T) ^ (-e) ≤ ‖ρ‖ ^ (-e) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_of_mem_windowZeros hρ)
      (norm_le_of_mem_windowZeros hρ) (by linarith)
  calc (windowCountDistinct 0 T : ℝ) * (1 + T) ^ (-e)
      = ∑ _ρ ∈ (windowZeros_finite 0 T).toFinset, (1 + T) ^ (-e) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e) := Finset.sum_le_sum hterm

/-! ## Divergence -/

/-- The partial sums `∑_{0 < γ ≤ T} ‖ρ‖^(-e)` over the nontrivial zeroes of `ζ` tend to infinity
with `T`, for every `0 < e ≤ 1`. -/
theorem tendsto_sum_rpow_neg_windowZeros_atTop {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Tendsto (fun T : ℝ => ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e)) atTop atTop := by
  obtain ⟨c, hc, T₀, hcount⟩ := exists_mul_le_windowCountDistinct_zero
  have hlog : Tendsto (fun T : ℝ => c / 2 * Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h1T : (1 : ℝ) ≤ 1 + T := by linarith
  -- `(1 + T)^(-e) ≥ (1 + T)⁻¹`
  have hpow : (1 + T)⁻¹ ≤ (1 + T) ^ (-e) := by
    have := Real.rpow_le_rpow_of_exponent_le h1T (by linarith : (-1 : ℝ) ≤ -e)
    rwa [Real.rpow_neg_one] at this
  have hstep1 : c / 2 * Real.log T ≤ (windowCountDistinct 0 T : ℝ) * (1 + T) ^ (-e) := by
    have hcT : c * (T * Real.log T) ≤ (windowCountDistinct 0 T : ℝ) := hcount T hT
    have hhalf : c / 2 * Real.log T ≤ c * (T * Real.log T) * (1 + T)⁻¹ := by
      rw [inv_eq_one_div, mul_one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 + T)]
      nlinarith [mul_nonneg (mul_nonneg hc.le hlogT) (by linarith : (0 : ℝ) ≤ T - 1)]
    have h2 : c * (T * Real.log T) * (1 + T)⁻¹
        ≤ (windowCountDistinct 0 T : ℝ) * (1 + T) ^ (-e) := by
      have hnn : (0 : ℝ) ≤ c * (T * Real.log T) := by positivity
      calc c * (T * Real.log T) * (1 + T)⁻¹ ≤ c * (T * Real.log T) * (1 + T) ^ (-e) :=
            mul_le_mul_of_nonneg_left hpow hnn
        _ ≤ (windowCountDistinct 0 T : ℝ) * (1 + T) ^ (-e) :=
            mul_le_mul_of_nonneg_right hcT (Real.rpow_nonneg (by linarith) _)
    linarith
  exact hstep1.trans (mul_rpow_le_sum_rpow_neg_windowZeros he.le)

/-- **The sum `∑_ρ ‖ρ‖^(-e)` over the nontrivial zeroes of `ζ` diverges for every `0 < e ≤ 1`.**
The zeroes are counted without multiplicity. -/
theorem not_summable_rpow_neg {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ¬ Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e)) := by
  classical
  intro hsum
  set B : ℝ := ∑' ρ : nontrivialZeroSet, ‖(ρ : ℂ)‖ ^ (-e) with hB
  have hbound : ∀ T : ℝ, ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e) ≤ B := by
    intro T
    set u : Finset nontrivialZeroSet :=
      ((windowZeros_finite 0 T).toFinset).subtype (· ∈ nontrivialZeroSet) with hu
    have hmem : ∀ ρ ∈ (windowZeros_finite 0 T).toFinset, ρ ∈ nontrivialZeroSet := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      exact hρ.1
    have hsumeq : ∑ ρ ∈ u, ‖(ρ : ℂ)‖ ^ (-e)
        = ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e) := by
      rw [hu, Finset.sum_subtype_eq_sum_filter (f := fun x : ℂ => ‖x‖ ^ (-e))]
      exact Finset.sum_filter_of_ne fun ρ hρ _ => hmem ρ hρ
    rw [← hsumeq]
    exact hsum.sum_le_tsum u (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨T, hT⟩ :=
    ((tendsto_sum_rpow_neg_windowZeros_atTop he he1).eventually_gt_atTop B).exists
  exact absurd (hbound T) (not_le.mpr hT)

/-- **`∑_ρ 1/‖ρ‖` diverges over the nontrivial zeroes of `ζ`**: the exponent of convergence of
the zero set is at least `1`. -/
theorem not_summable_inv_norm : ¬ Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖⁻¹) := by
  have h := not_summable_rpow_neg (e := 1) one_pos le_rfl
  simpa only [Real.rpow_neg_one] using h

/-- For a nonpositive exponent the sum diverges as well, since the terms are bounded away from
`0` and there are infinitely many zeroes. -/
theorem not_summable_rpow_neg_of_nonpos {e : ℝ} (he : e ≤ 0) :
    ¬ Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e)) := by
  intro hsum
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_nontrivialZero
  have hinf : Infinite nontrivialZeroSet := infinite_coe_iff.mpr infinite_nontrivialZeroSet
  have hzero := hsum.tendsto_cofinite_zero
  have hlow : ∀ ρ : nontrivialZeroSet, δ ^ (-e) ≤ ‖(ρ : ℂ)‖ ^ (-e) := fun ρ =>
    Real.rpow_le_rpow hδ.le (hδle _ ρ.2) (by linarith)
  have hδpow : 0 < δ ^ (-e) := Real.rpow_pos_of_pos hδ _
  have hev : ∀ᶠ ρ : nontrivialZeroSet in cofinite,
      dist (‖(ρ : ℂ)‖ ^ (-e)) 0 < δ ^ (-e) := Metric.tendsto_nhds.mp hzero _ hδpow
  obtain ⟨ρ, hρ⟩ := hev.exists
  have hge : δ ^ (-e) ≤ ‖(ρ : ℂ)‖ ^ (-e) := hlow ρ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hρ
  linarith

/-- **The exponent of convergence of the nontrivial zeroes of `ζ` is exactly `1`.**  The set of
exponents `e` for which `∑_ρ ‖ρ‖^(-e)` converges is `(1, ∞)`, whose infimum is `1`. -/
theorem sInf_exponent_summable_eq_one :
    sInf {e : ℝ | Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e))} = 1 := by
  have hset : {e : ℝ | Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e))} = Set.Ioi 1 := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
    constructor
    · intro h
      by_contra hlt
      rw [not_lt] at hlt
      rcases le_or_gt e 0 with h0 | h0
      · exact not_summable_rpow_neg_of_nonpos h0 h
      · exact not_summable_rpow_neg h0 hlt h
    · intro h
      have := summable_inv_norm_rpow (e := e - 1) (by linarith)
      simpa only [show (1 : ℝ) + (e - 1) = e by ring] using this
  rw [hset, csInf_Ioi]

end RiemannHypothesis
