/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareBohrLandau
import RiemannHypothesis.NearLine

/-!
# The Bohr–Landau mean square, uniformly in the abscissa

`RiemannHypothesis.exists_integral_normSq_riemannZeta_le_half` gives, for each fixed
`1/2 < σ < 1`, a constant `C σ` with `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C σ · T`.  The zero-density
argument of `RiemannHypothesis.BohrLandau` averages `log ‖ζ‖` over circles, and a circle meets a
whole *interval* of abscissas, so it needs the bound to hold with **one** constant for every
abscissa in a range `[σ₀, ∞)`.

Two changes make that possible.

* The integration starts at `t = 1` rather than `t = 0`.  The only term of the argument that
  degenerates as `σ → 1` is the contribution `∫ dt / ((1-σ)² + t²)` of the pole of `ζ` at `s = 1`,
  and away from `t = 0` that integral is bounded by `∫₁^∞ dt/t² = 1`, uniformly in `σ`.  This also
  removes the restriction `σ < 1` altogether: the statement below holds for **all** `σ ≥ σ₀`.
* The order `m` of the Euler–Maclaurin expansion is chosen once and for all from `σ₀`, and every
  constant entering the argument is estimated at `σ₀`; each of them is monotone in `σ`.

## Main results

* `offDiagSum_antitone` : the off-diagonal sum of the Dirichlet-polynomial mean value theorem is
  nonincreasing in `σ`.
* `integral_normSq_dirichletPoly_one_le_uniform` : the mean square of `∑_{n ≤ N} n^(-s)`,
  uniformly for `σ ≥ σ₀`.
* `exists_norm_riemannZeta_sub_dirichletPoly_le_em_uniform` : the Euler–Maclaurin bound of order
  `m`, uniformly for `σ ≥ σ₀` (and `|t| ≥ 1`, which is what makes `σ ≥ 1` admissible).
* `exists_integral_normSq_riemannZeta_le_uniform` : **for every `σ₀ > 1/2` there is a constant `C`
  with `∫₁ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T` for every `σ ≥ σ₀` and every `T ≥ 1`.**
* `integral_normSq_riemannZeta_le_uniform_Icc` : the same on a general interval `[a, b] ⊆ [1, ∞)`.
-/

noncomputable section

open Complex Real MeasureTheory

namespace RiemannHypothesis

/-! ## Monotonicity of the off-diagonal sum -/

/-- The off-diagonal sum of the mean value theorem is nonincreasing in `σ`: every summand is a
nonnegative multiple of `(m n)^(-σ)`. -/
theorem offDiagSum_antitone (a : ℕ → ℂ) (N : ℕ) {σ₀ σ : ℝ} (h : σ₀ ≤ σ) :
    offDiagSum a N σ ≤ offDiagSum a N σ₀ := by
  unfold offDiagSum
  refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, if_false]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hmp : (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    have hnp : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    gcongr

/-- **The mean square of the truncated zeta sum, uniformly in `σ ≥ σ₀`.** -/
theorem integral_normSq_dirichletPoly_one_le_uniform {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ C * (T + (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N)) := by
  obtain ⟨C₁, hC₁, hoff⟩ := offDiagSum_one_le h0 h1
  have h2σ : (1 : ℝ) < 2 * σ₀ := by linarith
  set D : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ₀)) with hD
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(2 * σ₀))) :=
    summable_natAddOne_rpow_neg h2σ
  have hD0 : 0 ≤ D := tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  refine ⟨D + C₁, by linarith, fun σ hσ N hN T hT => ?_⟩
  have hdiag : ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤ D := by
    have hle : ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
        ≤ ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * σ₀)) := by
      rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_le_sum fun i _ => ?_
      have hbase : (1 : ℝ) ≤ (i : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      have : ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [norm_one, one_pow, one_mul, this,
        show (-2 * σ) = -(2 * σ) by ring]
      exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    exact hle.trans (hsum.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (by positivity) _))
  have hmain := integral_normSq_dirichletPoly_le_diag_add_offDiag (fun _ => 1) N σ hT
  have hoffN : offDiagSum (fun _ => 1) N σ ≤ C₁ * (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N) :=
    (offDiagSum_antitone _ N hσ).trans (hoff N hN)
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    positivity
  nlinarith [hmain, hoffN, hdiag, hT, hD0, hC₁]

/-! ## The Euler–Maclaurin bound, uniformly in `σ` -/

/-- **The Euler–Maclaurin bound of order `m`, uniformly in `σ ≥ σ₀`.**  Compared with
`exists_norm_riemannZeta_sub_dirichletPoly_le_em` the abscissa is no longer bounded above by `1`;
the price is the harmless restriction `1 ≤ |t|`, which keeps `s` away from the pole. -/
theorem exists_norm_riemannZeta_sub_dirichletPoly_le_em_uniform (m : ℕ) (hm : 1 ≤ m) {σ₀ : ℝ}
    (h0 : 0 < σ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 1 ≤ |t| → σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨C₁, hC₁, hC₁bd⟩ := exists_norm_emTail_one_le m hm
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bq_bound m
  have hden₀ : (0 : ℝ) < σ₀ + (m : ℝ) - 1 := by linarith
  refine ⟨max (C₁ + 1) (Cb / (σ₀ + (m : ℝ) - 1)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), fun σ hσ N hN t ht1 htN => ?_⟩
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le h0 hσ
  have hden : (0 : ℝ) < σ + (m : ℝ) - 1 := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact hσ0
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht1
    simp at ht1
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
    exact ht0 him.symm
  have hnorm_s : ‖s‖ ≤ σ + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_pos hσ0] at h
    exact h
  have hsN : ‖s‖ ≤ (N : ℝ) := le_trans hnorm_s htN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [riemannZeta_eq_trapApprox N hs0 hs1, ← dirichletPoly_one N s,
    ← emTail_one_eq_tsum_trapTerm hs0 hs1 N]
  have hsplit : dirichletPoly (fun _ => 1) N s + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s - dirichletPoly (fun _ => 1) N s
      = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        + (((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s) := by ring
  rw [hsplit]
  have hpole : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ = ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  have hhalf : ‖((N + 1 : ℝ) : ℂ) ^ (-s) / 2‖ ≤ (N : ℝ) ^ (-σ) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hmono : ((N : ℝ) + 1) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
    simp only [hre, Complex.neg_re, Complex.norm_ofNat]
    linarith
  have htailm : ‖emTail m N s‖
      ≤ Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
    have h := norm_emTail_le m hm hCb hs0 hN
    rw [hre] at h
    refine h.trans ?_
    have hpoch : ‖poch m s‖ ≤ (σ + |t| + m) ^ m := by
      refine (norm_poch_le m s).trans ?_
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hexp : (N : ℝ) ^ (1 - (σ + (m : ℝ))) = (N : ℝ) ^ (1 - σ - (m : ℝ)) := by ring_nf
    have hrp : (0 : ℝ) < (N : ℝ) ^ (1 - σ - (m : ℝ)) := Real.rpow_pos_of_pos hN0 _
    rw [hexp]
    have hRD : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1) := by positivity
    have hstep1 : Cb * ‖poch m s‖ * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1))
        ≤ Cb * (σ + |t| + m) ^ m * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoch hCb0.le) hRD
    have hstep2 : Cb * (σ + |t| + m) ^ m * ((N : ℝ) ^ (1 - σ - (m : ℝ)) / (σ + (m : ℝ) - 1))
        = Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
      field_simp
    linarith
  have htail1 : ‖emTail 1 N s‖
      ≤ C₁ * (N : ℝ) ^ (-σ)
        + Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ))) := by
    have h := hC₁bd s hs0 N hN hsN
    rw [hre] at h
    linarith
  have hA : (0 : ℝ) < (N : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hN0 _
  have hB : (0 : ℝ) ≤ (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)) := by positivity
  have hmax1 : C₁ + 1 ≤ max (C₁ + 1) (Cb / (σ₀ + (m : ℝ) - 1)) := le_max_left _ _
  have hmono₀ : Cb / (σ + (m : ℝ) - 1) ≤ Cb / (σ₀ + (m : ℝ) - 1) :=
    div_le_div_of_nonneg_left hCb0.le hden₀ (by linarith)
  have hmax2 : Cb / (σ + (m : ℝ) - 1) ≤ max (C₁ + 1) (Cb / (σ₀ + (m : ℝ) - 1)) :=
    hmono₀.trans (le_max_right _ _)
  have hfinal := norm_add_le (((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1))
    (((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s)
  have hsecond : ‖((N + 1 : ℝ) : ℂ) ^ (-s) / 2 + emTail 1 N s‖
      ≤ (N : ℝ) ^ (-σ) + (C₁ * (N : ℝ) ^ (-σ)
        + Cb / (σ + (m : ℝ) - 1) * ((σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)))) :=
    (norm_add_le _ _).trans (add_le_add hhalf htail1)
  rw [hpole] at hfinal
  nlinarith [hfinal, hsecond, hA, hB, hmax1, hmax2]

/-! ## Continuity and the pole integral away from `t = 0` -/

/-- `t ↦ ‖ζ(σ + i t)‖²` is continuous on `[1, ∞)`, for every abscissa `σ`. -/
theorem continuousOn_normSq_riemannZeta_line (σ : ℝ) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Set.Ici 1) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hline : ContinuousAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
  have hz : ContinuousAt (fun u : ℝ => riemannZeta ((σ : ℂ) + (u : ℂ) * I)) t :=
    ContinuousAt.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (g := riemannZeta)
      ((differentiableAt_riemannZeta hne).continuousAt) hline
  exact (hz.norm.pow 2).continuousWithinAt

/-- Away from `t = 0` the contribution of the pole is bounded uniformly in `σ`. -/
theorem integral_inv_sq_shift_le_one (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ 1 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) T := by
    rw [Set.uIcc_of_le hT]; simp only [Set.mem_Icc, not_and, not_le]; intro h; linarith
  have hle : ∀ t ∈ Set.Icc (1 : ℝ) T, 1 / ((1 - σ) ^ 2 + t ^ 2) ≤ t ^ (-2 : ℤ) := by
    intro t ht
    have h1 : (1 : ℝ) ≤ t := ht.1
    have key : t ^ (-2 : ℤ) = 1 / t ^ 2 := by rw [zpow_neg, one_div]; norm_cast
    rw [key]
    have hden : t ^ 2 ≤ (1 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (1 - σ)]
    exact one_div_le_one_div_of_le (pow_pos (by linarith) 2) hden
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have h1 : (1 : ℝ) ≤ t := ht.1
    nlinarith [sq_nonneg (1 - σ)]
  have hi2 : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) volume 1 T :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hmem)
  refine (intervalIntegral.integral_mono_on hT hi1 hi2 hle).trans ?_
  rw [integral_zpow (Or.inr ⟨by norm_num, hmem⟩)]
  have hpos : (0 : ℝ) < T⁻¹ := by positivity
  norm_num
  linarith

/-! ## The pointwise and integrated bounds -/

/-- The pointwise Euler–Maclaurin bound, squared, with no upper restriction on `σ`. -/
theorem normSq_riemannZeta_le_pointwise_em_uniform {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 1 ≤ |t| → σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T t : ℝ} (ht0 : 1 ≤ t) (htT : t ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)))
        + 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ))
        + 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set P : ℂ := dirichletPoly (fun _ => 1) N s with hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have habs : |t| = t := abs_of_nonneg (by linarith)
  have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    simp [Complex.normSq_apply]
    ring
  have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
    have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (1 - σ)]
    nlinarith [norm_nonneg (s - 1), hnormsq]
  have hbdt := hbd N hN t (by rw [habs]; linarith) (by rw [habs]; linarith)
  set A : ℝ := (N : ℝ) ^ (-σ) with hA
  set B : ℝ := (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - (m : ℝ)) with hB
  set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
  have hA0 : 0 ≤ A := Real.rpow_nonneg hN0.le _
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : (0 : ℝ) ≤ σ + |t| + m := by positivity
    positivity
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + E1 + C * (A + B) := by
    have := norm_sub_norm_le (riemannZeta s) P
    linarith [hbdt]
  have hCAB : 0 ≤ C * (A + B) := by positivity
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ 3 * (‖P‖ ^ 2 + E1 ^ 2 + (C * (A + B)) ^ 2) := by
    nlinarith [norm_nonneg (riemannZeta s), norm_nonneg P, hE10, hCAB, htri,
      sq_nonneg (‖P‖ - E1), sq_nonneg (‖P‖ - C * (A + B)), sq_nonneg (E1 - C * (A + B))]
  have hE1sq : E1 ^ 2 = ((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    rw [hE1, div_pow, hnormsq, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hAsq : A ^ 2 = (N : ℝ) ^ (-(2 * σ)) := by
    rw [hA, ← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hBsq : B ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
    have hpow : ((N : ℝ) ^ (1 - σ - (m : ℝ))) ^ 2 = (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 - σ - (m : ℝ))) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    have hbase : σ + |t| + m ≤ σ + T + m := by rw [habs]; linarith
    have hb0 : (0 : ℝ) ≤ σ + |t| + m := by positivity
    have hmono : ((σ + |t| + m) ^ m) ^ 2 ≤ ((σ + T + m) ^ m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hb0 hbase m) 2
    rw [hB, mul_pow, hpow]
    have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
    exact mul_le_mul_of_nonneg_right hmono hrp
  have hprod : (C * (A + B)) ^ 2 ≤ 2 * C ^ 2 * (A ^ 2 + B ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg (A - B))]
  have h6 : (0 : ℝ) ≤ 6 * C ^ 2 := by positivity
  have hA2 : 6 * C ^ 2 * A ^ 2 = 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) := by rw [hAsq]
  have hB2 : 6 * C ^ 2 * B ^ 2
      ≤ 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left hBsq h6
  linarith [hsq, hE1sq, hprod, hA2, hB2]

/-- The mean square of `ζ` on `[1, T]`, in terms of the length `N` of the Dirichlet polynomial. -/
theorem integral_normSq_riemannZeta_le_aux_em_uniform {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 1 ≤ |t| → σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ)
        + 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T
        + 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set D : ℝ := 6 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) with hD
  set E : ℝ := 6 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) with hE
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hE0 : 0 ≤ E := by
    rw [hE]
    have : (0 : ℝ) ≤ σ + T + m := by positivity
    positivity
  have hzetaC : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Set.uIcc (1 : ℝ) T) := by
    rw [Set.uIcc_of_le hT]
    exact (continuousOn_normSq_riemannZeta_line σ).mono fun t ht => ht.1
  have hPC := continuous_normSq_dirichletPoly_line (σ := σ) N
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    ((hPC.const_smul (3 : ℝ)).congr fun t => by simp [smul_eq_mul]).intervalIntegrable 1 T
  have hi2 : IntervalIntegrable
      (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    refine continuousOn_const.mul (continuousOn_const.mul ?_)
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have h1 : (1 : ℝ) ≤ t := ht.1
    nlinarith [sq_nonneg (1 - σ)]
  have hi3 : IntervalIntegrable (fun _ : ℝ => D) volume 1 T := intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun _ : ℝ => E) volume 1 T := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hzetaC.intervalIntegrable)
    (((hi1.add hi2).add hi3).add hi4)
    (fun t ht => normSq_riemannZeta_le_pointwise_em_uniform h0 hC hbd hN ht.1 ht.2 hTN)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  have hφ : (∫ t in (1 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ 1 :=
    integral_inv_sq_shift_le_one σ hT
  -- the Dirichlet polynomial integral over `[1, T]` is at most the one over `[0, T]`
  have hPi0 : IntervalIntegrable
      (fun t : ℝ => ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 1 :=
    hPC.intervalIntegrable 0 1
  have hPi1 : IntervalIntegrable
      (fun t : ℝ => ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    hPC.intervalIntegrable 1 T
  have hadd := intervalIntegral.integral_add_adjacent_intervals hPi0 hPi1
  have hnn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1,
      ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity
  have hPle : (∫ t in (1 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    linarith
  simp only [smul_eq_mul]
  nlinarith [hφ, hA0, hD0, hE0, hPle, hT]

/-! ## Large abscissas -/

/-- For `Re s ≥ 2` the Dirichlet series of `ζ` is dominated by `∑ n⁻² ≤ 2`. -/
theorem norm_riemannZeta_le_two_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 := by
  have hre : 1 < s.re := by linarith
  set g : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hg
  set G : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-s.re) with hG
  have hnorm : ∀ n : ℕ, ‖g n‖ = G n := by
    intro n
    rw [hg, hG]
    simp only
    rw [norm_div, norm_one,
      show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)),
      Real.rpow_neg (by positivity)]
    push_cast
    rw [one_div]
  have hGsummable : Summable G := summable_natAddOne_rpow_neg hre
  have hnormsummable : Summable (fun n => ‖g n‖) := hGsummable.congr fun n => (hnorm n).symm
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hle : ‖riemannZeta s‖ ≤ ∑' n : ℕ, G n := by
    rw [hzeta]
    refine (norm_tsum_le_tsum_norm hnormsummable).trans ?_
    exact le_of_eq (tsum_congr hnorm)
  refine hle.trans ?_
  have hsplit : ∑' n : ℕ, G n = G 0 + ∑' n : ℕ, G (n + 1) := hGsummable.tsum_eq_zero_add
  have hG0 : G 0 = 1 := by simp [hG]
  have htail : ∑' n : ℕ, G (n + 1) ≤ 1 := by
    have h := tsum_shift_rpow_neg_le_rpow (p := s.re) hre (N := 1) le_rfl
    have hcongr : ∀ n : ℕ, G (n + 1) = (((n + 1 : ℕ) : ℝ) + 1) ^ (-s.re) := by
      intro n; simp [hG]
    have heq : ∑' n : ℕ, G (n + 1) = ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) + 1) ^ (-s.re) :=
      tsum_congr hcongr
    rw [heq]
    refine h.trans ?_
    rw [Nat.cast_one, Real.one_rpow, div_le_one (by linarith)]
    linarith
  rw [hsplit, hG0]
  linarith

/-! ## The uniform mean square -/

set_option maxHeartbeats 1600000 in
-- This proof assembles a dozen separate rpow estimates in a single declaration; the default
-- heartbeat budget is not enough for the accumulated `linarith`/`nlinarith` calls.
/-- **The Bohr–Landau mean square, uniformly in the abscissa.**  For every `σ₀ > 1/2` there is a
constant `C` such that `∫₁ᵀ ‖ζ(σ + i t)‖² dt ≤ C · T` for **every** `σ ≥ σ₀` and every `T ≥ 1`.

Note that there is no upper bound on `σ`: for `σ ≥ 1` the estimate is easier, and the argument
below covers all abscissas at once. -/
theorem exists_integral_normSq_riemannZeta_le_uniform {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T := by
  have hs0 : (0 : ℝ) < σ₀ := by linarith
  have h1s : (0 : ℝ) < 1 - σ₀ := by linarith
  have h2s : (0 : ℝ) < 2 * σ₀ - 1 := by linarith
  -- the order of the expansion, fixed once and for all by `σ₀`
  set m : ℕ := ⌈(1 - σ₀) / (2 * σ₀ - 1)⌉₊ + 1 with hm_def
  have hm : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmgt : (1 - σ₀) / (2 * σ₀ - 1) < (m : ℝ) := by
    have h := Nat.le_ceil ((1 - σ₀) / (2 * σ₀ - 1))
    have hcast : ((⌈(1 - σ₀) / (2 * σ₀ - 1)⌉₊ : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [hm_def]; push_cast; ring
    linarith
  have hkey0 : 1 - σ₀ < (m : ℝ) * (2 * σ₀ - 1) := by
    rw [div_lt_iff₀ h2s] at hmgt
    linarith
  have hden : (0 : ℝ) < σ₀ + (m : ℝ) - 1 := by linarith
  set e : ℝ := (m : ℝ) / (σ₀ + (m : ℝ) - 1) with he_def
  have he1 : (1 : ℝ) ≤ e := by
    rw [he_def, le_div_iff₀ hden]; linarith
  have he0 : (0 : ℝ) < e := by linarith
  set a : ℝ := e * (2 - 2 * σ₀) with ha_def
  have ha1 : a < 1 := by
    rw [ha_def, he_def, div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  have ha0 : (0 : ℝ) < a := by rw [ha_def]; exact mul_pos he0 (by linarith)
  -- the ingredients
  obtain ⟨Cem, hCem, hembd⟩ := exists_norm_riemannZeta_sub_dirichletPoly_le_em_uniform m hm hs0
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le_uniform h0 h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  set L : ℝ := Real.log 8 with hL_def
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by norm_num)
  set K : ℝ := 64 * (1 + L + e) * C₃ with hK_def
  have hK0 : (0 : ℝ) ≤ K := mul_nonneg (by linarith) hC₃.le
  refine ⟨3 * C₂ * (1 + K) + 3 * 64 + 6 * Cem ^ 2
      + 6 * Cem ^ 2 * ((3 + (m : ℝ)) ^ m) ^ 2 + 4, ?_, fun σ hσ T hT => ?_⟩
  · have hb1 : (0 : ℝ) < 3 * C₂ * (1 + K) :=
      mul_pos (by linarith) (by linarith)
    have hb3 : (0 : ℝ) < 6 * Cem ^ 2 := by positivity
    have hb4 : (0 : ℝ) ≤ 6 * Cem ^ 2 * ((3 + (m : ℝ)) ^ m) ^ 2 := by positivity
    linarith
  -- fix `σ` and `T`
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le hs0 hσ
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  by_cases hσ2 : σ ≤ 2
  swap
  · -- large abscissas: `‖ζ‖ ≤ 2` pointwise
    push Not at hσ2
    have hbd : ∀ t ∈ Set.Icc (1 : ℝ) T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ 4 := by
      intro t _
      have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
      have := norm_riemannZeta_le_two_of_two_le_re (s := (σ : ℂ) + (t : ℂ) * I)
        (by rw [hre]; linarith)
      nlinarith [norm_nonneg (riemannZeta ((σ : ℂ) + (t : ℂ) * I))]
    have hint : IntervalIntegrable
        (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hT]
      exact (continuousOn_normSq_riemannZeta_line σ).mono fun t ht => ht.1
    have := intervalIntegral.integral_mono_on hT hint intervalIntegrable_const hbd
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hp1 : (0 : ℝ) ≤ 3 * C₂ * (1 + K) := mul_nonneg (by linarith) (by linarith)
    have hp2 : (0 : ℝ) ≤ 6 * Cem ^ 2 := by positivity
    have hp3 : (0 : ℝ) ≤ 6 * Cem ^ 2 * ((3 + (m : ℝ)) ^ m) ^ 2 := by positivity
    have hCge : (4 : ℝ) ≤ 3 * C₂ * (1 + K) + 3 * 64 + 6 * Cem ^ 2
        + 6 * Cem ^ 2 * ((3 + (m : ℝ)) ^ m) ^ 2 + 4 := by linarith
    have hmulT := mul_le_mul_of_nonneg_right hCge hT0.le
    linarith
  -- the main range `σ₀ ≤ σ ≤ 2`
  set x : ℝ := T ^ e with hx_def
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hT he0.le
  have hx0 : (0 : ℝ) < x := by linarith
  have hTx : T ≤ x := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le hT he1
  set N : ℕ := ⌈x⌉₊ + ⌈T⌉₊ + 3 with hN_def
  have hN1 : 1 ≤ N := by omega
  have hNcast : (N : ℝ) = (⌈x⌉₊ : ℝ) + (⌈T⌉₊ : ℝ) + 3 := by rw [hN_def]; push_cast; ring
  have hNx : x ≤ (N : ℝ) := by
    have h := Nat.le_ceil x
    have hpos : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hNT : σ + T ≤ (N : ℝ) := by
    have h := Nat.le_ceil T
    have hpos : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hN8 : (N : ℝ) + 1 ≤ 8 * x := by
    have h1' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have h2' : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    rw [hNcast]
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- powers of `N`
  have hxa : x ^ (2 - 2 * σ₀) = T ^ a := by
    rw [hx_def, ← Real.rpow_mul hT0.le, ha_def]
  have h8pow : (8 : ℝ) ^ (2 - 2 * σ₀) ≤ 64 := by
    calc (8 : ℝ) ^ (2 - 2 * σ₀) ≤ (8 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 64 := by norm_num
  have hTa : T ^ a ≤ T := by
    calc T ^ a ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha1.le
      _ = T := Real.rpow_one T
  have hTa0 : (0 : ℝ) ≤ T ^ a := Real.rpow_nonneg hT0.le _
  have hNp1a : ((N : ℝ) + 1) ^ (2 - 2 * σ₀) ≤ 64 * T ^ a := by
    have h2 : ((N : ℝ) + 1) ^ (2 - 2 * σ₀) ≤ (8 * x) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow (by linarith) hN8 (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    linarith only [h2, mul_le_mul_of_nonneg_right h8pow hTa0]
  have hNa : (N : ℝ) ^ (2 - 2 * σ₀) ≤ 64 * T ^ a := by
    have h2 : (N : ℝ) ^ (2 - 2 * σ₀) ≤ ((N : ℝ) + 1) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
    linarith only [h2, hNp1a]
  have hNlog : Real.log N ≤ L + e * Real.log T := by
    have hle : Real.log N ≤ Real.log (8 * x) := Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), hx_def, Real.log_rpow hT0] at hle
    linarith only [hle]
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
  have hNprod : (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N) ≤ K * T := by
    have hLlog : (0 : ℝ) ≤ L * Real.log T := mul_nonneg hL0 hlogT
    have hexpand : (1 + L + e) * (1 + Real.log T)
        = 1 + Real.log T + L + L * Real.log T + e + e * Real.log T := by ring
    have hstep : 1 + Real.log N ≤ (1 + L + e) * (1 + Real.log T) := by
      rw [hexpand]
      linarith only [hNlog, hLlog, hlogT, he0]
    calc (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N)
        ≤ 64 * T ^ a * ((1 + L + e) * (1 + Real.log T)) :=
          mul_le_mul hNa hstep (by linarith) (by linarith [hTa0])
      _ = 64 * (1 + L + e) * (T ^ a * (1 + Real.log T)) := by ring
      _ ≤ 64 * (1 + L + e) * (C₃ * T) :=
          mul_le_mul_of_nonneg_left (hlog T hT) (by linarith)
      _ = K * T := by rw [hK_def]; ring
  -- the negative powers of `N`
  have hNneg : (N : ℝ) ^ (-(2 * σ)) ≤ 1 := by
    have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := (N : ℝ)) (by norm_num) hN1'
      (by linarith : -(2 * σ) ≤ 0)
    simpa using this
  have heexp : e * (2 - 2 * σ - 2 * (m : ℝ)) ≤ -(2 * (m : ℝ)) := by
    rw [he_def, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have hNm : (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ T ^ (-(2 * (m : ℝ))) := by
    have hexp : 2 - 2 * σ - 2 * (m : ℝ) ≤ 0 := by linarith
    have h2 : (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ x ^ (2 - 2 * σ - 2 * (m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hNx hexp
    have h3 : x ^ (2 - 2 * σ - 2 * (m : ℝ)) ≤ T ^ (-(2 * (m : ℝ))) := by
      rw [hx_def, ← Real.rpow_mul hT0.le]
      exact Real.rpow_le_rpow_of_exponent_le hT heexp
    linarith
  have hTm2 : ((T : ℝ) ^ m) ^ 2 = T ^ (2 * (m : ℝ)) := by
    rw [← Real.rpow_natCast T m, ← Real.rpow_natCast (T ^ (m : ℝ)) 2, ← Real.rpow_mul hT0.le]
    ring_nf
  have hbig : ((σ + T + (m : ℝ)) ^ m) ^ 2 ≤ ((3 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ)) := by
    have hbase : σ + T + (m : ℝ) ≤ (3 + (m : ℝ)) * T := by
      have hmT : (m : ℝ) * 1 ≤ (m : ℝ) * T :=
        mul_le_mul_of_nonneg_left hT (by linarith)
      linarith only [hmT, hT, hσ2]
    have hb0 : (0 : ℝ) ≤ σ + T + (m : ℝ) := by positivity
    have hp := pow_le_pow_left₀ hb0 hbase m
    rw [mul_pow] at hp
    have hsq : ((σ + T + (m : ℝ)) ^ m) ^ 2 ≤ ((3 + (m : ℝ)) ^ m * T ^ m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp 2
    rw [mul_pow, hTm2] at hsq
    exact hsq
  have herr : ((σ + T + (m : ℝ)) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))
      ≤ ((3 + (m : ℝ)) ^ m) ^ 2 := by
    have hnn2 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
    have hcancel : T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ))) = 1 := by
      rw [← Real.rpow_add hT0]
      norm_num
    calc ((σ + T + (m : ℝ)) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))
        ≤ (((3 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ))) * T ^ (-(2 * (m : ℝ))) :=
          mul_le_mul hbig hNm hnn2 (by positivity)
      _ = ((3 + (m : ℝ)) ^ m) ^ 2 * (T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ)))) := by ring
      _ = ((3 + (m : ℝ)) ^ m) ^ 2 := by rw [hcancel, mul_one]
  -- assemble
  have hembdσ := hembd σ hσ
  have hmain := integral_normSq_riemannZeta_le_aux_em_uniform (m := m) (C := Cem) hσ0 hCem.le
    hembdσ hN1 hT hNT
  have hb1 : 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * C₂ * (1 + K) * T := by
    calc 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 3 * (C₂ * (T + (N : ℝ) ^ (2 - 2 * σ₀) * (1 + Real.log N))) := by
          linarith only [hpoly σ hσ N hN1 T hT0.le]
      _ ≤ 3 * (C₂ * (T + K * T)) := by
          linarith only [mul_le_mul_of_nonneg_left hNprod hC₂.le]
      _ = 3 * C₂ * (1 + K) * T := by ring
  have hb2 : 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 3 * 64 * T := by
    have hmono : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ ((N : ℝ) + 1) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 64 * T := by
      linarith only [hmono, hNp1a, hTa]
    linarith
  have hb3 : 6 * Cem ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T ≤ 6 * Cem ^ 2 * T := by
    have hnn : (0 : ℝ) ≤ 6 * Cem ^ 2 * T := by positivity
    linarith only [mul_le_mul_of_nonneg_left hNneg hnn]
  have hb4 : 6 * Cem ^ 2 * (((σ + T + (m : ℝ)) ^ m) ^ 2
        * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T
      ≤ 6 * Cem ^ 2 * ((3 + (m : ℝ)) ^ m) ^ 2 * T := by
    have hnn : (0 : ℝ) ≤ 6 * Cem ^ 2 * T := by positivity
    linarith only [mul_le_mul_of_nonneg_left herr hnn]
  linarith only [hmain, hb1, hb2, hb3, hb4, hT0]

/-- The uniform mean square on a general interval `[a, b] ⊆ [1, ∞)`. -/
theorem integral_normSq_riemannZeta_le_uniform_Icc {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * b := by
  obtain ⟨C, hC, hbd⟩ := exists_integral_normSq_riemannZeta_le_uniform h0 h1
  refine ⟨C, hC, fun σ hσ a b ha hab => ?_⟩
  have h1b : (1 : ℝ) ≤ b := le_trans ha hab
  have hcont := continuousOn_normSq_riemannZeta_line σ
  have hint : ∀ u v : ℝ, 1 ≤ u → u ≤ v → IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume u v := by
    intro u v hu huv
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le huv]
    exact fun t ht => le_trans hu ht.1
  have hsplit : (∫ t in (1 : ℝ)..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      = (∫ t in (1 : ℝ)..a, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + ∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 1 a le_rfl ha)
      (hint a b ha hab)).symm
  have hnn : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..a, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun t _ => by positivity)
  have := hbd σ hσ b h1b
  linarith [hsplit ▸ this]

end RiemannHypothesis
