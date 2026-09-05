/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CarlsonPowerSaving

/-!
# The density theorem with a power saving: `N(σ, T) = O(T^(1−c))`

`RiemannHypothesis/CarlsonDensity.lean` proves Carlson's density theorem in the qualitative
form `N(σ, T) = o(T)`.  `RiemannHypothesis/CarlsonPowerSaving.lean` upgrades the analytic
input — the mean square of `ζ M_y − 1` — to a quantitative estimate in which the mollifier
length `y` is allowed to grow with the height.  This file feeds that estimate into the Jensen
counting inequality of `RiemannHypothesis/CarlsonDensity.lean` and obtains a genuine power
saving.

## The balancing

With `y = ⌈T^γ⌉` and the parameter `λ = T^c'` of the logarithmic majorant, the counting
inequality

`κ · N(σ, T) · log (R/r) ≤ (λ/2) ∫_4^T A(u) du + (1/(2λ) + 2/y) (T − 4)`

has right-hand side `≤ (C + 3) T^(1 − c')`, because the vertical integral of the circle
averages is `≤ C (T y^(−θ) + T^(1−c₁))`, and each of the three terms `λ T^(1−γθ)`,
`T/λ` and `T/y` is `T^(1−c')` once `c' ≤ min (γθ/2) (c₁/2) γ`.

## Main results

* `exists_ncard_zerosRightOf_high_le_rpow` — the estimate for the zeroes of ordinate `≥ 5`.
* `exists_ncard_zerosRightOf_le_rpow` — **the power saving**: for `1/2 < σ < 1` there are
  `c > 0` and `C` with `N(σ, T) ≤ C T^(1−c)` for all `T ≥ 1`, and the saving satisfies
  `c ≥ (σ − 1/2)²/64`.
* `exists_ncard_zerosOffCriticalLine_le_rpow` — the two-sided form.
* `ncard_zerosRightOf_le_rpow_explicit` and `ncard_zerosOffCriticalLine_le_rpow_explicit` —
  the same with the exponent named: `N(σ, T) ≤ C(σ) T^(1 − (σ−1/2)²/64)`.

## The exponent

Every exponent in the chain is tracked in `θ = σ₀ − 1/2`, the distance from the critical line
that the circles of the Jensen step leave available; here `θ = (σ − 1/2)/2`.  The
Montgomery–Vaughan half contributes `1 − θ/2`, the Euler–Maclaurin half at most `1 − θ`, the
mollifier has length `T^{θ/8}` and the mean square saves `3θ/8`; balancing the three terms
`λ T^{1−γθ}`, `T/λ` and `T/y` gives the saving `θ²/16 = (σ − 1/2)²/64`.

## Scope

The saving `(σ − 1/2)²/64` is explicit in `σ` and degrades continuously to `0` as `σ ↓ 1/2`,
but it is far from Carlson's `1 − 4σ(1 − σ)`, whose saving is `4(σ − 1/2)²`: the shape in
`σ − 1/2` is the same, the constant is `256` times worse.  The constant `C(σ)` is *not*
explicit.  Nothing is claimed uniformly in `σ`, and nothing at `σ = 1/2`.  Zeroes are counted
without multiplicity.  No zero is located, and the Riemann hypothesis is neither proved nor
disproved.
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set

namespace RiemannHypothesis

set_option maxHeartbeats 1000000 in
-- the proof carries the Jensen geometry, the windowed counting function and four exponents
/-- **The power saving for the zeroes of ordinate at least `5`.**  For `1/2 < σ < 1` there are
`c > 0` and `C` such that the number of zeroes of `ζ` with real part at least `σ` and ordinate
in `[5, T]` is at most `C T^(1−c)` for all large `T`. -/
theorem exists_ncard_zerosRightOf_high_le_rpow {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ (σ - 1 / 2) ^ 2 / 64 ≤ c ∧
      ∃ T₀ : ℝ, 5 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T}).ncard : ℝ)
        ≤ C * T ^ (1 - c) := by
  classical
  set κ : ℝ := (σ - 1 / 2) / 4 with hκ_def
  set r : ℝ := 3 - σ + κ with hr_def
  set R : ℝ := 3 - σ + 2 * κ with hR_def
  have hκ : 0 < κ := by rw [hκ_def]; linarith
  have hκ1 : κ < 1 := by rw [hκ_def]; linarith
  have hr : 0 < r := by rw [hr_def]; linarith
  have hrR : r < R := by rw [hr_def, hR_def]; linarith
  have hR0 : 0 < R := hr.trans hrR
  have hR52 : R < 5 / 2 := by rw [hR_def, hκ_def]; linarith
  have hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2 := by rw [hr_def]; nlinarith
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  set L : ℝ := Real.log (R / r) with hL_def
  obtain ⟨C₁, c₁, θ, γ, hC₁0, hc₁0, hc₁1, hθ0, hγ0, hθeq, hc₁le, hγeq, b₀, hb₀4, hCA⟩ :=
    exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow hR0 hR52
  -- the three exponents of the analytic input, explicitly in `t = σ − 1/2`
  have hmin : min (5 / 2 - R) (1 / 4) = (σ - 1 / 2) / 2 := by
    have hle : 5 / 2 - R ≤ 1 / 4 := by rw [hR_def, hκ_def]; linarith
    rw [min_eq_left hle, hR_def, hκ_def]; ring
  have hθval : θ = (σ - 1 / 2) / 2 := by rw [hθeq, hmin]
  have hγval : γ = (σ - 1 / 2) / 16 := by rw [hγeq, hmin]; ring
  have hc₁val : 3 * (σ - 1 / 2) / 16 ≤ c₁ := by rw [hmin] at hc₁le; linarith
  -- the saving exponent
  set mn : ℝ := min (γ * θ) c₁ with hmn_def
  have hmn0 : 0 < mn := lt_min (by positivity) hc₁0
  have hmnγθ : mn ≤ γ * θ := min_le_left _ _
  have hmnc₁ : mn ≤ c₁ := min_le_right _ _
  set cc : ℝ := min (min (mn / 2) γ) (1 / 2) with hcc_def
  have hcc0 : 0 < cc := lt_min (lt_min (by linarith) hγ0) (by norm_num)
  have hcchalf : cc ≤ 1 / 2 := min_le_right _ _
  have hccmn : cc ≤ mn / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hccγ : cc ≤ γ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcc1 : cc < 1 := by linarith
  -- the saving is at least `(σ − 1/2)²/64`
  have hccexp : (σ - 1 / 2) ^ 2 / 64 ≤ cc := by
    have ht0 : 0 < σ - 1 / 2 := by linarith
    have ht2 : σ - 1 / 2 < 1 / 2 := by linarith
    have hmn' : (σ - 1 / 2) ^ 2 / 32 ≤ mn := by
      rw [hmn_def, hθval, hγval]
      exact le_min (le_of_eq (by ring)) (by nlinarith [hc₁val])
    rw [hcc_def]
    refine le_min (le_min (by linarith) ?_) (by nlinarith)
    rw [hγval]; nlinarith
  -- the threshold: the mollifier length `⌈T^γ⌉` must be at least `4`
  have hγinv : (0 : ℝ) < 1 / γ := by positivity
  set T₁ : ℝ := (4 : ℝ) ^ (1 / γ) with hT₁_def
  refine ⟨cc, (C₁ + 3) / (κ * L), hcc0, hcc1, by positivity, hccexp,
    max (max b₀ T₁) 5, le_max_right _ _, fun T hT => ?_⟩
  have hT5 : (5 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTb₀ : b₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- the mollifier length and the parameter of the logarithmic majorant
  have hTγ4 : (4 : ℝ) ≤ T ^ γ := by
    have hstep : ((4 : ℝ) ^ (1 / γ)) ^ γ ≤ T ^ γ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hTT₁ hγ0.le
    have heq : ((4 : ℝ) ^ (1 / γ)) ^ γ = 4 := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hγ0),
        Real.rpow_one]
    linarith [hstep, heq]
  set y : ℕ := ⌈T ^ γ⌉₊ with hy_def
  have hyge : T ^ γ ≤ (y : ℝ) := Nat.le_ceil _
  have hy4R : (4 : ℝ) ≤ (y : ℝ) := le_trans hTγ4 hyge
  have hy4 : 4 ≤ y := by exact_mod_cast hy4R
  have hy1 : 1 ≤ y := by omega
  have hyR : (0 : ℝ) < (y : ℝ) := by linarith
  have hyle : (y : ℝ) ≤ 2 * T ^ γ := by
    have hceil : (y : ℝ) ≤ T ^ γ + 1 := by
      rw [hy_def]
      exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
    linarith
  set lam : ℝ := T ^ cc with hlam_def
  have hlam : 0 < lam := Real.rpow_pos_of_pos hT0 cc
  -- the set of zeroes in question, as a finset
  set Z : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T} with hZ_def
  have hZsub : Z ⊆ zerosRightOf σ T := by
    rintro ρ ⟨hz, hre, h5, hle⟩
    exact ⟨hz, hre, by linarith, hle⟩
  have hZfin : Z.Finite := (finite_zerosRightOf (by linarith : (0 : ℝ) < σ)).subset hZsub
  set S : Finset ℂ := hZfin.toFinset with hS_def
  have hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re := by
    intro ρ hρ
    rw [hS_def, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1, hρ.2.1⟩
  have hSim : ∀ ρ ∈ S, 5 ≤ ρ.im ∧ ρ.im ≤ T := by
    intro ρ hρ
    rw [hS_def, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.2.2.1, hρ.2.2.2⟩
  -- the counting function of the windows
  set f : ℝ → ℝ := fun u => ((S.filter fun ρ => |ρ.im - u| ≤ κ).card : ℝ) with hf_def
  have hfsum : ∀ u : ℝ, f u = ∑ ρ ∈ S, (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0) := by
    intro u
    rw [hf_def]
    simp only [Finset.card_filter, Nat.cast_sum, apply_ite (Nat.cast : ℕ → ℝ), Nat.cast_one,
      Nat.cast_zero]
  have hfint : IntervalIntegrable f volume 4 T := by
    have hsum := IntervalIntegrable.sum S
      (fun ρ (_ : ρ ∈ S) => intervalIntegrable_window_indicator ρ.im κ 4 T)
    have heq : (∑ ρ ∈ S, fun u : ℝ => (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0)) = f := by
      funext u
      rw [hfsum u, Finset.sum_apply]
    rwa [heq] at hsum
  -- lower bound for the integral of the counting function
  have hlower : κ * (S.card : ℝ) ≤ ∫ u in (4 : ℝ)..T, f u := by
    have hsum : (∫ u in (4 : ℝ)..T, f u)
        = ∑ ρ ∈ S, ∫ u in (4 : ℝ)..T, (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0) := by
      rw [intervalIntegral.integral_congr (g := fun u =>
        ∑ ρ ∈ S, (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0)) (fun u _ => hfsum u)]
      exact intervalIntegral.integral_finsetSum
        (fun ρ _ => intervalIntegrable_window_indicator ρ.im κ 4 T)
    rw [hsum]
    have hterm : ∀ ρ ∈ S, κ ≤ ∫ u in (4 : ℝ)..T, (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0) := by
      intro ρ hρ
      obtain ⟨h5, hle⟩ := hSim ρ hρ
      exact le_integral_window_indicator hκ (by linarith) hle
    calc κ * (S.card : ℝ) = ∑ _ρ ∈ S, κ := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ρ ∈ S, ∫ u in (4 : ℝ)..T, (if |ρ.im - u| ≤ κ then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hterm
  -- upper bound for the same integral
  set g : ℝ → ℝ := fun u =>
    (lam / 2 * circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R
      + 1 / (2 * lam) + 2 / y) / L with hg_def
  have hgint : IntervalIntegrable g volume 4 T :=
    (((((intervalIntegrable_circleAverage_normSq_mollifiedZeta_sub_one y hR0 hR52
      (by norm_num) (by linarith)).const_mul (lam / 2)).add
        intervalIntegrable_const).add intervalIntegrable_const).div_const _)
  have hfg : ∀ u ∈ Set.Icc (4 : ℝ) T, f u ≤ g u := by
    intro u hu
    have hjen := card_filter_le_circleAverage_mollified hy4 hκ hr hrR hR52 hlam hgeom S hS hu.1
    rw [hg_def, hf_def, le_div_iff₀ hL]
    exact hjen
  have hgcalc : (∫ u in (4 : ℝ)..T, g u)
      = (lam / 2 * (∫ u in (4 : ℝ)..T, circleAverage
            (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
          + (1 / (2 * lam) + 2 / y) * (T - 4)) / L := by
    rw [hg_def, intervalIntegral.integral_div, intervalIntegral.integral_add
      (((intervalIntegrable_circleAverage_normSq_mollifiedZeta_sub_one y hR0 hR52
        (by norm_num) (by linarith)).const_mul (lam / 2)).add intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_add
      ((intervalIntegrable_circleAverage_normSq_mollifiedZeta_sub_one y hR0 hR52
        (by norm_num) (by linarith)).const_mul (lam / 2)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
    ring
  have hmono := intervalIntegral.integral_mono_on (by linarith : (4 : ℝ) ≤ T) hfint hgint hfg
  rw [hgcalc] at hmono
  have hkey : κ * (S.card : ℝ) * L
      ≤ lam / 2 * (∫ u in (4 : ℝ)..T, circleAverage
          (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
        + (1 / (2 * lam) + 2 / y) * (T - 4) := by
    have h := hlower.trans hmono
    rw [le_div_iff₀ hL] at h
    linarith
  -- the analytic input, with its rate
  have hCAbd := hCA y hy1 4 T le_rfl (by linarith) hTb₀ hyle
  -- the three exponent estimates
  have hyθ : (y : ℝ) ^ (-θ) ≤ T ^ (γ * -θ) := by
    have hbase : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT0 γ
    have h := Real.rpow_le_rpow_of_nonpos hbase hyge (neg_nonpos.mpr hθ0.le)
    rwa [← Real.rpow_mul hT0.le] at h
  have e1 : lam * (T * (y : ℝ) ^ (-θ)) ≤ T ^ (1 - cc) := by
    have hstep : T * (y : ℝ) ^ (-θ) ≤ T * T ^ (γ * -θ) :=
      mul_le_mul_of_nonneg_left hyθ hT0.le
    have hstep2 : lam * (T * (y : ℝ) ^ (-θ)) ≤ lam * (T * T ^ (γ * -θ)) :=
      mul_le_mul_of_nonneg_left hstep hlam.le
    have hcomb : lam * (T * T ^ (γ * -θ)) = T ^ (cc + 1 + γ * -θ) := by
      rw [hlam_def, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_one]
      ring
    have hexp : T ^ (cc + 1 + γ * -θ) ≤ T ^ (1 - cc) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith only [hccmn, hmnγθ])
    linarith
  have e2 : lam * T ^ (1 - c₁) ≤ T ^ (1 - cc) := by
    have hcomb : lam * T ^ (1 - c₁) = T ^ (cc + (1 - c₁)) := by
      rw [hlam_def, Real.rpow_add hT0]
    have hexp : T ^ (cc + (1 - c₁)) ≤ T ^ (1 - cc) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    linarith
  have hlamne : T ^ cc ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hT0 cc)
  have e3 : 1 / (2 * lam) * T = T ^ (1 - cc) / 2 := by
    rw [hlam_def, Real.rpow_sub hT0, Real.rpow_one]
    field_simp
  have e4 : 2 / (y : ℝ) * T ≤ 2 * T ^ (1 - cc) := by
    have hTγpos : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT0 γ
    have hstep : 2 / (y : ℝ) ≤ 2 / T ^ γ :=
      div_le_div_of_nonneg_left (by norm_num) hTγpos hyge
    have hstep2 : 2 / (y : ℝ) * T ≤ 2 / T ^ γ * T := mul_le_mul_of_nonneg_right hstep hT0.le
    have heq : 2 / T ^ γ * T = 2 * T ^ (1 - γ) := by
      rw [Real.rpow_sub hT0, Real.rpow_one]
      field_simp
    have hexp : T ^ (1 - γ) ≤ T ^ (1 - cc) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    linarith
  -- assemble the counting inequality
  have hI0 : (0 : ℝ) ≤ T ^ (1 - cc) := Real.rpow_nonneg hT0.le _
  have hcoef : (0 : ℝ) ≤ 1 / (2 * lam) + 2 / y := by positivity
  have hshrink : (1 / (2 * lam) + 2 / y) * (T - 4) ≤ (1 / (2 * lam) + 2 / y) * T :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef
  have hpart2 : (1 / (2 * lam) + 2 / y) * T ≤ 5 / 2 * T ^ (1 - cc) := by
    have hexpand : (1 / (2 * lam) + 2 / y) * T = 1 / (2 * lam) * T + 2 / (y : ℝ) * T := by ring
    linarith [e3, e4, hexpand]
  have hpart1 : lam / 2 * (∫ u in (4 : ℝ)..T, circleAverage
        (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
      ≤ C₁ * T ^ (1 - cc) := by
    have hstep : lam / 2 * (∫ u in (4 : ℝ)..T, circleAverage
          (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
        ≤ lam / 2 * (C₁ * (T * (y : ℝ) ^ (-θ) + T ^ (1 - c₁))) :=
      mul_le_mul_of_nonneg_left hCAbd (by positivity)
    have hexpand : lam / 2 * (C₁ * (T * (y : ℝ) ^ (-θ) + T ^ (1 - c₁)))
        = C₁ / 2 * (lam * (T * (y : ℝ) ^ (-θ))) + C₁ / 2 * (lam * T ^ (1 - c₁)) := by ring
    have hb1 : C₁ / 2 * (lam * (T * (y : ℝ) ^ (-θ))) ≤ C₁ / 2 * T ^ (1 - cc) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have hb2 : C₁ / 2 * (lam * T ^ (1 - c₁)) ≤ C₁ / 2 * T ^ (1 - cc) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hfinal : κ * (S.card : ℝ) * L ≤ (C₁ + 3) * T ^ (1 - cc) := by
    linarith [hkey, hpart1, hpart2, hshrink]
  -- conclude
  have hcard : (Z.ncard : ℝ) = (S.card : ℝ) := by
    rw [hS_def, Set.ncard_eq_toFinset_card Z hZfin]
  rw [hZ_def] at hcard ⊢
  rw [hcard]
  have hκL : 0 < κ * L := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hκL]
  nlinarith only [hfinal]

/-- **`N(σ, T) = O(T^(1−c))`.**  For every fixed `σ > 1/2` there are `c > 0` and `C` such that
the number of zeroes of `ζ` with real part at least `σ` and ordinate in `(0, T]` is at most
`C T^(1−c)`.  Zeroes are counted without multiplicity. -/
theorem exists_ncard_zerosRightOf_le_rpow {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ (σ - 1 / 2) ^ 2 / 64 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - c) := by
  classical
  obtain ⟨c, C, hc0, hc1, hC0, hcexp, T₀, hT₀5, hbd⟩ :=
    exists_ncard_zerosRightOf_high_le_rpow h0 h1
  have hσ0 : (0 : ℝ) < σ := by linarith
  set M : ℝ := ((nontrivialZeros 5).ncard : ℝ) with hM_def
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  set M₂ : ℝ := ((zerosRightOf σ T₀).ncard : ℝ) with hM₂_def
  have hM₂0 : (0 : ℝ) ≤ M₂ := Nat.cast_nonneg _
  refine ⟨c, C + M + M₂, hc0, hc1, by linarith, hcexp, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hTpow : (1 : ℝ) ≤ T ^ (1 - c) := Real.one_le_rpow hT (by linarith)
  rcases le_or_gt T₀ T with hTT₀ | hTT₀
  · -- the main range: the zeroes of ordinate at least `5`, plus the finitely many others
    set Zhigh : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T}
      with hZhigh
    have hsub : zerosRightOf σ T ⊆ Zhigh ∪ nontrivialZeros 5 := by
      rintro ρ ⟨hz, hre, him0, himT⟩
      rcases le_or_gt 5 ρ.im with h5 | h5
      · exact Or.inl ⟨hz, hre, h5, himT⟩
      · refine Or.inr ⟨hz, lt_of_lt_of_le hσ0 hre, (mem_strip_of_zero_of_im_pos hz him0).2, ?_⟩
        rw [abs_of_pos him0]
        linarith
    have hZhighfin : Zhigh.Finite :=
      (finite_zerosRightOf hσ0 (T := T)).subset (by
        rintro ρ ⟨hz, hre, h5, hle⟩
        exact ⟨hz, hre, by linarith, hle⟩)
    have hfin : (Zhigh ∪ nontrivialZeros 5).Finite := hZhighfin.union (finite_nontrivialZeros 5)
    have hle := Set.ncard_le_ncard hsub hfin
    have hunion : (Zhigh ∪ nontrivialZeros 5).ncard ≤ Zhigh.ncard + (nontrivialZeros 5).ncard :=
      Set.ncard_union_le _ _
    have hcast : ((zerosRightOf σ T).ncard : ℝ) ≤ (Zhigh.ncard : ℝ) + M := by
      rw [hM_def]
      exact_mod_cast hle.trans hunion
    have hhigh := hbd T hTT₀
    rw [hZhigh] at hcast
    nlinarith only [hcast, hhigh, hTpow, hM0, hM₂0, hC0]
  · -- the bounded range: monotonicity in the height
    have hsub : zerosRightOf σ T ⊆ zerosRightOf σ T₀ := by
      rintro ρ ⟨hz, hre, him0, himT⟩
      exact ⟨hz, hre, him0, by linarith⟩
    have hle := Set.ncard_le_ncard hsub (finite_zerosRightOf hσ0)
    have hcast : ((zerosRightOf σ T).ncard : ℝ) ≤ M₂ := by
      rw [hM₂_def]
      exact_mod_cast hle
    nlinarith only [hcast, hTpow, hM0, hM₂0, hC0]

/-- The two-sided form: the number of zeroes at distance at least `δ` from the critical line
and of ordinate in `(0, T]` is `O(T^(1−c))`. -/
theorem exists_ncard_zerosOffCriticalLine_le_rpow {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ C * T ^ (1 - c) := by
  obtain ⟨c, C, hc0, hc1, hC0, _, hbd⟩ :=
    exists_ncard_zerosRightOf_le_rpow (σ := 1 / 2 + δ) (by linarith) (by linarith)
  refine ⟨c, 2 * C, hc0, hc1, by linarith, fun T hT => ?_⟩
  have hle := ncard_zerosOffCriticalLine_le_two_mul hδ0 hδ1 T
  have hcast : ((zerosOffCriticalLine δ T).ncard : ℝ)
      ≤ 2 * ((zerosRightOf (1 / 2 + δ) T).ncard : ℝ) := by exact_mod_cast hle
  have hmain := hbd T hT
  linarith

/-! ## The saving with an explicit exponent

The two statements above produce *some* saving `c > 0`; the two below name it.  Tracking the
constants through the chain — the Montgomery–Vaughan exponent `1 − θ/2`, the Euler–Maclaurin
exponent `≤ 1 − θ`, the mollifier length `b^{θ/8}`, the mean-square saving `3θ/8`, and the
three-way balancing of the counting inequality — gives the saving `(σ − 1/2)²/64`, which is an
explicit function of `σ` and degrades continuously to `0` as `σ ↓ 1/2`. -/

/-- **`N(σ, T) = O(T^(1 − (σ−1/2)²/64))`.**  The density theorem with an explicit saving: for
`1/2 < σ < 1` the number of zeroes of `ζ` with real part at least `σ` and ordinate in `(0, T]`
is at most `C(σ) T^(1 − (σ−1/2)²/64)` for all `T ≥ 1`.  Only the constant `C` is left
implicit; the exponent is an explicit function of `σ`.  Zeroes are counted without
multiplicity. -/
theorem ncard_zerosRightOf_le_rpow_explicit {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - (σ - 1 / 2) ^ 2 / 64) := by
  obtain ⟨c, C, hc0, hc1, hC0, hcexp, hbd⟩ := exists_ncard_zerosRightOf_le_rpow h0 h1
  refine ⟨C, hC0, fun T hT => ?_⟩
  have hmono : T ^ (1 - c) ≤ T ^ (1 - (σ - 1 / 2) ^ 2 / 64) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact (hbd T hT).trans (mul_le_mul_of_nonneg_left hmono hC0.le)

/-- The two-sided form with an explicit exponent: the number of zeroes at distance at least
`δ` from the critical line and of ordinate in `(0, T]` is `O(T^(1 − δ²/64))`. -/
theorem ncard_zerosOffCriticalLine_le_rpow_explicit {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ C * T ^ (1 - δ ^ 2 / 64) := by
  obtain ⟨C, hC0, hbd⟩ :=
    ncard_zerosRightOf_le_rpow_explicit (σ := 1 / 2 + δ) (by linarith) (by linarith)
  refine ⟨2 * C, by linarith, fun T hT => ?_⟩
  have hle := ncard_zerosOffCriticalLine_le_two_mul hδ0 hδ1 T
  have hcast : ((zerosOffCriticalLine δ T).ncard : ℝ)
      ≤ 2 * ((zerosRightOf (1 / 2 + δ) T).ncard : ℝ) := by exact_mod_cast hle
  have hmain := hbd T hT
  have hexp : (1 / 2 + δ - 1 / 2) ^ 2 / 64 = δ ^ 2 / 64 := by ring
  rw [hexp] at hmain
  linarith

end RiemannHypothesis
