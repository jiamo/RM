/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MollifiedZetaCircle
import RiemannHypothesis.BohrLandau
import RiemannHypothesis.Partial

/-!
# Carlson's density theorem: `N(σ, T) = o(T)`

The Bohr–Landau theorem of `RiemannHypothesis/BohrLandau.lean` gives `N(σ, T) = O_σ(T)` for
every fixed `σ > 1/2`.  Carlson's theorem improves this to `o(T)`, and that improvement is
what `AlmostAllZerosNearCriticalLine` of `RiemannHypothesis/Partial.lean` asks for: the count
is normalized by `T`, not by the Riemann–von Mangoldt total `N(0, T) ≍ T log T`.

## The argument

The geometry is the one of `RiemannHypothesis/BohrLandau.lean`: for `1/2 < σ < 1` put
`κ = (σ − 1/2)/4`, `r = 3 − σ + κ`, `R = 3 − σ + 2κ`, so a zero with `Re ρ ≥ σ` and
`|Im ρ − u| ≤ κ` lies in the closed disc of radius `r` about `3 + i u`.  What changes is the
function to which Jensen's counting inequality is applied: not `ζ` but `F_y = ζ M_y`.

* Every zero of `ζ` is a zero of `F_y`, so the counting inequality applies verbatim.
* At the centre `− log ‖F_y(3 + i u)‖ ≤ 2/y` is small, whereas for `ζ` it is only `≤ log 2`.
* On the circle `log ‖F_y‖ ≤ (λ/2) ‖F_y − 1‖² + 1/(2λ)`, and the vertical integral of the
  circle averages of `‖F_y − 1‖²` is `≤ ε b` for a mollifier length `y` depending on `ε`.

Integrating over the ordinate of the centre as in Bohr–Landau therefore gives

`κ · N(σ, T) · log (R/r) ≤ (λ ε / 2 + 1/(2λ) + 2/y) T + O(1)`,

and the right-hand side is `≤ η T` for any prescribed `η > 0`: choose `y` large, then `λ`
large, then `ε` small.  Hence `N(σ, T) = o(T)`.

## Main results

* `exists_ncard_zerosRightOf_le_eps` : for every `σ > 1/2` and every `ε > 0`,
  `N(σ, T) ≤ ε T` for all large `T`.
* `tendsto_ncard_zerosRightOf_div_atTop` : `N(σ, T) / T → 0`.
* `tendsto_ncard_zerosOffCriticalLine_div_atTop` : the same for the two-sided count.
* `almostAllZerosNearCriticalLine` : the proposition `AlmostAllZerosNearCriticalLine` of
  `RiemannHypothesis/Partial.lean`, **proved**.

## Scope

Zeroes are counted without multiplicity.  The bound is `o(T)`; the power saving
`N(σ, T) = O(T^(4σ(1−σ)+ε))` of Carlson's quantitative form is *not* claimed, and would need
the mollifier length to grow with `T`.  No zero is located and the Riemann hypothesis is
neither proved nor disproved.
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set
open scoped Topology

namespace RiemannHypothesis

/-- **The core Jensen estimate for the mollified function.**  For `u ≥ 4` the number of zeroes
of `ζ` with real part at least `σ` and ordinate within `κ` of `u` is bounded through the circle
average of `‖F_y − 1‖²`. -/
theorem card_filter_le_circleAverage_mollified {σ κ r R lam : ℝ} {y : ℕ} (hy : 4 ≤ y)
    (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R) (hR : R < 5 / 2) (hlam : 0 < lam)
    (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {u : ℝ} (hu : 4 ≤ u) :
    ((S.filter fun ρ => |ρ.im - u| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ lam / 2 * circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2)
          ((3 : ℂ) + (u : ℂ) * I) R + 1 / (2 * lam) + 2 / y := by
  classical
  set c : ℂ := (3 : ℂ) + (u : ℂ) * I with hc
  have hR0 : 0 < R := hr.trans hrR
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = u := by simp [hc]
  have hne : mollifiedZeta y c ≠ 0 :=
    mollifiedZeta_ne_zero (by omega) (by rw [hcre])
  have hana : AnalyticOnNhd ℂ (mollifiedZeta y) (closedBall c R) :=
    analyticOnNhd_mollifiedZeta_closedBall y hu hR
  have hmem : ∀ ρ ∈ S.filter (fun ρ => |ρ.im - u| ≤ κ),
      dist ρ c ≤ r ∧ mollifiedZeta y ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρS, hρκ⟩ := hρ
    obtain ⟨hz, hre⟩ := hS ρ hρS
    refine ⟨?_, by rw [mollifiedZeta, hz, zero_mul]⟩
    have hre1 : ρ.re < 1 := by
      by_contra hcon
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hz
    have hdist : dist ρ c ^ 2 = (ρ.re - 3) ^ 2 + (ρ.im - u) ^ 2 := by
      rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity), hcre, hcim]
    have hsq1 : (ρ.re - 3) ^ 2 ≤ (3 - σ) ^ 2 := by nlinarith
    have hsq2 : (ρ.im - u) ^ 2 ≤ κ ^ 2 := by
      have := abs_nonneg (ρ.im - u)
      nlinarith [sq_abs (ρ.im - u)]
    have hle : dist ρ c ^ 2 ≤ r ^ 2 := by rw [hdist]; linarith
    nlinarith [dist_nonneg (x := ρ) (y := c)]
  have hjensen := card_mul_log_le_circleAverage_sub_log hr hrR hana hne hmem
  have hcomp := circleAverage_log_norm_mollifiedZeta_le (y := y) hu hR0 hR hlam
  have hcentre : -Real.log ‖mollifiedZeta y c‖ ≤ 2 / y :=
    neg_log_norm_mollifiedZeta_le hy (by rw [hcre])
  linarith

set_option maxHeartbeats 1000000 in
-- the elaboration of this assembly is long; the default limit is not enough here
/-- **Carlson, high zeroes.**  For every `ε > 0` the number of zeroes with real part at least
`σ` and ordinate in `[5, T]` is at most `ε T` for all large `T`. -/
theorem exists_ncard_zerosRightOf_high_le_eps {σ ε : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T}).ncard : ℝ) ≤ ε * T := by
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
  -- the three small quantities
  set eta : ℝ := ε * κ * L / 3 with heta_def
  have heta : 0 < eta := by rw [heta_def]; positivity
  set lam : ℝ := 1 / (2 * eta) with hlam_def
  have hlam : 0 < lam := by rw [hlam_def]; positivity
  have hlaminv : 1 / (2 * lam) = eta := by
    rw [hlam_def]
    field_simp
  set eps₁ : ℝ := 2 * eta / lam with heps₁_def
  have heps₁ : 0 < eps₁ := by rw [heps₁_def]; positivity
  have hlameps : lam / 2 * eps₁ = eta := by
    rw [heps₁_def]
    field_simp
  obtain ⟨y₀, hy₀4, hall⟩ :=
    exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le hR0 hR52 heps₁
  set y : ℕ := max y₀ ⌈2 / eta⌉₊ with hy_def
  have hy4 : 4 ≤ y := le_trans hy₀4 (le_max_left _ _)
  have hyR : (0 : ℝ) < (y : ℝ) := by
    have : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy4
    linarith
  have hyeta : 2 / (y : ℝ) ≤ eta := by
    have hceil : (2 / eta : ℝ) ≤ (⌈2 / eta⌉₊ : ℝ) := Nat.le_ceil _
    have hle : ((⌈2 / eta⌉₊ : ℕ) : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast Nat.cast_le.mpr (le_max_right y₀ _)
    have h2 : (2 / eta : ℝ) ≤ (y : ℝ) := le_trans hceil hle
    rw [div_le_iff₀ hyR]
    rw [div_le_iff₀ heta] at h2
    linarith
  obtain ⟨b₀, hb₀, hCA⟩ := hall y (le_max_left _ _)
  refine ⟨max (max b₀ 5) 1, le_max_right _ _, fun T hT => ?_⟩
  have hT5 : (5 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTb₀ : b₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
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
  have hupper : (∫ u in (4 : ℝ)..T, f u)
      ≤ (lam / 2 * (eps₁ * T) + (1 / (2 * lam) + 2 / y) * (T - 4)) / L := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : (4 : ℝ) ≤ T) hfint hgint hfg
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
    have hCAbd := hCA 4 T (by norm_num) (by linarith) hTb₀
    have hstep : (∫ u in (4 : ℝ)..T, g u)
        ≤ (lam / 2 * (eps₁ * T) + (1 / (2 * lam) + 2 / y) * (T - 4)) / L := by
      rw [hgcalc]
      gcongr
    linarith
  -- conclude
  have hcard : (Z.ncard : ℝ) = (S.card : ℝ) := by
    rw [hS_def, Set.ncard_eq_toFinset_card Z hZfin]
  rw [hZ_def] at hcard ⊢
  rw [hcard]
  have hkey : κ * (S.card : ℝ) * L
      ≤ lam / 2 * (eps₁ * T) + (1 / (2 * lam) + 2 / y) * (T - 4) := by
    have h := hlower.trans hupper
    rw [le_div_iff₀ hL] at h
    linarith
  have hbound : lam / 2 * (eps₁ * T) + (1 / (2 * lam) + 2 / y) * (T - 4) ≤ 3 * eta * T := by
    have h1 : lam / 2 * (eps₁ * T) = eta * T := by
      rw [← hlameps]; ring
    have h2 : (1 / (2 * lam) + 2 / y) ≤ 2 * eta := by
      rw [hlaminv]; linarith
    have h3 : (0 : ℝ) ≤ T - 4 := by linarith
    nlinarith [h1, h2, h3, heta.le]
  have hfinal : κ * (S.card : ℝ) * L ≤ 3 * eta * T := le_trans hkey hbound
  have heta' : 3 * eta = ε * κ * L := by rw [heta_def]; ring
  rw [heta'] at hfinal
  have hκL : 0 < κ * L := by positivity
  nlinarith [hfinal, hκL]

/-- **Carlson's density theorem, `o(T)` form.**  For every `σ > 1/2` and every `ε > 0` the
number of zeroes of `ζ` with real part at least `σ` and ordinate in `(0, T]` is at most `ε T`
for all large `T`. -/
theorem exists_ncard_zerosRightOf_le_eps {σ ε : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ((zerosRightOf σ T).ncard : ℝ) ≤ ε * T := by
  obtain ⟨T₁, hT₁, hbd⟩ := exists_ncard_zerosRightOf_high_le_eps h0 h1 (half_pos hε)
  set M : ℕ := (nontrivialZeros 5).ncard with hM
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  refine ⟨max T₁ (max (2 * M / ε) 1), le_trans (le_max_right _ _) (le_max_right _ _),
    fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTM : 2 * M / ε ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  set Zhigh : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T} with hZhigh
  have hσ0 : (0 : ℝ) < σ := by linarith
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
  have hunion : (Zhigh ∪ nontrivialZeros 5).ncard ≤ Zhigh.ncard + M := Set.ncard_union_le _ _
  have hcast : ((zerosRightOf σ T).ncard : ℝ) ≤ (Zhigh.ncard : ℝ) + (M : ℝ) := by
    have := hle.trans hunion
    exact_mod_cast this
  have hhigh := hbd T hTT₁
  rw [hZhigh] at hcast
  have hMle : (M : ℝ) ≤ ε / 2 * T := by
    rw [div_le_iff₀ hε] at hTM
    linarith
  linarith

/-- `N(σ, T) / T → 0` for every fixed `σ > 1/2`. -/
theorem tendsto_ncard_zerosRightOf_div_atTop {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Tendsto (fun T : ℝ => ((zerosRightOf σ T).ncard : ℝ) / T) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀, hbd⟩ := exists_ncard_zerosRightOf_le_eps h0 h1 (half_pos hε)
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have h := hbd T (le_trans (le_max_left _ _) hT)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hT0]
  nlinarith [h, mul_pos hε hT0]

/-- The two-sided form: the number of zeroes at distance at least `δ` from the critical line
and of ordinate in `(0, T]` is `o(T)`. -/
theorem ncard_zerosOffCriticalLine_le_two_mul {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (T : ℝ) :
    (zerosOffCriticalLine δ T).ncard ≤ 2 * (zerosRightOf (1 / 2 + δ) T).ncard := by
  classical
  set A : Set ℂ := zerosRightOf (1 / 2 + δ) T with hA
  have hAfin : A.Finite := finite_zerosRightOf (by linarith)
  set refl : ℂ → ℂ := fun ρ => 1 - (starRingEnd ℂ) ρ with hrefl
  have hsub : zerosOffCriticalLine δ T ⊆ A ∪ refl '' A := by
    rintro ρ ⟨hz, hδρ, him0, himT⟩
    obtain ⟨hre0, hre1⟩ := mem_strip_of_zero_of_im_pos hz him0
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hhalf | hhalf
    · refine Or.inl ⟨hz, ?_, him0, himT⟩
      rw [abs_of_nonneg (by linarith)] at hδρ
      linarith
    · rw [abs_of_neg (by linarith)] at hδρ
      refine Or.inr ⟨refl ρ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · exact riemannZeta_one_sub_conj_eq_zero hre0 hre1 hz
      · rw [hrefl]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [hrefl]
        simpa using him0
      · rw [hrefl]
        simpa using himT
      · rw [hrefl]
        simp
  have hfin : (A ∪ refl '' A).Finite := hAfin.union (hAfin.image _)
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 : (A ∪ refl '' A).ncard ≤ A.ncard + (refl '' A).ncard := Set.ncard_union_le _ _
  have h3 : (refl '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  omega

/-- The two-sided form: the number of zeroes at distance at least `δ` from the critical line
and of ordinate in `(0, T]` is `o(T)`. -/
theorem tendsto_ncard_zerosOffCriticalLine_div_atTop {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLine δ T).ncard : ℝ) / T) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀, hbd⟩ := exists_ncard_zerosRightOf_le_eps (σ := 1 / 2 + δ) (by linarith)
    (by linarith) (show (0 : ℝ) < ε / 4 by linarith)
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have h := hbd T (le_trans (le_max_left _ _) hT)
  have hcast : ((zerosOffCriticalLine δ T).ncard : ℝ)
      ≤ 2 * ((zerosRightOf (1 / 2 + δ) T).ncard : ℝ) := by
    exact_mod_cast ncard_zerosOffCriticalLine_le_two_mul hδ0 hδ1 T
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hT0]
  nlinarith [h, hcast, mul_pos hε hT0]

/-- **Almost all zeroes lie within `δ` of the critical line, in the `o(T)` sense.**  This is
the proposition `AlmostAllZerosNearCriticalLine` of `RiemannHypothesis/Partial.lean`. -/
theorem almostAllZerosNearCriticalLine : AlmostAllZerosNearCriticalLine := by
  intro δ hδ
  rcases lt_or_ge δ (1 / 2 : ℝ) with hδ1 | hδ1
  · have hmain := tendsto_ncard_zerosOffCriticalLine_div_atTop hδ hδ1
    refine squeeze_zero' ?_ ?_ hmain
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hsub : {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧ δ ≤ |s.re - 1 / 2|}
          ⊆ zerosOffCriticalLine δ T := by
        rintro s ⟨hz, him0, himT, hδs⟩
        exact ⟨hz, hδs, him0, le_of_lt himT⟩
      have hfin : (zerosOffCriticalLine δ T).Finite := by
        refine (finite_nontrivialZeros T).subset ?_
        rintro s ⟨hz, hδs, him0, himT⟩
        obtain ⟨hre0, hre1⟩ := mem_strip_of_zero_of_im_pos hz him0
        exact ⟨hz, hre0, hre1, by rw [abs_of_pos him0]; exact himT⟩
      have hcard : Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
          δ ≤ |s.re - 1 / 2|} ≤ (zerosOffCriticalLine δ T).ncard :=
        Set.ncard_le_ncard hsub hfin
      have hcast : (Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
          δ ≤ |s.re - 1 / 2|} : ℝ) ≤ ((zerosOffCriticalLine δ T).ncard : ℝ) := by
        exact_mod_cast hcard
      gcongr
  · -- for `δ ≥ 1/2` the set is empty: a zero of positive ordinate lies in the open strip
    have hempty : ∀ T : ℝ, {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
        δ ≤ |s.re - 1 / 2|} = ∅ := by
      intro T
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz him0 _
      obtain ⟨hre0, hre1⟩ := mem_strip_of_zero_of_im_pos hz him0
      have : |s.re - 1 / 2| < 1 / 2 := by
        rw [abs_lt]
        constructor <;> linarith
      linarith
    have : (fun T : ℝ => (Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
        δ ≤ |s.re - 1 / 2|} : ℝ) / T) = fun _ : ℝ => (0 : ℝ) := by
      funext T
      rw [hempty T]
      simp
    rw [this]
    exact tendsto_const_nhds

end RiemannHypothesis
