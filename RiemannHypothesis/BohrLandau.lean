/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.JensenDiscCount
import RiemannHypothesis.ZetaCircleAverage
import RiemannHypothesis.ZeroCount
import RiemannHypothesis.ZeroCountLocal
import RiemannHypothesis.Zeros
import RiemannHypothesis.Symmetry
import RiemannHypothesis.OffLine
import Zeta23.RvM.Statement

/-!
# The Bohr–Landau zero-density theorem

For every fixed `σ > 1/2` the number `N(σ, T)` of zeroes of `ζ` with real part at least `σ` and
ordinate in `(0, T]` is `O_σ(T)`.  Since the total number of zeroes of ordinate in `(0, T]` is
`≍ T log T`, this says that **almost all zeroes of `ζ` lie within `δ` of the critical line**, for
every fixed `δ > 0`: the proportion of the exceptional ones is `O(1 / log T)`.

Nothing here is conditional.

## The argument

Fix `1/2 < σ < 1` and put `κ = (σ - 1/2)/4`, `r = 3 - σ + κ`, `R = 3 - σ + 2κ`, so that
`0 < r < R < 5/2` and `3 - R = σ - 2κ > 1/2`.

* Every zero `ρ` with `Re ρ ≥ σ` and `|Im ρ - y| ≤ κ` lies in the closed disc of radius `r` about
  `3 + i y`, because `(3 - Re ρ)² + (Im ρ - y)² ≤ (3 - σ)² + κ² ≤ r²`.
* Jensen's counting inequality `card_mul_log_le_circleAverage_sub_log` therefore bounds the number
  of such zeroes by `(circleAverage (log ‖ζ‖) (3 + i y) R + log 2) / log (R / r)`, using
  `‖ζ(3 + i y)‖ ≥ 1/2`.
* Integrating over `y` and using `exists_integral_circleAverage_normSq_riemannZeta_le` (the
  Bohr–Landau mean square) gives `N(σ, T) · κ · log (R/r) = O(T)`.

## Main results

* `exists_ncard_zerosRightOf_le` : `N(σ, T) = O_σ(T)` for `1/2 < σ < 1`.
* `exists_ncard_zerosOffCriticalLine_le` : the same for zeroes at distance `≥ δ` from the
  critical line, on either side.
* `exists_mul_le_windowCount_zero` : the Riemann–von Mangoldt lower bound `N(0,T) ≫ T log T`.
* `tendsto_zerosOffCriticalLine_div_windowCount` : **the proportion of zeroes at distance `≥ δ`
  from the critical line tends to `0`.**
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set
open scoped Topology

namespace RiemannHypothesis

/-! ## The counting sets -/

/-- The zeroes of `ζ` with real part at least `σ` and ordinate in `(0, T]`. -/
def zerosRightOf (σ T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- The zeroes of `ζ` at distance at least `δ` from the critical line, of ordinate in `(0, T]`. -/
def zerosOffCriticalLine (δ T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- A zero of `ζ` of positive ordinate lies in the open critical strip: the trivial zeroes are
real. -/
theorem mem_strip_of_zero_of_im_pos {ρ : ℂ} (hzero : riemannZeta ρ = 0) (him : 0 < ρ.im) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine zero_of_nontrivial_mem_strip hzero ?_
  rintro ⟨n, rfl⟩
  simp at him

/-- The zeroes counted by `zerosRightOf` all lie in the critical strip. -/
theorem zerosRightOf_subset_nontrivialZeros {σ T : ℝ} (hσ : 0 < σ) :
    zerosRightOf σ T ⊆ nontrivialZeros T := by
  rintro ρ ⟨hzero, hre, him0, himT⟩
  exact ⟨hzero, lt_of_lt_of_le hσ hre, (mem_strip_of_zero_of_im_pos hzero him0).2,
    by rw [abs_of_pos him0]; exact himT⟩

theorem finite_zerosRightOf {σ T : ℝ} (hσ : 0 < σ) : (zerosRightOf σ T).Finite :=
  (finite_nontrivialZeros T).subset (zerosRightOf_subset_nontrivialZeros hσ)

/-! ## The core estimate -/

/-- **The core Jensen estimate.**  For `y ≥ 4` the number of zeroes of `ζ` with real part at
least `σ` and ordinate within `κ` of `y` is bounded by the circle average of `‖ζ‖² / 2`. -/
theorem card_filter_le_circleAverage {σ κ r R : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R)
    (hR : R < 5 / 2) (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {y : ℝ} (hy : 4 ≤ y) :
    ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R
        + Real.log 2 := by
  classical
  set c : ℂ := (3 : ℂ) + (y : ℂ) * I with hc
  have hR0 : 0 < R := hr.trans hrR
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = y := by simp [hc]
  have hzc : (1 : ℝ) / 2 ≤ ‖riemannZeta c‖ :=
    half_le_norm_riemannZeta_of_three_le_re (by rw [hcre])
  have hne : riemannZeta c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzc
    linarith
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall c R) :=
    analyticOnNhd_riemannZeta_closedBall hy hR
  have hmem : ∀ ρ ∈ S.filter (fun ρ => |ρ.im - y| ≤ κ), dist ρ c ≤ r ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρS, hρκ⟩ := hρ
    obtain ⟨hz, hre⟩ := hS ρ hρS
    refine ⟨?_, hz⟩
    have hre1 : ρ.re < 1 := by
      by_contra hcon
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hz
    have hdist : dist ρ c ^ 2 = (ρ.re - 3) ^ 2 + (ρ.im - y) ^ 2 := by
      rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity), hcre, hcim]
    have hsq1 : (ρ.re - 3) ^ 2 ≤ (3 - σ) ^ 2 := by nlinarith
    have hsq2 : (ρ.im - y) ^ 2 ≤ κ ^ 2 := by
      have := abs_nonneg (ρ.im - y)
      nlinarith [sq_abs (ρ.im - y)]
    have hle : dist ρ c ^ 2 ≤ r ^ 2 := by rw [hdist]; linarith
    nlinarith [dist_nonneg (x := ρ) (y := c)]
  have hjensen := card_mul_log_le_circleAverage_sub_log hr hrR hana hne hmem
  have hcomp : circleAverage (fun z => Real.log ‖riemannZeta z‖) c R
      ≤ circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) c R :=
    circleAverage_log_norm_riemannZeta_le_circleAverage_normSq hy hR0 hR
  have hlogc : -Real.log ‖riemannZeta c‖ ≤ Real.log 2 := by
    have hmono : Real.log (1 / 2) ≤ Real.log ‖riemannZeta c‖ :=
      Real.log_le_log (by norm_num) hzc
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at hmono
    linarith
  linarith

/-! ## Integrating the Jensen estimate over the ordinate -/

/-- The indicator of a window of half-width `κ` about `c` is interval integrable. -/
theorem intervalIntegrable_window_indicator (c κ a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => if |c - y| ≤ κ then (1 : ℝ) else 0) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le (by fun_prop) measurable_const
  · filter_upwards with x
    split <;> simp

/-- The integral of that indicator over an interval containing `[c - κ, c]` is at least `κ`. -/
theorem le_integral_window_indicator {c κ a b : ℝ} (hκ : 0 < κ) (ha : a ≤ c - κ) (hb : c ≤ b) :
    κ ≤ ∫ y in a..b, (if |c - y| ≤ κ then (1 : ℝ) else 0) := by
  have hsub : (∫ y in (c - κ)..c, (if |c - y| ≤ κ then (1 : ℝ) else 0))
      ≤ ∫ y in a..b, (if |c - y| ≤ κ then (1 : ℝ) else 0) := by
    refine intervalIntegral.integral_mono_interval ha (by linarith) hb ?_
      (intervalIntegrable_window_indicator c κ a b)
    filter_upwards with x
    split <;> simp
  have heq : (∫ y in (c - κ)..c, (if |c - y| ≤ κ then (1 : ℝ) else 0)) = κ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · simp
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have h1 : |c - x| ≤ κ := by
        rw [abs_le]
        constructor <;> [linarith [hx.2]; linarith [hx.1]]
      simp [h1]
  linarith [heq ▸ hsub]

/-- **Bohr–Landau, high zeroes.**  The number of zeroes with real part at least `σ` and ordinate
in `[5, T]` is `O_σ(T)`. -/
theorem exists_ncard_zerosRightOf_high_le {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T}).ncard : ℝ) ≤ C * T := by
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
  obtain ⟨C₁, hC₁, hCA⟩ := exists_integral_circleAverage_normSq_riemannZeta_le hR0 hR52
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(C₁ + Real.log 2) / (κ * Real.log (R / r)), by positivity, fun T hT => ?_⟩
  rcases lt_or_ge T 5 with hT5 | hT5
  · -- no zeroes of ordinate at least `5` below height `T`
    have hempty : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 5 ≤ ρ.im ∧ ρ.im ≤ T} = ∅ := by
      ext ρ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ _ h5 hle
      linarith
    rw [hempty]
    simp only [Set.ncard_empty, Nat.cast_zero]
    positivity
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
  set f : ℝ → ℝ := fun y => ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) with hf_def
  have hfsum : ∀ y : ℝ, f y = ∑ ρ ∈ S, (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0) := by
    intro y
    rw [hf_def]
    simp only [Finset.card_filter, Nat.cast_sum, apply_ite (Nat.cast : ℕ → ℝ), Nat.cast_one,
      Nat.cast_zero]
  have hfint : IntervalIntegrable f volume 4 T := by
    have hsum := IntervalIntegrable.sum S
      (fun ρ (_ : ρ ∈ S) => intervalIntegrable_window_indicator ρ.im κ 4 T)
    have heq : (∑ ρ ∈ S, fun y : ℝ => (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0))
        = f := by
      funext y
      rw [hfsum y, Finset.sum_apply]
    rwa [heq] at hsum
  -- lower bound for the integral of the counting function
  have hlower : κ * (S.card : ℝ) ≤ ∫ y in (4 : ℝ)..T, f y := by
    have hsum : (∫ y in (4 : ℝ)..T, f y)
        = ∑ ρ ∈ S, ∫ y in (4 : ℝ)..T, (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0) := by
      rw [intervalIntegral.integral_congr (g := fun y =>
        ∑ ρ ∈ S, (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0)) (fun y _ => hfsum y)]
      exact intervalIntegral.integral_finsetSum
        (fun ρ _ => intervalIntegrable_window_indicator ρ.im κ 4 T)
    rw [hsum]
    have hterm : ∀ ρ ∈ S,
        κ ≤ ∫ y in (4 : ℝ)..T, (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0) := by
      intro ρ hρ
      obtain ⟨h5, hle⟩ := hSim ρ hρ
      exact le_integral_window_indicator hκ (by linarith) hle
    calc κ * (S.card : ℝ) = ∑ _ρ ∈ S, κ := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ρ ∈ S, ∫ y in (4 : ℝ)..T, (if |ρ.im - y| ≤ κ then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hterm
  -- upper bound for the same integral
  set g : ℝ → ℝ := fun y =>
    (circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R
      + Real.log 2) / Real.log (R / r) with hg_def
  have hgint : IntervalIntegrable g volume 4 T :=
    (((intervalIntegrable_circleAverage_normSq_riemannZeta hR0 hR52 (by norm_num) (by linarith)
      ).add intervalIntegrable_const).div_const _)
  have hfg : ∀ y ∈ Set.Icc (4 : ℝ) T, f y ≤ g y := by
    intro y hy
    have hjen := card_filter_le_circleAverage hκ hr hrR hR52 hgeom S hS hy.1
    rw [hg_def, hf_def, le_div_iff₀ hL]
    exact hjen
  have hupper : (∫ y in (4 : ℝ)..T, f y) ≤ (C₁ * T + Real.log 2 * (T - 4)) / Real.log (R / r) := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : (4 : ℝ) ≤ T) hfint hgint hfg
    have hgcalc : (∫ y in (4 : ℝ)..T, g y)
        = ((∫ y in (4 : ℝ)..T,
            circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
          + Real.log 2 * (T - 4)) / Real.log (R / r) := by
      rw [hg_def, intervalIntegral.integral_div, intervalIntegral.integral_add
        (intervalIntegrable_circleAverage_normSq_riemannZeta hR0 hR52 (by norm_num) (by linarith))
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hCAbd := hCA 4 T (by norm_num) (by linarith)
    have : (∫ y in (4 : ℝ)..T, g y) ≤ (C₁ * T + Real.log 2 * (T - 4)) / Real.log (R / r) := by
      rw [hgcalc]
      gcongr
    linarith
  -- conclude
  have hcard : (Z.ncard : ℝ) = (S.card : ℝ) := by
    rw [hS_def, Set.ncard_eq_toFinset_card Z hZfin]
  rw [hZ_def] at hcard ⊢
  rw [hcard]
  have hkey : κ * (S.card : ℝ) * Real.log (R / r) ≤ C₁ * T + Real.log 2 * (T - 4) := by
    have h := hlower.trans hupper
    rw [le_div_iff₀ hL] at h
    linarith
  have hT0 : (0 : ℝ) < T := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < κ * Real.log (R / r))]
  nlinarith [hkey, hlog2, hT0]

/-- **The Bohr–Landau zero-density theorem.**  For every `σ > 1/2` the number of zeroes of `ζ`
with real part at least `σ` and ordinate in `(0, T]` is `O_σ(T)`. -/
theorem exists_ncard_zerosRightOf_le {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ((zerosRightOf σ T).ncard : ℝ) ≤ C * T := by
  obtain ⟨C, hC, hbd⟩ := exists_ncard_zerosRightOf_high_le h0 h1
  set M : ℕ := (nontrivialZeros 5).ncard with hM
  refine ⟨C + M + 1, by positivity, fun T hT => ?_⟩
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
  have hunion : (Zhigh ∪ nontrivialZeros 5).ncard ≤ Zhigh.ncard + M :=
    Set.ncard_union_le _ _
  have hcast : ((zerosRightOf σ T).ncard : ℝ) ≤ (Zhigh.ncard : ℝ) + (M : ℝ) := by
    have := hle.trans hunion
    exact_mod_cast this
  have hhigh := hbd T hT
  rw [hZhigh] at hcast
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  nlinarith [hcast, hhigh, hT, hM0]

/-! ## The reflected half and the two-sided statement -/

/-- Reflection in the critical line, `ρ ↦ 1 - conj ρ`, is an involution of the zero set of `ζ`
inside the critical strip that preserves ordinates. -/
theorem riemannZeta_one_sub_conj_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 := by
  have hconj : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
    rw [riemannZeta_conj_of_mem_strip h0 h1, hρ, map_zero]
  have hre : ((starRingEnd ℂ) ρ).re = ρ.re := by simp
  exact riemannZeta_one_sub_eq_zero_of_mem_strip (by rw [hre]; exact h0) (by rw [hre]; exact h1)
    hconj

/-- **The two-sided Bohr–Landau bound.** -/
theorem exists_ncard_zerosOffCriticalLine_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ C * T := by
  obtain ⟨C, hC, hbd⟩ :=
    exists_ncard_zerosRightOf_le (σ := 1 / 2 + δ) (by linarith) (by linarith)
  refine ⟨2 * C, by linarith, fun T hT => ?_⟩
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
  have hcast : ((zerosOffCriticalLine δ T).ncard : ℝ) ≤ 2 * (A.ncard : ℝ) := by
    have : (zerosOffCriticalLine δ T).ncard ≤ 2 * A.ncard := by omega
    exact_mod_cast this
  have hA' := hbd T hT
  rw [← hA] at hA'
  linarith

/-! ## Almost all zeroes lie near the critical line -/

/-- Enlarging the window to the left can only increase the zero count. -/
theorem windowCount_mono_left {T₁ T₁' T : ℝ} (h : T₁' ≤ T₁) :
    windowCount T₁ T ≤ windowCount T₁' T := by
  classical
  have hfin := windowZeros_finite T₁ T
  have hfin' := windowZeros_finite T₁' T
  rw [windowCount, windowCount, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin']
  refine Finset.sum_le_sum_of_subset ?_
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact ⟨hρ.1, lt_of_le_of_lt h hρ.2.1, hρ.2.2⟩

/-- The total number of zeroes of ordinate in `(0, T]`, counted with multiplicity, is `≫ T log T`.
This is the Riemann–von Mangoldt lower bound, taken from the dyadic window `(T/2, T]`. -/
theorem exists_mul_le_windowCount_zero :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (windowCount 0 T : ℝ) := by
  obtain ⟨C, T₀, hmain⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set K : ℝ := Real.log (4 * π) - 2 * Real.log 2 + 1 with hK
  refine ⟨1 / (16 * π), by positivity,
    max (max (2 * T₀) (2 : ℝ)) (max (Real.exp (2 * K)) (16 * π * C')), fun T hT => ?_⟩
  have hT1 : 2 * T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : Real.exp (2 * K) ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT4 : 16 * π * C' ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 2 * K ≤ Real.log T := by
    rw [← Real.log_exp (2 * K)]
    exact Real.log_le_log (Real.exp_pos _) hT3
  have hlogT0 : (0 : ℝ) < Real.log T := lt_of_lt_of_le (Real.log_pos (by linarith)) (le_refl _)
  -- the dyadic window `(T/2, T]`
  have hhalf : T₀ ≤ T / 2 := by linarith
  have hmainT := hmain (T / 2) hhalf
  rw [show 2 * (T / 2) = T by ring] at hmainT
  have hell : Zeta23.ell1 (T / 2) = Real.log T - K := by
    rw [Zeta23.ell1, Zeta23.l, hK, show T / 2 / (2 * π) = T / (4 * π) by ring,
      Real.log_div (by linarith) (by positivity)]
    ring
  rw [hell] at hmainT
  have habs := abs_le.mp hmainT
  have hlogT2 : Real.log (T / 2) ≤ Real.log T :=
    Real.log_le_log (by linarith) (by linarith)
  have hN : (Zeta23.zetaZeroConfig.N (T / 2) T : ℝ)
      ≥ T / 2 / (2 * π) * (Real.log T - K) - C' * Real.log T := by
    have h1 := habs.1
    have h2 : C * Real.log (T / 2) ≤ C' * Real.log T := by
      rcases le_or_gt 0 C with hCpos | hCneg
      · calc C * Real.log (T / 2) ≤ C * Real.log T :=
              mul_le_mul_of_nonneg_left hlogT2 hCpos
          _ ≤ C' * Real.log T := mul_le_mul_of_nonneg_right hCC' hlogT0.le
      · have : C * Real.log (T / 2) ≤ 0 := by
          have hlog2pos : 0 ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
          nlinarith
        nlinarith
    linarith
  -- the window count is monotone in the left endpoint
  have hmono : windowCount (T / 2) T ≤ windowCount 0 T := windowCount_mono_left (by linarith)
  have hNeq : (windowCount (T / 2) T : ℝ) = (Zeta23.zetaZeroConfig.N (T / 2) T : ℝ) := by
    rw [windowCount_eq, Zeta23.zetaZeroConfig_N]
  have hmonoR : (windowCount (T / 2) T : ℝ) ≤ (windowCount 0 T : ℝ) := by exact_mod_cast hmono
  -- the arithmetic
  have hfinal : 1 / (16 * π) * (T * Real.log T)
      ≤ T / 2 / (2 * π) * (Real.log T - K) - C' * Real.log T := by
    have hKle : 2 * K ≤ Real.log T := hlogT
    have h1 : C' * Real.log T ≤ T / (16 * π) * Real.log T := by
      have : C' ≤ T / (16 * π) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_right this hlogT0.le
    have h2 : T / 2 / (2 * π) * (Real.log T - K) ≥ T / (4 * π) * (Real.log T / 2) := by
      have hstep : Real.log T - K ≥ Real.log T / 2 := by linarith
      have : T / 2 / (2 * π) = T / (4 * π) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    have h3 : T / (4 * π) * (Real.log T / 2) - T / (16 * π) * Real.log T
        = 1 / (16 * π) * (T * Real.log T) := by
      field_simp
      ring
    linarith
  linarith [hN, hNeq ▸ hmonoR]

/-- **Almost all zeroes of `ζ` lie within `δ` of the critical line.**  The proportion of zeroes of
ordinate in `(0, T]` at distance at least `δ` from the critical line tends to `0`; quantitatively
it is `O_δ(1 / log T)`. -/
theorem tendsto_zerosOffCriticalLine_div_windowCount {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLine δ T).ncard : ℝ) / (windowCount 0 T : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := exists_ncard_zerosOffCriticalLine_le hδ0 hδ1
  obtain ⟨c, hc, T₀, hlow⟩ := exists_mul_le_windowCount_zero
  have hgoal : Tendsto (fun T : ℝ => C / c / Real.log T) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  refine squeeze_zero' ?_ ?_ hgoal
  · filter_upwards with T
    positivity
  · filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 : ℝ)] with T hT hT2
    have hT0 : (0 : ℝ) < T := by linarith
    have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
    have hden : 0 < c * (T * Real.log T) := by positivity
    have hlowT := hlow T hT
    have hnum := hbd T (by linarith)
    have hdenpos : (0 : ℝ) < (windowCount 0 T : ℝ) := lt_of_lt_of_le hden hlowT
    calc ((zerosOffCriticalLine δ T).ncard : ℝ) / (windowCount 0 T : ℝ)
        ≤ (C * T) / (c * (T * Real.log T)) := by
          apply div_le_div₀ (by positivity) hnum hden hlowT
      _ = C / c / Real.log T := by
          field_simp

end RiemannHypothesis
