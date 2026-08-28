/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BohrLandau

/-!
# Backlund's density criterion: the Lindelöf hypothesis gives `o(log T)` zeroes in a unit window

The Lindelöf hypothesis is the statement that `ζ(σ + i t) = O(t^ε)` for every `ε > 0`, uniformly
for `σ ≥ 1/2`.  Backlund proved that it is *equivalent* to a statement about the zeroes: for every
fixed `σ > 1/2` the number of zeroes of `ζ` with real part at least `σ` and ordinate in a window
`(T, T+1]` of unit height is `o(log T)`.  Unconditionally that number is `O(log T)` — this is the
local Riemann–von Mangoldt bound of `RiemannHypothesis.ZeroCountLocal` — so the content of the
criterion is the saving of the whole logarithm.

This file proves the direction

  **Lindelöf hypothesis ⟹ for every fixed `σ > 1/2`, `N(σ, T+1) − N(σ, T) = o(log T)`.**

## The argument

It is the Jensen-disc argument of `RiemannHypothesis.BohrLandau`, with the mean square of `ζ`
replaced by the pointwise Lindelöf bound.  Fix `1/2 < σ < 1` and put, exactly as there,
`κ = (σ − 1/2)/4`, `r = 3 − σ + κ`, `R = 3 − σ + 2κ`, so that `0 < r < R < 5/2` and
`3 − R = σ/2 + 1/4 > 1/2`: the closed disc of radius `R` about `3 + i y` stays inside the
half-plane `re s > 1/2` where the Lindelöf bound applies, while the concentric disc of radius `r`
already contains every zero with `re ≥ σ` and ordinate within `κ` of `y`.

Jensen's counting inequality (`RiemannHypothesis.card_mul_log_le_circleAverage_sub_log`) bounds the
number of those zeroes by `(log M + log 2)/log (R/r)`, where `M` is the maximum of `‖ζ‖` on the
circle of radius `R`; under the Lindelöf hypothesis `M ≤ C (y+3)^ε`, so each disc carries at most
`(log C + log 2 + ε log (y+3))/log (R/r)` zeroes.  A window of unit height is covered by
`⌈1/(2κ)⌉` such discs, a number depending only on `σ`, and `ε > 0` is arbitrary, so the count is
`o(log T)`.

## Main results

* `LindelofHypothesis` — the Lindelöf hypothesis, as a `Prop`.
* `zerosRightOfWindow` — the zeroes of `ζ` with real part at least `σ` and ordinate in `(T₁, T₂]`.
* `card_filter_le_log_max` — the Jensen estimate for one disc, against the *maximum* of `‖ζ‖` on
  the circle (unconditional).
* `exists_ncard_zerosRightOfWindow_le` — under the Lindelöf hypothesis, for every `ε > 0` there is
  `A` with `N(σ, T+1) − N(σ, T) ≤ A + ε log T` for all `T ≥ 5`.
* `tendsto_ncard_zerosRightOfWindow_div_log` — hence `(N(σ, T+1) − N(σ, T))/log T → 0`.
* `zerosOffCriticalLineWindow`, `tendsto_ncard_zerosOffCriticalLineWindow_div_log` — the two-sided
  form, obtained from the one-sided one by the reflection `ρ ↦ 1 − conj ρ`.
* `exists_ncard_zerosRightOfWindow_le_log` — the unconditional comparison `O(log T)`.

## Scope

Only one direction of Backlund's equivalence is proved.  The converse — that `o(log T)` zeroes per
unit window implies the Lindelöf hypothesis — needs Littlewood's lemma together with the
Borel–Carathéodory estimate for `log ζ`, and is not formalized here.  Nothing in this file is
unconditional beyond the one-disc estimate `card_filter_le_log_max` and the `O(log T)` comparison
`exists_ncard_zerosRightOfWindow_le_log`, and nothing here bears on the
Riemann hypothesis itself: the Lindelöf hypothesis is a consequence of the Riemann hypothesis and
is itself open.

## Hypothesis hygiene (AGENTS.md)

`LindelofHypothesis` is *assumed*, never proved, in this file, and every theorem that uses it says
so in its name or its statement.

1. **Direction.**  What is free unconditionally is the *upper* bound `N(σ,T+1) − N(σ,T) = O(log T)`
   (`RiemannHypothesis.ZeroCountLocal`); the hypothesis buys the factor `o(1)`.  The implication
   proved here runs from the analytic hypothesis to the zero count, which is the direction in which
   the hypothesis is a genuine input.
2. **Strength.**  The Lindelöf hypothesis is strictly weaker than the Riemann hypothesis (RH ⟹ LH
   classically, and LH is not known to imply RH), and it does not imply the conclusion trivially:
   the conclusion is a statement about zeroes, the hypothesis a statement about growth.
3. **Non-triviality.**  No proof of `LindelofHypothesis` is available here, from RH or otherwise;
   it is recorded as an open hypothesis, and the theorems below are explicitly conditional.
4. **Attribution.**  The equivalence is Backlund's (1918); what is formalized is the easier of its
   two implications, by the Jensen-disc argument.
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set
open scoped Topology

namespace RiemannHypothesis

/-! ## The hypothesis and the counting set -/

/-- **The Lindelöf hypothesis**: for every `ε > 0` there is a constant `C` with
`‖ζ(s)‖ ≤ C (im s)^ε` for every `s` with `re s ≥ 1/2` and `im s ≥ 2`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε

/-- The zeroes of `ζ` with real part at least `σ` and ordinate in the window `(T₁, T₂]`. -/
def zerosRightOfWindow (σ T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

theorem zerosRightOfWindow_subset_zerosRightOf {σ T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    zerosRightOfWindow σ T₁ T₂ ⊆ zerosRightOf σ T₂ := by
  rintro ρ ⟨hz, hre, hlt, hle⟩
  exact ⟨hz, hre, lt_of_le_of_lt hT₁ hlt, hle⟩

theorem finite_zerosRightOfWindow {σ T₁ T₂ : ℝ} (hσ : 0 < σ) (hT₁ : 0 ≤ T₁) :
    (zerosRightOfWindow σ T₁ T₂).Finite :=
  (finite_zerosRightOf hσ).subset (zerosRightOfWindow_subset_zerosRightOf hT₁)

/-! ## The one-disc estimate, against the maximum of `‖ζ‖` -/

/-- **Jensen's estimate for one disc, against the maximum.**  For `y ≥ 4` and `M` an upper bound
for `‖ζ‖` on the circle of radius `R` about `3 + i y`, the number of zeroes of `ζ` with real part
at least `σ` and ordinate within `κ` of `y` is at most `(log M + log 2)/log (R/r)`.

This statement is unconditional; the Lindelöf hypothesis enters only through `M`. -/
theorem card_filter_le_log_max {σ κ r R M : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R)
    (hR : R < 5 / 2) (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2) (hM : 1 ≤ M)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {y : ℝ} (hy : 4 ≤ y)
    (hbd : ∀ z ∈ Metric.sphere ((3 : ℂ) + (y : ℂ) * I) R, ‖riemannZeta z‖ ≤ M) :
    ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ Real.log M + Real.log 2 := by
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
  have hcomp : circleAverage (fun z => Real.log ‖riemannZeta z‖) c R ≤ Real.log M := by
    have hint : CircleIntegrable (fun z => Real.log ‖riemannZeta z‖) c R := by
      refine MeromorphicOn.circleIntegrable_log_norm ?_
      have habs : |R| = R := abs_of_pos hR0
      rw [habs]
      exact (hana.mono (sphere_subset_closedBall)).meromorphicOn
    refine circleAverage_mono_on_of_le_circle hint ?_
    intro z hz
    rw [abs_of_pos hR0] at hz
    rcases eq_or_lt_of_le (norm_nonneg (riemannZeta z)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hM
    · exact Real.log_le_log h0 (hbd z hz)
  have hlogc : -Real.log ‖riemannZeta c‖ ≤ Real.log 2 := by
    have hmono : Real.log (1 / 2) ≤ Real.log ‖riemannZeta c‖ :=
      Real.log_le_log (by norm_num) hzc
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at hmono
    linarith
  linarith

/-! ## The Lindelöf bound on a Jensen circle -/

/-- Under the Lindelöf hypothesis with parameter `ε` and constant `C`, every point of the circle
of radius `R < 5/2` about `3 + i y` with `y ≥ 5` satisfies `‖ζ‖ ≤ C (y+3)^ε`, provided the circle
stays in `re ≥ 1/2`. -/
theorem norm_riemannZeta_le_on_sphere_of_lindelof {ε C R y : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hLH : ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε)
    (hR : R ≤ 5 / 2) (hy : 5 ≤ y) :
    ∀ z ∈ Metric.sphere ((3 : ℂ) + (y : ℂ) * I) R, ‖riemannZeta z‖ ≤ C * (y + 3) ^ ε := by
  intro z hz
  set c : ℂ := (3 : ℂ) + (y : ℂ) * I with hc
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = y := by simp [hc]
  have hdist : dist z c = R := hz
  have hre : |z.re - 3| ≤ R := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [← Complex.dist_eq, hdist] at h
    simpa [hcre] using h
  have him : |z.im - y| ≤ R := by
    have h := Complex.abs_im_le_norm (z - c)
    rw [← Complex.dist_eq, hdist] at h
    simpa [hcim] using h
  have hre' : (1 : ℝ) / 2 ≤ z.re := by
    have h := abs_le.mp hre
    linarith [h.1]
  have him2 : (2 : ℝ) ≤ z.im := by
    have h := abs_le.mp him
    linarith [h.1]
  have himle : z.im ≤ y + 3 := by
    have h := abs_le.mp him
    linarith [h.2]
  refine (hLH z hre' him2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  exact Real.rpow_le_rpow (by linarith) himle hε.le

/-- The one-disc estimate under the Lindelöf hypothesis: at most
`(log C + ε log (y+3) + log 2)/log (R/r)` zeroes with real part at least `σ` have ordinate within
`κ` of `y`. -/
theorem card_filter_le_of_lindelof {σ κ r R ε C : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R)
    (hR : R < 5 / 2) (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2) (hε : 0 < ε) (hC : 1 ≤ C)
    (hbdd : ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {y : ℝ} (hy : 5 ≤ y) :
    ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ Real.log C + ε * Real.log (y + 3) + Real.log 2 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hy3 : (1 : ℝ) ≤ y + 3 := by linarith
  have hrpow : (1 : ℝ) ≤ (y + 3) ^ ε := Real.one_le_rpow hy3 hε.le
  have hM : (1 : ℝ) ≤ C * (y + 3) ^ ε := by nlinarith
  have hbd := norm_riemannZeta_le_on_sphere_of_lindelof hε hC0 hbdd (le_of_lt hR) hy
  have hkey := card_filter_le_log_max hκ hr hrR hR hgeom hM S hS (by linarith : (4 : ℝ) ≤ y) hbd
  have hlog : Real.log (C * (y + 3) ^ ε) = Real.log C + ε * Real.log (y + 3) := by
    rw [Real.log_mul (ne_of_gt hC0) (by positivity), Real.log_rpow (by linarith)]
  rw [hlog] at hkey
  exact hkey

/-! ## Covering a unit window by discs -/

/-- A window of unit height is covered by `m` discs of half-height `κ` whenever `1/(2κ) ≤ m`. -/
theorem card_le_sum_card_filter {S : Finset ℂ} {T κ : ℝ} (hκ : 0 < κ) {m : ℕ}
    (hm : 1 / (2 * κ) ≤ (m : ℝ)) (hS : ∀ ρ ∈ S, T < ρ.im ∧ ρ.im ≤ T + 1) :
    S.card ≤ ∑ j ∈ Finset.range m,
      (S.filter fun ρ => |ρ.im - (T + κ * (2 * j + 1))| ≤ κ).card := by
  classical
  set t : ℕ → Finset ℂ := fun j => S.filter fun ρ => |ρ.im - (T + κ * (2 * j + 1))| ≤ κ with ht
  have hsub : S ⊆ (Finset.range m).biUnion t := ?_
  · exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  intro ρ hρ
  obtain ⟨hlt, hle⟩ := hS ρ hρ
  set x : ℝ := (ρ.im - T) / (2 * κ) with hx
  have h2κ : (0 : ℝ) < 2 * κ := by linarith
  have hx0 : 0 < x := div_pos (by linarith) h2κ
  have hxm : x ≤ (m : ℝ) := by
    have h1 : ρ.im - T ≤ 1 := by linarith
    have : x ≤ 1 / (2 * κ) := by
      rw [hx, div_le_div_iff_of_pos_right h2κ]
      linarith
    linarith
  set n : ℕ := ⌈x⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_ceil_iff.mpr hx0
  have hnm : n ≤ m := Nat.ceil_le.mpr hxm
  refine Finset.mem_biUnion.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), ?_⟩
  rw [ht]
  refine Finset.mem_filter.mpr ⟨hρ, ?_⟩
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn1
    push_cast [Nat.cast_sub this]
    ring
  have hxle : x ≤ (n : ℝ) := Nat.le_ceil x
  have hltx : (n : ℝ) - 1 < x := by
    have := Nat.ceil_lt_add_one (le_of_lt hx0)
    rw [← hn] at this
    linarith
  have hupper : ρ.im - T ≤ 2 * κ * (n : ℝ) := by
    have := (div_le_iff₀ h2κ).mp hxle
    linarith [this]
  have hlower : 2 * κ * ((n : ℝ) - 1) < ρ.im - T := by
    have := (lt_div_iff₀ h2κ).mp hltx
    linarith [this]
  rw [abs_le, hcast]
  constructor <;> nlinarith

/-- The quantitative form: under the Lindelöf hypothesis, for every `ε > 0` there is a constant
`A` with `N(σ, T+1) − N(σ, T) ≤ A + ε log T` for `T ≥ 5`. -/
theorem exists_ncard_zerosRightOfWindow_le (hLH : LindelofHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 5 ≤ T →
      ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ A + ε * Real.log T := by
  classical
  set κ : ℝ := (σ - 1 / 2) / 4 with hκ_def
  set r : ℝ := 3 - σ + κ with hr_def
  set R : ℝ := 3 - σ + 2 * κ with hR_def
  have hκ : 0 < κ := by rw [hκ_def]; linarith
  have hκ8 : κ ≤ 1 / 8 := by rw [hκ_def]; linarith
  have hr : 0 < r := by rw [hr_def]; linarith
  have hrR : r < R := by rw [hr_def, hR_def]; linarith
  have hR52 : R < 5 / 2 := by rw [hR_def, hκ_def]; linarith
  have hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2 := by rw [hr_def]; nlinarith
  set L : ℝ := Real.log (R / r) with hL_def
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hrR)
  set m : ℕ := ⌈1 / (2 * κ)⌉₊ with hm_def
  have hm : 1 / (2 * κ) ≤ (m : ℝ) := Nat.le_ceil _
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hm
  have hmlt : (m : ℝ) < 1 / (2 * κ) + 1 := Nat.ceil_lt_add_one (by positivity)
  set ε' : ℝ := ε * L / (2 * m) with hε'_def
  have hε' : 0 < ε' := by rw [hε'_def]; positivity
  obtain ⟨C, hC0, hCbd⟩ := hLH ε' hε'
  set C' : ℝ := max C 1 with hC'_def
  have hC' : 1 ≤ C' := le_max_right _ _
  have hlogC' : 0 ≤ Real.log C' := Real.log_nonneg hC'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC'bd : ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C' * s.im ^ ε' := by
    intro s h1 h2
    refine (hCbd s h1 h2).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _)
  -- the constant
  have hAnn : 0 ≤ (m : ℝ) * (Real.log C' + Real.log 2 + ε' * Real.log 2) / L := by positivity
  refine ⟨(m : ℝ) * (Real.log C' + Real.log 2 + ε' * Real.log 2) / L + 1, by linarith, ?_⟩
  intro T hT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  -- the zeroes of the window, as a finset
  have hZfin : (zerosRightOfWindow σ T (T + 1)).Finite :=
    finite_zerosRightOfWindow (by linarith) (by linarith)
  set S : Finset ℂ := hZfin.toFinset with hS_def
  have hSmem : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re := by
    intro ρ hρ
    rw [hS_def, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1, hρ.2.1⟩
  have hSim : ∀ ρ ∈ S, T < ρ.im ∧ ρ.im ≤ T + 1 := by
    intro ρ hρ
    rw [hS_def, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.2.2.1, hρ.2.2.2⟩
  have hcover := card_le_sum_card_filter (S := S) (T := T) (κ := κ) hκ hm hSim
  -- each disc carries few zeroes
  have hdisc : ∀ j ∈ Finset.range m,
      ((S.filter fun ρ => |ρ.im - (T + κ * (2 * j + 1))| ≤ κ).card : ℝ)
        ≤ (Real.log C' + Real.log 2 + ε' * (Real.log 2 + Real.log T)) / L := by
    intro j hj
    rw [Finset.mem_range] at hj
    set y : ℝ := T + κ * (2 * j + 1) with hy_def
    have hy5 : 5 ≤ y := by
      have : 0 ≤ κ * (2 * (j : ℝ) + 1) := by positivity
      rw [hy_def]; linarith
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hj
    have hyle : y + 3 ≤ 2 * T := by
      have h1 : κ * (2 * (j : ℝ) + 1) ≤ 2 * κ * (m : ℝ) := by nlinarith
      have h2 : 2 * κ * (m : ℝ) ≤ 1 + 2 * κ := by
        have := hmlt
        have h2κ : (0 : ℝ) < 2 * κ := by linarith
        have : 2 * κ * (m : ℝ) < 2 * κ * (1 / (2 * κ) + 1) := by
          exact (mul_lt_mul_iff_of_pos_left h2κ).mpr hmlt
        rw [mul_add, mul_one_div, div_self (ne_of_gt h2κ)] at this
        linarith
      rw [hy_def]
      linarith
    have hkey := card_filter_le_of_lindelof hκ hr hrR hR52 hgeom hε' hC' hC'bd S hSmem hy5
    have hlogy : Real.log (y + 3) ≤ Real.log 2 + Real.log T := by
      have h1 : Real.log (y + 3) ≤ Real.log (2 * T) :=
        Real.log_le_log (by linarith) hyle
      rwa [Real.log_mul two_ne_zero (by linarith : (T : ℝ) ≠ 0)] at h1
    have hmono : ε' * Real.log (y + 3) ≤ ε' * (Real.log 2 + Real.log T) :=
      mul_le_mul_of_nonneg_left hlogy hε'.le
    rw [le_div_iff₀ hL]
    linarith
  -- summing over the discs
  have hsum : (S.card : ℝ)
      ≤ (m : ℝ) * ((Real.log C' + Real.log 2 + ε' * (Real.log 2 + Real.log T)) / L) := by
    have hcast : (S.card : ℝ) ≤ ((∑ j ∈ Finset.range m,
        (S.filter fun ρ => |ρ.im - (T + κ * (2 * j + 1))| ≤ κ).card : ℕ) : ℝ) := by
      exact_mod_cast hcover
    refine hcast.trans ?_
    push_cast
    calc (∑ j ∈ Finset.range m,
            ((S.filter fun ρ => |ρ.im - (T + κ * (2 * j + 1))| ≤ κ).card : ℝ))
        ≤ ∑ _j ∈ Finset.range m,
            (Real.log C' + Real.log 2 + ε' * (Real.log 2 + Real.log T)) / L :=
          Finset.sum_le_sum hdisc
      _ = (m : ℝ) * ((Real.log C' + Real.log 2 + ε' * (Real.log 2 + Real.log T)) / L) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- and rewriting the main term
  have hmain : (m : ℝ) * (ε' * Real.log T / L) = ε / 2 * Real.log T := by
    rw [hε'_def]
    field_simp
  have hncard : ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) = (S.card : ℝ) := by
    rw [hS_def, Set.ncard_eq_toFinset_card _ hZfin]
  rw [hncard]
  have hexpand : (m : ℝ) * ((Real.log C' + Real.log 2 + ε' * (Real.log 2 + Real.log T)) / L)
      = (m : ℝ) * (Real.log C' + Real.log 2 + ε' * Real.log 2) / L
        + (m : ℝ) * (ε' * Real.log T / L) := by
    field_simp
    ring
  rw [hexpand, hmain] at hsum
  have : ε / 2 * Real.log T ≤ ε * Real.log T := by nlinarith
  linarith

/-- **Backlund's criterion, the easy direction.**  Under the Lindelöf hypothesis, for every fixed
`σ > 1/2` the number of zeroes of `ζ` with real part at least `σ` and ordinate in a window of unit
height at height `T` is `o(log T)`. -/
theorem tendsto_ncard_zerosRightOfWindow_div_log (hLH : LindelofHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T : ℝ => ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) / Real.log T)
      atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr ?_
  intro δ hδ
  obtain ⟨A, hA, hbound⟩ := exists_ncard_zerosRightOfWindow_le hLH hσ hσ1 (half_pos hδ)
  filter_upwards [eventually_ge_atTop (5 : ℝ),
    eventually_gt_atTop (Real.exp (2 * A / δ))] with T hT5 hTexp
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT5
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT' : 2 * A / δ < Real.log T := by
    have h := Real.log_lt_log (Real.exp_pos (2 * A / δ)) hTexp
    rwa [Real.log_exp] at h
  have hAlt : A < δ / 2 * Real.log T := by
    have h := (div_lt_iff₀ hδ).mp hlogT'
    nlinarith
  have h1 : ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ A + δ / 2 * Real.log T :=
    hbound T hT5
  have hnonneg : (0 : ℝ) ≤ ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnonneg hlogT.le), div_lt_iff₀ hlogT]
  nlinarith

/-! ## The two-sided form -/

/-- The zeroes of `ζ` at distance at least `δ` from the critical line, on either side, with
ordinate in the window `(T₁, T₂]`. -/
def zerosOffCriticalLineWindow (δ T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- Reflection in the critical line halves the two-sided count: a zero of the window at distance
at least `δ` from the critical line is either in `zerosRightOfWindow (1/2 + δ)` or the reflection
of one. -/
theorem ncard_zerosOffCriticalLineWindow_le {δ T : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hT : 0 ≤ T) :
    (zerosOffCriticalLineWindow δ T (T + 1)).ncard
      ≤ 2 * (zerosRightOfWindow (1 / 2 + δ) T (T + 1)).ncard := by
  classical
  set A : Set ℂ := zerosRightOfWindow (1 / 2 + δ) T (T + 1) with hA
  have hAfin : A.Finite := finite_zerosRightOfWindow (by linarith) hT
  set refl : ℂ → ℂ := fun ρ => 1 - (starRingEnd ℂ) ρ with hrefl
  have hsub : zerosOffCriticalLineWindow δ T (T + 1) ⊆ A ∪ refl '' A := by
    rintro ρ ⟨hz, hδρ, him0, himT⟩
    have himpos : 0 < ρ.im := lt_of_le_of_lt hT him0
    obtain ⟨hre0, hre1⟩ := mem_strip_of_zero_of_im_pos hz himpos
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

/-- **The two-sided form of Backlund's criterion.**  Under the Lindelöf hypothesis, for every
fixed `δ > 0` a window of unit height at height `T` carries `o(log T)` zeroes at distance at
least `δ` from the critical line, on either side. -/
theorem tendsto_ncard_zerosOffCriticalLineWindow_div_log (hLH : LindelofHypothesis) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLineWindow δ T (T + 1)).ncard : ℝ) / Real.log T)
      atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr ?_
  intro η hη
  obtain ⟨A, hA, hbound⟩ := exists_ncard_zerosRightOfWindow_le hLH
    (σ := 1 / 2 + δ) (by linarith) (by linarith) (ε := η / 4) (by linarith)
  filter_upwards [eventually_ge_atTop (5 : ℝ),
    eventually_gt_atTop (Real.exp (4 * A / η))] with T hT5 hTexp
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT5
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT' : 4 * A / η < Real.log T := by
    have h := Real.log_lt_log (Real.exp_pos (4 * A / η)) hTexp
    rwa [Real.log_exp] at h
  have hAlt : A < η / 4 * Real.log T := by
    have h := (div_lt_iff₀ hη).mp hlogT'
    nlinarith
  have hhalf : ((zerosOffCriticalLineWindow δ T (T + 1)).ncard : ℝ)
      ≤ 2 * ((zerosRightOfWindow (1 / 2 + δ) T (T + 1)).ncard : ℝ) := by
    exact_mod_cast ncard_zerosOffCriticalLineWindow_le hδ0 hδ1 (by linarith)
  have h1 : ((zerosRightOfWindow (1 / 2 + δ) T (T + 1)).ncard : ℝ) ≤ A + η / 4 * Real.log T :=
    hbound T hT5
  have hnonneg : (0 : ℝ) ≤ ((zerosOffCriticalLineWindow δ T (T + 1)).ncard : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnonneg hlogT.le), div_lt_iff₀ hlogT]
  nlinarith

/-! ## The unconditional comparison

Without any hypothesis the same window carries `O(log T)` zeroes — this is the local
Riemann–von Mangoldt bound of `RiemannHypothesis.ZeroCountLocal`, restricted to the zeroes to the
right of `re s = σ`.  Recording it here makes the content of Backlund's criterion explicit: the
conditional statements above save the whole logarithm. -/

/-- The zeroes of `ζ` in the critical strip at height within `1` of `T` form a finite set. -/
lemma finite_zerosNearHeight {T : ℝ} (hT : 25 ≤ T) : (zerosNearHeight T).Finite := by
  obtain ⟨M, -, hsphere, hcne, -⟩ := exists_disc_data_near_height hT
  have hfin := finite_setOf_zeros (f := xiFn) (c := 4 + (T : ℂ) * I) (R := 20) (M := M)
    (by norm_num) differentiable_xiFn.diffContOnCl hsphere hcne
  exact hfin.subset (zerosNearHeight_subset T)

/-- **The unconditional bound.**  For every `σ`, a window of unit height at height `T` carries
`O(log T)` zeroes of `ζ` with real part at least `σ`, with an absolute implied constant. -/
theorem exists_ncard_zerosRightOfWindow_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ) (T : ℝ), 25 ≤ T →
      ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ C * Real.log T := by
  obtain ⟨C, hC, hbd⟩ := ncard_zerosNearHeight_le
  refine ⟨C, hC, fun σ T hT => ?_⟩
  have hsub : zerosRightOfWindow σ T (T + 1) ⊆ zerosNearHeight T := by
    rintro ρ ⟨hz, -, him0, himT⟩
    have himpos : 0 < ρ.im := lt_trans (by linarith) him0
    obtain ⟨h0, h1⟩ := mem_strip_of_zero_of_im_pos hz himpos
    exact ⟨hz, h0, h1, by rw [abs_le]; constructor <;> linarith⟩
  have hle : (zerosRightOfWindow σ T (T + 1)).ncard ≤ (zerosNearHeight T).ncard :=
    Set.ncard_le_ncard hsub (finite_zerosNearHeight hT)
  exact le_trans (by exact_mod_cast hle) (hbd T hT)

end RiemannHypothesis
