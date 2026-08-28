/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCriterion

/-!
# Equidistribution modulo one in its counting form

`RiemannHypothesis.WeylCriterion` proves Weyl's criterion with equidistribution expressed against
continuous test functions on the circle.  This module converts that into the classical counting
statement: the proportion of the first `N` terms whose fractional part lies in a subinterval
`[a, b) ⊆ (0, 1)` tends to the length `b − a`.

## Main results

* `trap` — the trapezoidal function which is `1` on `[u, v]`, `0` outside `(u − η, v + η)`, and
  linear in between; `trapCirc` is its descent to the circle.
* `tendsto_avg_real` — the real-valued form of equidistribution.
* `tendsto_countIn_div` — **the counting form**: if `x` is equidistributed modulo one and
  `0 < a < b < 1`, then

      #{n < N : Int.fract (x n) ∈ [a, b)} / N → b − a .

* `tendsto_countIn_div_quadratic` — the same for `x n = α n²` with `α` irrational, which is
  Weyl's theorem for quadratic sequences in its classical form.

## Proof

The indicator of `[a, b)` is squeezed between two trapezoids: one supported in `[a, b]` and equal
to `1` on `[a + η, b − η]`, one equal to `1` on `[a, b]` and supported in `[a − η, b + η]`.  Both
descend to continuous functions on the circle because their supports avoid the point `0`, which
is where `[0, 1)` is glued.  Their integrals differ from `b − a` by at most `2η`, and the averages
of continuous functions converge by hypothesis, so the counting quotient is caught between
`b − a − ε` and `b − a + ε`.

## Scope

The hypothesis `0 < a < b < 1` keeps the interval away from the glueing point; the statement for
an interval containing `0` is not derived.  Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory AddCircle

namespace RiemannHypothesis

namespace WeylCount

open KusminLandau WeylCriterion

/-- The trapezoid: `1` on `[u, v]`, `0` off `(u − η, v + η)`, linear in between. -/
def trap (u v η t : ℝ) : ℝ := max 0 (min 1 (min ((t - u + η) / η) ((v + η - t) / η)))

theorem continuous_trap (u v η : ℝ) : Continuous (trap u v η) := by
  unfold trap
  fun_prop

theorem trap_nonneg (u v η t : ℝ) : 0 ≤ trap u v η t := le_max_left _ _

theorem trap_le_one (u v η t : ℝ) : trap u v η t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem trap_eq_one {u v η t : ℝ} (hη : 0 < η) (hu : u ≤ t) (hv : t ≤ v) : trap u v η t = 1 := by
  have h1 : 1 ≤ (t - u + η) / η := by
    rw [le_div_iff₀ hη]
    linarith
  have h2 : 1 ≤ (v + η - t) / η := by
    rw [le_div_iff₀ hη]
    linarith
  unfold trap
  rw [min_eq_left (le_min h1 h2)]
  simp

theorem trap_eq_zero_of_le {u v η t : ℝ} (hη : 0 < η) (ht : t ≤ u - η) : trap u v η t = 0 := by
  have h1 : (t - u + η) / η ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  unfold trap
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1))

theorem trap_eq_zero_of_ge {u v η t : ℝ} (hη : 0 < η) (ht : v + η ≤ t) : trap u v η t = 0 := by
  have h1 : (v + η - t) / η ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  unfold trap
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1))

/-- The trapezoid, descended to the circle.  The hypotheses place its support inside `(0, 1)`, so
the descent is continuous. -/
def trapCirc (u v η : ℝ) (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1) : C(Circ, ℝ) where
  toFun := AddCircle.liftIco 1 0 (trap u v η)
  continuous_toFun := by
    refine AddCircle.liftIco_zero_continuous ?_ (continuous_trap u v η).continuousOn
    rw [trap_eq_zero_of_le hη (by linarith), trap_eq_zero_of_ge hη (by linarith)]

theorem trapCirc_coe {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    trapCirc u v η hη h0 h1 ((t : ℝ) : Circ) = trap u v η t := by
  simp only [trapCirc, ContinuousMap.coe_mk]
  exact AddCircle.liftIco_zero_coe_apply ht

/-- A real number and its fractional part have the same image in the circle. -/
theorem coe_eq_coe_fract (y : ℝ) : ((y : ℝ) : Circ) = ((Int.fract y : ℝ) : Circ) := by
  have hy : y = Int.fract y + (⌊y⌋ : ℝ) := by
    rw [Int.fract]
    ring
  have hzero : (((⌊y⌋ : ℤ) : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨⌊y⌋, by simp⟩
  calc ((y : ℝ) : Circ) = ((Int.fract y + (⌊y⌋ : ℝ) : ℝ) : Circ) := by rw [← hy]
    _ = ((Int.fract y : ℝ) : Circ) + (((⌊y⌋ : ℤ) : ℝ) : Circ) := by rw [AddCircle.coe_add]
    _ = ((Int.fract y : ℝ) : Circ) := by rw [hzero, add_zero]

/-- Equidistribution, tested against real-valued continuous functions. -/
theorem tendsto_avg_real {x : ℕ → ℝ} (h : EquidistributedMod1 x) (f : C(Circ, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : Circ)) atTop
      (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  have hgf := h ⟨fun t => ((f t : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  simp only [ContinuousMap.coe_mk] at hgf
  rw [integral_complex_ofReal] at hgf
  have hre := (Complex.continuous_re.tendsto (((∫ t, f t ∂haarAddCircle : ℝ) : ℂ))).comp hgf
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr fun N => ?_
  simp only [avg]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- The mean of the descended trapezoid is the integral of the trapezoid over `[0, 1]`. -/
theorem integral_trapCirc_eq {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1) :
    (∫ t, trapCirc u v η hη h0 h1 t ∂haarAddCircle) = ∫ t in (0 : ℝ)..1, trap u v η t := by
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun t : Circ => trapCirc u v η hη h0 h1 t)
  have hvol : (volume : Measure Circ) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol] at hpre
  rw [← hpre]
  simp only [zero_add]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  change trapCirc u v η hη h0 h1 ((t : ℝ) : Circ) = trap u v η t
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact trapCirc_coe hη h0 h1 ⟨ht.1, hlt⟩
  · have hcoe : ((t : ℝ) : Circ) = ((0 : ℝ) : Circ) := by
      rw [heq]
      simp
    rw [hcoe, trapCirc_coe hη h0 h1 ⟨le_rfl, by norm_num⟩, trap_eq_zero_of_le hη (by linarith),
      heq]
    exact (trap_eq_zero_of_ge hη (by linarith)).symm

/-- The mean of a trapezoid is at most the length of its plateau plus `2η`. -/
theorem integral_trapCirc_le {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1)
    (huv : u ≤ v) :
    (∫ t, trapCirc u v η hη h0 h1 t ∂haarAddCircle) ≤ (v - u) + 2 * η := by
  rw [integral_trapCirc_eq hη h0 h1]
  have hcont : Continuous (trap u v η) := continuous_trap u v η
  have hsplit : (∫ t in (0 : ℝ)..1, trap u v η t)
      = (∫ t in (0 : ℝ)..(u - η), trap u v η t) + (∫ t in (u - η)..(v + η), trap u v η t)
        + ∫ t in (v + η)..(1 : ℝ), trap u v η t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hleft : (∫ t in (0 : ℝ)..(u - η), trap u v η t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact trap_eq_zero_of_le hη ht.2
  have hright : (∫ t in (v + η)..(1 : ℝ), trap u v η t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact trap_eq_zero_of_ge hη ht.1
  have hmid : (∫ t in (u - η)..(v + η), trap u v η t) ≤ (v + η) - (u - η) := by
    have hle : (u - η) ≤ (v + η) := by linarith
    calc (∫ t in (u - η)..(v + η), trap u v η t)
        ≤ ∫ _t in (u - η)..(v + η), (1 : ℝ) :=
          intervalIntegral.integral_mono_on hle (hcont.intervalIntegrable _ _)
            intervalIntegrable_const fun t _ => trap_le_one u v η t
      _ = (v + η) - (u - η) := by simp
  rw [hsplit, hleft, hright]
  linarith

/-- The mean of a trapezoid is at least the length of its plateau. -/
theorem le_integral_trapCirc {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1)
    (huv : u ≤ v) :
    (v - u) ≤ ∫ t, trapCirc u v η hη h0 h1 t ∂haarAddCircle := by
  rw [integral_trapCirc_eq hη h0 h1]
  have hcont : Continuous (trap u v η) := continuous_trap u v η
  have hsplit : (∫ t in (0 : ℝ)..1, trap u v η t)
      = (∫ t in (0 : ℝ)..u, trap u v η t) + (∫ t in u..v, trap u v η t)
        + ∫ t in v..(1 : ℝ), trap u v η t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hleft : 0 ≤ ∫ t in (0 : ℝ)..u, trap u v η t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => trap_nonneg _ _ _ _
  have hright : 0 ≤ ∫ t in v..(1 : ℝ), trap u v η t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => trap_nonneg _ _ _ _
  have hmid : (v - u) ≤ ∫ t in u..v, trap u v η t := by
    calc (v - u) = ∫ _t in u..v, (1 : ℝ) := by simp
      _ ≤ ∫ t in u..v, trap u v η t :=
          intervalIntegral.integral_mono_on huv intervalIntegrable_const
            (hcont.intervalIntegrable _ _) fun t ht => ge_of_eq (trap_eq_one hη ht.1 ht.2)
  rw [hsplit]
  linarith

/-- The number of `n < N` whose fractional part lies in `[a, b)`. -/
def countIn (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card

theorem countIn_eq_sum (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (countIn x a b N : ℝ)
      = ∑ n ∈ Finset.range N,
          (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) := by
  rw [countIn, Finset.sum_boole]

/-- **The counting form of equidistribution.** -/
theorem tendsto_countIn_div {x : ℕ → ℝ} (h : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := min (min (a / 2) ((1 - b) / 2)) (min ((b - a) / 4) (ε / 8)) with hηdef
  have hη1 : η ≤ a / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη2 : η ≤ (1 - b) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη3 : η ≤ (b - a) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη4 : η ≤ ε / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hup0 : 0 < a - η := by linarith
  have hup1 : b + η < 1 := by linarith
  have hlow0 : 0 < (a + η) - η := by linarith
  have hlow1 : (b - η) + η < 1 := by linarith
  set up : C(Circ, ℝ) := trapCirc a b η hη0 hup0 hup1 with hupdef
  set low : C(Circ, ℝ) := trapCirc (a + η) (b - η) η hη0 hlow0 hlow1 with hlowdef
  have hupint : (∫ t, up t ∂haarAddCircle) ≤ (b - a) + 2 * η :=
    integral_trapCirc_le hη0 hup0 hup1 hab.le
  have hlowint : (b - a) - 2 * η ≤ ∫ t, low t ∂haarAddCircle := by
    have := le_integral_trapCirc hη0 hlow0 hlow1 (by linarith : a + η ≤ b - η)
    linarith [this]
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 (tendsto_avg_real h up)) (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 (tendsto_avg_real h low)) (ε / 4) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- the pointwise sandwich
  have hpoint_up : ∀ n : ℕ,
      (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0)
        ≤ up ((x n : ℝ) : Circ) := by
    intro n
    have hfr : Int.fract (x n) ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hval : up ((x n : ℝ) : Circ) = trap a b η (Int.fract (x n)) := by
      rw [coe_eq_coe_fract, hupdef, trapCirc_coe hη0 hup0 hup1 hfr]
    rw [hval]
    by_cases hmem : a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
    · rw [if_pos hmem, trap_eq_one hη0 hmem.1 hmem.2.le]
    · rw [if_neg hmem]
      exact trap_nonneg _ _ _ _
  have hpoint_low : ∀ n : ℕ, low ((x n : ℝ) : Circ)
      ≤ (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) := by
    intro n
    have hfr : Int.fract (x n) ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hval : low ((x n : ℝ) : Circ) = trap (a + η) (b - η) η (Int.fract (x n)) := by
      rw [coe_eq_coe_fract, hlowdef, trapCirc_coe hη0 hlow0 hlow1 hfr]
    rw [hval]
    by_cases hmem : a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
    · rw [if_pos hmem]
      exact trap_le_one _ _ _ _
    · rw [if_neg hmem]
      simp only [not_and, not_lt] at hmem
      rcases lt_or_ge (Int.fract (x n)) a with hlt | hge
      · exact le_of_eq (trap_eq_zero_of_le hη0 (by linarith))
      · have hbb : b ≤ Int.fract (x n) := hmem hge
        exact le_of_eq (trap_eq_zero_of_ge hη0 (by linarith))
  have hsum_up : (countIn x a b N : ℝ) / N
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, up ((x n : ℝ) : Circ) := by
    rw [countIn_eq_sum, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hpoint_up n) (by positivity)
  have hsum_low : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, low ((x n : ℝ) : Circ)
      ≤ (countIn x a b N : ℝ) / N := by
    rw [countIn_eq_sum, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hpoint_low n) (by positivity)
  have h1 := hN₁ N hN1'
  have h2 := hN₂ N hN2'
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  constructor
  · have := abs_lt.1 (by rw [← Real.dist_eq]; exact hN₂ N hN2')
    linarith [hsum_low, hlowint, this.1]
  · have := abs_lt.1 (by rw [← Real.dist_eq]; exact hN₁ N hN1')
    linarith [hsum_up, hupint, this.2]

/-- **Weyl's theorem for quadratic sequences, in its classical form**: for every irrational `α`
the proportion of `n < N` with `α n²` having fractional part in `[a, b)` tends to `b − a`. -/
theorem tendsto_countIn_div_quadratic {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun N : ℕ => (countIn (fun n : ℕ => α * (n : ℝ) ^ 2) a b N : ℝ) / N) atTop
      (𝓝 (b - a)) :=
  tendsto_countIn_div (equidistributedMod1_quadratic hα) ha hab hb

end WeylCount

end RiemannHypothesis
