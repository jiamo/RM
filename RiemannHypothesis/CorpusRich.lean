/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CorpusCeiling

/-!
# A thicker corpus: four more unconditional facts, and the same ceiling

`RiemannHypothesis/CorpusCeiling.lean` abstracts the repository's unconditional facts about the
distribution of the zeroes into `ZeroCorpus θ` and shows that everything derivable from that
list stops at the proportion `1 − θ`, and in particular does not reach the Riemann hypothesis.
The force of such a negative result is exactly the richness of the list: a corpus with few facts
is easy to satisfy, so its independence result says little.

This file *thickens* the list.  `RichZeroCorpus θ` extends `ZeroCorpus θ` by four further facts,
each of them a theorem of this repository and none of them a consequence of the earlier ones:

* `simpleOnLine`, `window_simpleOnLine` (`sixty_seven_percent_simple_on_critical_line`) — a
  *fifth counting function*: the zeroes that are simple **and** on the line, with the same
  `1 − θ` proportion.
* `distinct_ratio` (`five_sixths_distinct`, Theorem C) — `N_d ≥ (5/6 − ε) N`, a quantitative
  bound on the loss from multiplicity, where the plain corpus has only `N_d ≤ N` and the
  `O(log T)` factor of `mult`.
* `localCount` (`sum_zeroMultiplicity_zerosNearHeight_le`) — the **local** Riemann–von Mangoldt
  bound `N(T+1) − N(T) = O(log T)`, which the global asymptotic with its `O(T)` error does not
  imply.
* `strip` (the definition of a nontrivial zero) — no zero at distance `1/2` or more from the
  critical line, at *every* height; the zero-free region of the plain corpus is asymptotic.

## The results

* `RiemannHypothesis.RichZeroCorpus` — the enlarged constraint system.
* `RiemannHypothesis.richModelCorpus` — the model of `CorpusCeiling` satisfies all four new
  facts as well: for every rate `r < θ` there is a *rich* corpus whose off-line count is
  `r·N(T) + O(1)`.
* `RiemannHypothesis.rh_not_derivable_from_rich_corpus` — the thicker corpus still does not
  entail the Riemann hypothesis.
* `RiemannHypothesis.rich_corpus_window_ceiling` — and it still has exactly the same ceiling:
  a proportion `p` on the critical line is derivable from the enlarged list if and only if
  `p ≤ 1 − θ`.  The four new facts buy nothing towards the conjecture, which is a sharper
  statement than the one of `CorpusCeiling` because the list is longer.
* `RiemannHypothesis.rich_density_not_sufficient` — the same for density bounds at a fixed
  distance.

## Scope

As in `CorpusCeiling`, nothing here is a statement about `ζ`; the instance that the zeroes of `ζ`
provide is built in `RiemannHypothesis/CorpusRichInstance.lean`.  These are theorems about what a
fixed list of inequalities between counting functions can and cannot prove.
-/

namespace RiemannHypothesis

open Real

/-- The counting data of `ZeroCorpus`, together with four further unconditional facts of this
repository: the simple-and-on-the-line count, Theorem C's bound on multiplicity loss, the local
Riemann–von Mangoldt bound, and the containment of the zeroes in the open critical strip. -/
structure RichZeroCorpus (θ : ℝ) extends ZeroCorpus θ where
  /-- `N₀ˢ(T)`: the distinct zeroes of ordinate in `(0, T]` that are simple and on the critical
  line.  Repository: `windowCountSimpleOnLine 0 T`. -/
  simpleOnLine : ℝ → ℝ
  simpleOnLine_nonneg : ∀ T, 0 ≤ simpleOnLine T
  /-- a simple zero on the line is a zero on the line -/
  simpleOnLine_le_onLine : ∀ T, simpleOnLine T ≤ onLine T
  /-- **The mollifier proportion, for simple zeroes.**  At least `1 − θ` of the zeroes of a
  dyadic window are simple *and* on the critical line.  Repository:
  `sixty_seven_percent_simple_on_critical_line`. -/
  window_simpleOnLine : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (1 - θ) * (total (2 * T) - total T) ≤ simpleOnLine (2 * T) - simpleOnLine T
  /-- **Theorem C.**  At least `5/6 − ε` of the zeroes of a dyadic window, counted with
  multiplicity, are distinct.  Repository: `five_sixths_distinct`. -/
  distinct_ratio : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (5 / 6 - ε) * (total (2 * T) - total T) ≤ distinct (2 * T) - distinct T
  /-- **The local Riemann–von Mangoldt bound.**  A unit window contains `O(log T)` zeroes, with
  multiplicity.  Repository: `sum_zeroMultiplicity_zerosNearHeight_le`. -/
  localCount : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀,
    total (T + 1) - total T ≤ C * Real.log T
  /-- **The zeroes lie in the open critical strip**, at every height: nothing at distance `1/2`
  or more from the critical line.  Repository: the definition of `nontrivialZeroSet`. -/
  strip : ∀ T, offAt (1 / 2) T = 0

namespace RichZeroCorpus

variable {θ : ℝ}

/-- Soundness, inherited: the off-line count of a dyadic window is eventually at most `θ` times
its total count. -/
theorem windowOff_le (Z : RichZeroCorpus θ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, Z.toZeroCorpus.windowOff T ≤ θ * Z.toZeroCorpus.windowTotal T :=
  Z.toZeroCorpus.windowOff_le

/-- **The simple zeroes of a window are eventually a proportion `1 − θ` of it**, and hence, with
`windowOff_le`, all but the off-line ones: the new counting function is constrained exactly as
the on-line count is. -/
theorem windowSimple_ge (Z : RichZeroCorpus θ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - θ) * Z.toZeroCorpus.windowTotal T ≤ Z.simpleOnLine (2 * T) - Z.simpleOnLine T := by
  obtain ⟨T₀, hT₀⟩ := Z.window_simpleOnLine
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end RichZeroCorpus

/-! ## The model satisfies the four new facts as well -/

/-- The growth of the model count over a unit window is at most `log T`: the model obeys the
local Riemann–von Mangoldt bound. -/
lemma rvmModel_unit_window_le {T : ℝ} (hT : 32 ≤ T) :
    rvmModel (T + 1) - rvmModel T ≤ Real.log T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (32 : ℝ) ≤ T + 1 := by linarith
  have hlogT : (3.4 : ℝ) ≤ Real.log T := log_ge_of_ge hT
  have hpi : (6 : ℝ) < 2 * Real.pi := two_pi_pos
  -- `log (T+1) ≤ log T + 1/T ≤ log T + 1`
  have hdiv : Real.log ((T + 1) / T) ≤ (T + 1) / T - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log ((T + 1) / T) = Real.log (T + 1) - Real.log T :=
    Real.log_div (by linarith) (by linarith)
  have hfrac : (T + 1) / T - 1 = 1 / T := by
    field_simp
    ring
  have hstep : Real.log (T + 1) ≤ Real.log T + 1 / T := by
    rw [hsplit, hfrac] at hdiv
    linarith
  have hTinv : 1 / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have hlog1 : Real.log (T + 1) ≤ Real.log T + 1 := by linarith
  have hlogpos : (0 : ℝ) < Real.log T := by linarith
  have hkey : rvmModel (T + 1) - rvmModel T
      = ((T + 1) * Real.log (T + 1) - T * Real.log T) / (2 * Real.pi) := by
    rw [rvmModel_eq hT1, rvmModel_eq hT]
    field_simp
  have hnum : (T + 1) * Real.log (T + 1) - T * Real.log T ≤ Real.log T + 2 := by
    have h1 : (T + 1) * Real.log (T + 1) ≤ (T + 1) * (Real.log T + 1 / T) := by
      exact mul_le_mul_of_nonneg_left hstep (by linarith)
    have h2 : (T + 1) * (Real.log T + 1 / T) = T * Real.log T + Real.log T + (T + 1) / T := by
      field_simp
    have h3 : (T + 1) / T ≤ 2 := by
      rw [div_le_iff₀ hT0]; linarith
    linarith
  rw [hkey, div_le_iff₀ (by linarith)]
  nlinarith [hlogT, hpi, hlogpos]

/-- **The rich model corpus.**  The counting configuration of `modelCorpus` — a positive
proportion of the zeroes off the critical line — satisfies the four additional facts as well. -/
noncomputable def richModelCorpus (θ r : ℝ) (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    RichZeroCorpus θ where
  toZeroCorpus := modelCorpus θ r hr hrθ hθ
  simpleOnLine := fun T => rvmModel T - offModel r T
  simpleOnLine_nonneg := (modelCorpus θ r hr hrθ hθ).onLine_nonneg
  simpleOnLine_le_onLine := fun _ => le_rfl
  window_simpleOnLine := (modelCorpus θ r hr hrθ hθ).window_onLine
  distinct_ratio := by
    intro ε hε
    refine ⟨0, fun T hT => ?_⟩
    have hmono := rvmModel_mono (show T ≤ 2 * T by linarith)
    have hW : 0 ≤ rvmModel (2 * T) - rvmModel T := by linarith
    change (5 / 6 - ε) * (rvmModel (2 * T) - rvmModel T) ≤ rvmModel (2 * T) - rvmModel T
    nlinarith
  localCount := by
    refine ⟨1, one_pos, 32, fun T hT => ?_⟩
    have h := rvmModel_unit_window_le hT
    change rvmModel (T + 1) - rvmModel T ≤ 1 * Real.log T
    linarith
  strip := by
    intro T
    change offAtModel r (1 / 2) T = 0
    have hfloor : ⌊(1 : ℝ) / (1 / 2)⌋₊ = 2 := by
      rw [show (1 : ℝ) / (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
    unfold offAtModel
    rw [hfloor]
    norm_num
    exact offModel_nonneg r T

@[simp] lemma richModelCorpus_toZeroCorpus {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    (richModelCorpus θ r hr hrθ hθ).toZeroCorpus = modelCorpus θ r hr hrθ hθ := rfl

/-! ## What the thicker corpus can and cannot prove -/

/-- **The Riemann hypothesis is not derivable from the thicker corpus either.**  Adding the
simple-zero count with its `67 %`, Theorem C, the local Riemann–von Mangoldt bound and the
containment in the open critical strip to the list still leaves a counting configuration with a
positive proportion of off-line zeroes. -/
theorem rh_not_derivable_from_rich_corpus :
    ¬ ∀ Z : RichZeroCorpus 0.33, RHCounts Z.toZeroCorpus := by
  intro h
  have hpos := modelCorpus_off_pos (θ := 0.33) (r := 0.3) (by norm_num) (by norm_num)
    (by norm_num) (T := 32) le_rfl (by norm_num)
  have h32 : (modelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num)).off 32 = 0 :=
    h (richModelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num)) 32
  rw [h32] at hpos
  exact lt_irrefl 0 hpos

/-- **The thicker corpus does not give a zero proportion off the critical line.** -/
theorem rich_offLine_positive_proportion_consistent {q : ℝ} (hq : 0 < q) (hq' : q < 0.33) :
    ∃ Z : RichZeroCorpus 0.33, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      q * Z.toZeroCorpus.windowTotal T ≤ Z.toZeroCorpus.windowOff T := by
  obtain ⟨r, hqr, hrθ⟩ := exists_between hq'
  have hr : 0 < r := lt_trans hq hqr
  refine ⟨richModelCorpus 0.33 r hr hrθ (by norm_num), ?_⟩
  obtain ⟨T₀, hT₀⟩ := modelCorpus_windowOff_ge (θ := 0.33) hr hrθ (by norm_num)
    (ε := r - q) (by linarith)
  exact ⟨T₀, fun T hT => by simpa [show r - (r - q) = q by ring] using hT₀ T hT⟩

/-- **No density theorem at a fixed distance closes the gap, even against the thicker
corpus.** -/
theorem rich_density_not_sufficient :
    ∃ Z : RichZeroCorpus 0.33,
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, Z.toZeroCorpus.offAt δ T ≤ C) ∧
        ¬ RHCounts Z.toZeroCorpus := by
  refine ⟨richModelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num), ?_, ?_⟩
  · exact fun δ hδ => ⟨2 / δ, fun T => modelCorpus_offAt_bounded (θ := 0.33) (r := 0.3)
      (by norm_num) (by norm_num) (by norm_num) hδ T⟩
  · intro h
    have hpos := modelCorpus_off_pos (θ := 0.33) (r := 0.3) (by norm_num) (by norm_num)
      (by norm_num) (T := 32) le_rfl (by norm_num)
    have h32 : (modelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num)).off 32 = 0 :=
      h 32
    rw [h32] at hpos
    exact lt_irrefl 0 hpos

/-- **The ceiling of the thicker corpus is the same.**  A proportion `p` of the zeroes of a
dyadic window on the critical line is derivable from the enlarged list of facts **if and only
if** `p ≤ 1 − θ`.  Since the list is strictly longer than that of `corpus_window_ceiling`, this
is a strictly stronger negative statement: the simple-zero count, Theorem C, the local
Riemann–von Mangoldt bound and the critical strip do not move the ceiling. -/
theorem rich_corpus_window_ceiling {θ p : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∀ Z : RichZeroCorpus θ, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        p * Z.toZeroCorpus.windowTotal T ≤ Z.toZeroCorpus.windowOn T) ↔ p ≤ 1 - θ := by
  constructor
  · intro h
    -- the model corpora are rich, so a bound for all rich corpora bounds them too
    have hmodel : ∀ (r : ℝ) (hr : 0 < r) (hrθ : r < θ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
        p * (modelCorpus θ r hr hrθ hθ1).windowTotal T
          ≤ (modelCorpus θ r hr hrθ hθ1).windowOn T := by
      intro r hr hrθ
      exact h (richModelCorpus θ r hr hrθ hθ1)
    -- reproduce the argument of `corpus_window_ceiling` with the rich models
    · by_contra hp
      push Not at hp
      set ε : ℝ := min ((p - (1 - θ)) / 3) (θ / 2) with hεdef
      have hε1 : ε ≤ (p - (1 - θ)) / 3 := min_le_left _ _
      have hε2 : ε ≤ θ / 2 := min_le_right _ _
      have hε : 0 < ε := lt_min (by linarith) (by linarith)
      have hrlt : θ - ε < θ := by linarith
      have hrpos : 0 < θ - ε := by linarith
      obtain ⟨T₀, hT₀⟩ := hmodel (θ - ε) hrpos hrlt
      obtain ⟨T₁, hT₁⟩ :=
        modelCorpus_windowOff_ge (θ := θ) (r := θ - ε) hrpos hrlt hθ1 (ε := ε) hε
      set T : ℝ := max (max T₀ T₁) 32 with hTdef
      have hT32 : (32 : ℝ) ≤ T := le_max_right _ _
      have h1 := hT₀ T (le_trans (le_max_left _ _) (le_max_left _ _))
      have h2 := hT₁ T (le_trans (le_max_right _ _) (le_max_left _ _))
      have hWval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowTotal T
          = rvmModel (2 * T) - rvmModel T := rfl
      have hOffval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowOff T
          = offModel (θ - ε) (2 * T) - offModel (θ - ε) T := rfl
      have hOnval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowOn T
          = (rvmModel (2 * T) - rvmModel T)
            - (offModel (θ - ε) (2 * T) - offModel (θ - ε) T) := by
        change (rvmModel (2 * T) - offModel (θ - ε) (2 * T))
            - (rvmModel T - offModel (θ - ε) T) = _
        ring
      rw [hWval, hOnval] at h1
      rw [hWval, hOffval] at h2
      have hW : T / 2 ≤ rvmModel (2 * T) - rvmModel T := rvmModel_window_ge hT32
      have hWpos : 0 < rvmModel (2 * T) - rvmModel T := by linarith
      have hkey : p * (rvmModel (2 * T) - rvmModel T)
          ≤ (1 - θ + 2 * ε) * (rvmModel (2 * T) - rvmModel T) := by nlinarith [h1, h2]
      have hple : p ≤ 1 - θ + 2 * ε := le_of_mul_le_mul_right hkey hWpos
      linarith
  · intro hp Z
    obtain ⟨T₀, hT₀⟩ := (corpus_window_ceiling (p := p) hθ hθ1).2 hp Z.toZeroCorpus
    exact ⟨T₀, hT₀⟩

end RiemannHypothesis
