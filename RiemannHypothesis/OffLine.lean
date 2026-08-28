/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.PartialProved
import RiemannHypothesis.CriticalLineOrdinates

/-!
# At most a third of the zeroes lie off the critical line

`RiemannHypothesis.Zeta23Bridge` states that at least two thirds of the nontrivial zeroes of
`ζ` — counted with multiplicity on the left, as distinct points on the right — lie on the
critical line.  Read from the other side, this bounds the zeroes that could possibly violate
the Riemann hypothesis: at most a third of them, in the same counting sense.

## Main results

* `windowCountOffLine`: the number of distinct nontrivial zeroes in a window `(T₁, T₂]` whose
  real part is *not* `1/2`;
* `one_third_off_critical_line` and `one_third_off_critical_line_cumulative`:
  `limsup N_off/N ≤ 1/3`, in dyadic and in cumulative windows;
* `offCriticalZeroCount`, `eventually_offCriticalZeroCount_le` and
  `limsup_offCriticalZeroCount_div_le_one_third`: the same bound in the counting functions of
  `RiemannHypothesis.Partial`.

None of this bears on the hypothesis itself, which asserts that the off-line count is *zero*;
what is proved here is only that its proportion cannot exceed `1/3`.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## The off-line count in a window -/

/-- The nontrivial zeroes of `ζ` with ordinate in `(T₁, T₂]` that are *not* on the critical
line. -/
def windowZerosOffLine (T₁ T₂ : ℝ) : Set ℂ := windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re ≠ 1 / 2}

/-- The number of distinct nontrivial zeroes of ordinate in `(T₁, T₂]` off the critical
line. -/
def windowCountOffLine (T₁ T₂ : ℝ) : ℕ := (windowZerosOffLine T₁ T₂).ncard

/-- Splitting the zeroes of a window according to whether they lie on the critical line. -/
lemma windowCountOffLine_add_windowCountOnLine (T₁ T₂ : ℝ) :
    windowCountOffLine T₁ T₂ + windowCountOnLine T₁ T₂ = windowCountDistinct T₁ T₂ := by
  classical
  have hfin := windowZeros_finite T₁ T₂
  have hdisj : Disjoint (windowZerosOffLine T₁ T₂) (windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}) :=
    Set.disjoint_left.2 fun s hs hs' => hs.2 hs'.2
  have hunion : windowZerosOffLine T₁ T₂ ∪ (windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}) =
      windowZeros T₁ T₂ := by
    ext s
    simp only [windowZerosOffLine, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
    · intro hs
      by_cases hre : s.re = 1 / 2
      · exact Or.inr ⟨hs, hre⟩
      · exact Or.inl ⟨hs, hre⟩
  have := Set.ncard_union_eq hdisj (hfin.subset fun s hs => hs.1)
    (hfin.subset fun s hs => hs.1)
  rw [hunion] at this
  simpa only [windowCountOffLine, windowCountOnLine, windowCountDistinct] using this.symm

/-- **At most a third of the zeroes lie off the critical line** (dyadic windows): for every
`ε > 0` and all large `T`, `N_off(T, 2T) ≤ (1/3 + ε)·N(T, 2T)`. -/
theorem one_third_off_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (windowCountOffLine T (2 * T) : ℝ) ≤ (1 / 3 + ε) * windowCount T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (windowCountOffLine T (2 * T) : ℝ) + windowCountOnLine T (2 * T)
      = windowCountDistinct T (2 * T) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine T (2 * T))
  have hle : (windowCountDistinct T (2 * T) : ℝ) ≤ windowCount T (2 * T) := by
    exact_mod_cast windowCountDistinct_le_windowCount T (2 * T)
  have h := hT₀ T hT
  nlinarith [hsplit, hle, h]

/-- **At most a third of the zeroes lie off the critical line**, cumulative form over the
windows `(0, T]`. -/
theorem one_third_off_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (windowCountOffLine 0 T : ℝ) ≤ (1 / 3 + ε) * windowCount 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (windowCountOffLine 0 T : ℝ) + windowCountOnLine 0 T
      = windowCountDistinct 0 T := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine 0 T)
  have hle : (windowCountDistinct 0 T : ℝ) ≤ windowCount 0 T := by
    exact_mod_cast windowCountDistinct_le_windowCount 0 T
  have h := hT₀ T hT
  nlinarith [hsplit, hle, h]

/-! ## The off-line count in the counting functions of `Partial.lean` -/

/-- The number of zeroes of `ζ` with imaginary part in `(0, T)` that are *not* on the critical
line — the complement, inside `zeroCount`, of `criticalZeroCount`. -/
def offCriticalZeroCount (T : ℝ) : ℕ :=
  ncard {s : ℂ | riemannZeta s = 0 ∧ s.re ≠ 1 / 2 ∧ 0 < s.im ∧ s.im < T}

lemma offCriticalZeroCount_add_criticalZeroCount (T : ℝ) :
    offCriticalZeroCount T + criticalZeroCount T = zeroCount T := by
  classical
  have hfin := openWindowZeros_finite T
  have hsub₁ : {s : ℂ | riemannZeta s = 0 ∧ s.re ≠ 1 / 2 ∧ 0 < s.im ∧ s.im < T} ⊆
      openWindowZeros T := fun s hs => ⟨hs.1, hs.2.2.1, hs.2.2.2⟩
  have hsub₂ : {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ 0 < s.im ∧ s.im < T} ⊆
      openWindowZeros T := fun s hs => ⟨hs.1, hs.2.2.1, hs.2.2.2⟩
  have hdisj : Disjoint {s : ℂ | riemannZeta s = 0 ∧ s.re ≠ 1 / 2 ∧ 0 < s.im ∧ s.im < T}
      {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ 0 < s.im ∧ s.im < T} :=
    Set.disjoint_left.2 fun s hs hs' => hs.2.1 hs'.2.1
  have hunion : {s : ℂ | riemannZeta s = 0 ∧ s.re ≠ 1 / 2 ∧ 0 < s.im ∧ s.im < T} ∪
      {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ 0 < s.im ∧ s.im < T} =
      {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T} := by
    ext s
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hz, -, him, hlt⟩ | ⟨hz, -, him, hlt⟩) <;> exact ⟨hz, him, hlt⟩
    · rintro ⟨hz, him, hlt⟩
      by_cases hre : s.re = 1 / 2
      · exact Or.inr ⟨hz, hre, him, hlt⟩
      · exact Or.inl ⟨hz, hre, him, hlt⟩
  have := Set.ncard_union_eq hdisj (hfin.subset hsub₁) (hfin.subset hsub₂)
  rw [hunion] at this
  simpa only [offCriticalZeroCount, criticalZeroCount, zeroCount] using this.symm

/-- **At most a third of the zeroes lie off the critical line**, in the counting functions of
`RiemannHypothesis.Partial`: for every `ε > 0`, eventually `N_off(T) ≤ (1/3 + ε)·N(T)`. -/
theorem eventually_offCriticalZeroCount_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, (offCriticalZeroCount T : ℝ) ≤ (1 / 3 + ε) * zeroCount T := by
  filter_upwards [eventually_twoThirds_criticalZeroCount ε hε] with T hT
  have hsplit : (offCriticalZeroCount T : ℝ) + criticalZeroCount T = zeroCount T := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (offCriticalZeroCount_add_criticalZeroCount T)
  rcases Nat.eq_zero_or_pos (zeroCount T) with h0 | hpos
  · have hnat := offCriticalZeroCount_add_criticalZeroCount T
    have hoff : offCriticalZeroCount T = 0 := by omega
    simp [hoff, h0]
  · have hposR : (0 : ℝ) < zeroCount T := by exact_mod_cast hpos
    rw [le_div_iff₀ hposR] at hT
    linarith

/-- The proportion of zeroes off the critical line has upper limit at most `1/3`. -/
theorem limsup_offCriticalZeroCount_div_le_one_third :
    limsup (fun T : ℝ => (offCriticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop ≤ 1 / 3 := by
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun T : ℝ => (offCriticalZeroCount T : ℝ) / (zeroCount T : ℝ)) := by
    refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with T
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_le hcobdd ?_
  filter_upwards [eventually_offCriticalZeroCount_le ε hε] with T hT
  rcases Nat.eq_zero_or_pos (zeroCount T) with h0 | hpos
  · simp only [h0, Nat.cast_zero, div_zero]
    positivity
  · have hposR : (0 : ℝ) < zeroCount T := by exact_mod_cast hpos
    rw [div_le_iff₀ hposR]
    linarith

end RiemannHypothesis
