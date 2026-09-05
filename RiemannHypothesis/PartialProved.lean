/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CriticalLine
import RiemannHypothesis.Partial
import RiemannHypothesis.Zeros
import Zeta23.RvM.NcountWindow

/-!
# The stated partial results, proved

`RiemannHypothesis.Partial` states the classical partial results towards the Riemann
hypothesis as `Prop`s, phrased with the counting functions

* `zeroCount T`         — the number of zeroes of `ζ` with `0 < im ρ < T`, distinct;
* `criticalZeroCount T` — those of them on the critical line.

Note that these are *open* windows `(0, T)` and count *distinct* zeroes, whereas
`RiemannHypothesis.Zeta23Bridge` uses half-open windows `(0, T]`.  The bridge between the
two is `exists_window_eq_openWindowZeros`: for each `T` the open window `(0, T)` cuts out
exactly the same set of zeroes as some half-open window `(0, T']` with `T' < T`, because
there are only finitely many zeroes below any height.

With that, the two-thirds theorem gives all of the following, unconditionally:

* `hardyTheorem` — Hardy's theorem `HardyTheorem`;
* `twoThirds_le_liminf_criticalZeroCount_div` — `liminf N₀(T)/N(T) ≥ 2/3`;
* `positiveProportionOnCriticalLine` — Selberg's `PositiveProportionOnCriticalLine`;
* `oneThirdOnCriticalLine`, `twoFifthsOnCriticalLine` — the Levinson and Conrey
  proportions `1/3` and `2/5`.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## Hardy's theorem -/

/-- **Hardy's theorem**, in the form stated in `RiemannHypothesis.Partial`. -/
theorem hardyTheorem : HardyTheorem := infinite_criticalLineZeroSet.to_subtype

/-! ## From open windows `(0,T)` to half-open windows `(0,T']` -/

/-- Every zero of `ζ` off the real axis is a nontrivial zero. -/
lemma mem_nontrivialZeroSet_of_im_ne_zero {s : ℂ} (hz : riemannZeta s = 0) (him : s.im ≠ 0) :
    s ∈ nontrivialZeroSet := by
  have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
    rintro ⟨n, rfl⟩
    exact him (by simp)
  exact ⟨hz, (zero_of_nontrivial_mem_strip hz htriv).1,
    (zero_of_nontrivial_mem_strip hz htriv).2⟩

/-- The zeroes of `ζ` with `0 < im ρ < T`. -/
def openWindowZeros (T : ℝ) : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T}

lemma openWindowZeros_subset (T : ℝ) : openWindowZeros T ⊆ windowZeros 0 T := by
  rintro s ⟨hz, him, hlt⟩
  exact ⟨mem_nontrivialZeroSet_of_im_ne_zero hz (ne_of_gt him), him, hlt.le⟩

lemma windowZeros_finite (T₁ T₂ : ℝ) : (windowZeros T₁ T₂).Finite := by
  rw [windowZeros_eq]
  exact Zeta23.zerosIn_finite T₁ T₂

lemma openWindowZeros_finite (T : ℝ) : (openWindowZeros T).Finite :=
  (windowZeros_finite 0 T).subset (openWindowZeros_subset T)

/-- The open window `(0, T)` cuts out exactly the same zeroes as a half-open window
`(0, T']` for some `T' < T`. -/
lemma exists_window_eq_openWindowZeros (T : ℝ) :
    ∃ T' < T, openWindowZeros T = windowZeros 0 T' := by
  rcases (openWindowZeros T).eq_empty_or_nonempty with hemp | hne
  · refine ⟨min 0 (T - 1), lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
    rw [hemp]
    symm
    rw [Set.eq_empty_iff_forall_notMem]
    rintro s ⟨-, hs0, hs1⟩
    exact absurd (hs1.trans (min_le_left _ _)) (not_le.2 hs0)
  · classical
    set F := (openWindowZeros_finite T).toFinset with hF
    have hFne : F.Nonempty := by
      obtain ⟨s, hs⟩ := hne
      exact ⟨s, by rw [hF, Set.Finite.mem_toFinset]; exact hs⟩
    obtain ⟨ρ, hρF, hρmax⟩ := F.exists_max_image (fun s : ℂ => s.im) hFne
    have hρ : ρ ∈ openWindowZeros T := by
      rw [hF, Set.Finite.mem_toFinset] at hρF; exact hρF
    refine ⟨ρ.im, hρ.2.2, ?_⟩
    ext s
    constructor
    · intro hs
      refine ⟨mem_nontrivialZeroSet_of_im_ne_zero hs.1 (ne_of_gt hs.2.1), hs.2.1, ?_⟩
      exact hρmax s (by rw [hF, Set.Finite.mem_toFinset]; exact hs)
    · rintro ⟨⟨hz, -, -⟩, him, hle⟩
      exact ⟨hz, him, lt_of_le_of_lt hle hρ.2.2⟩

lemma zeroCount_eq (T T' : ℝ) (h : openWindowZeros T = windowZeros 0 T') :
    zeroCount T = windowCountDistinct 0 T' := by
  rw [zeroCount, windowCountDistinct, ← h]
  rfl

lemma criticalZeroCount_eq (T T' : ℝ) (h : openWindowZeros T = windowZeros 0 T') :
    criticalZeroCount T = windowCountOnLine 0 T' := by
  rw [criticalZeroCount, windowCountOnLine, ← h]
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, openWindowZeros]
  tauto

/-! ## The counting functions in half-open windows -/

lemma windowCountDistinct_le_windowCount (T₁ T₂ : ℝ) :
    windowCountDistinct T₁ T₂ ≤ windowCount T₁ T₂ := by
  rw [windowCountDistinct_eq, windowCount_eq]
  exact (Zeta23.trivial_chain Zeta23.zetaSeam T₁ T₂).2.2.2.2.2

lemma windowCount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowCount a c = windowCount a b + windowCount b c := by
  simp only [windowCount_eq]
  exact Zeta23.Ncount_add h1 h2

/-- There are zeroes of arbitrarily large ordinate: for every `T₀` there is a nontrivial zero
with `T₀ < im ρ`. -/
lemma exists_zero_im_gt (T₀ : ℝ) : ∃ ρ ∈ nontrivialZeroSet, T₀ < ρ.im := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ T ≥ max T₀ 0, windowCount 0 T = windowCount 0 (max T₀ 0) := by
    intro T hT
    have hmax : (0 : ℝ) ≤ max T₀ 0 := le_max_right _ _
    have hempty : windowZeros (max T₀ 0) T = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro s ⟨hs, hlt, -⟩
      exact absurd (lt_of_le_of_lt (le_max_left _ _) hlt) (not_lt.2 (hcon s hs))
    have hzero : windowCount (max T₀ 0) T = 0 := by simp [windowCount, hempty]
    rw [windowCount_add hmax hT, hzero, Nat.add_zero]
  obtain ⟨T, hT⟩ := (tendsto_windowCount_atTop.eventually_ge_atTop
    ((windowCount 0 (max T₀ 0) : ℝ) + 1)).and (eventually_ge_atTop (max T₀ 0)) |>.exists
  rw [hconst T hT.2] at hT
  linarith [hT.1]

/-! ## Two thirds of the zeroes, in the `Partial.lean` counting functions -/

/-- The two-thirds theorem in the counting functions of `RiemannHypothesis.Partial`:
for every `ε > 0`, eventually `criticalZeroCount T ≥ (2/3 − ε) · zeroCount T`. -/
theorem eventually_twoThirds_criticalZeroCount (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, (2 / 3 - ε) ≤ (criticalZeroCount T : ℝ) / (zeroCount T : ℝ) := by
  rcases le_or_gt (2 / 3 : ℝ) ε with hbig | hsmall
  · filter_upwards with T
    have : (2 : ℝ) / 3 - ε ≤ 0 := by linarith
    exact this.trans (by positivity)
  obtain ⟨T₀, hT₀⟩ := two_thirds_on_critical_line_cumulative ε hε
  obtain ⟨ρ, hρmem, hρim⟩ := exists_zero_im_gt (max T₀ 0)
  filter_upwards [eventually_gt_atTop ρ.im] with T hT
  obtain ⟨T', hT'lt, hT'eq⟩ := exists_window_eq_openWindowZeros T
  -- `ρ` lies in the window `(0, T']`
  have hρT' : ρ ∈ windowZeros 0 T' := by
    rw [← hT'eq]
    exact ⟨hρmem.1, lt_of_le_of_lt (le_max_right T₀ 0) hρim, hT⟩
  have hT'ge : T₀ ≤ T' := le_trans (le_trans (le_max_left T₀ 0) hρim.le) hρT'.2.2
  have hpos : 0 < windowCountDistinct 0 T' := by
    rw [windowCountDistinct, Set.ncard_pos (windowZeros_finite 0 T')]
    exact ⟨ρ, hρT'⟩
  have hposR : (0 : ℝ) < (windowCountDistinct 0 T' : ℝ) := by exact_mod_cast hpos
  have hchain : (2 / 3 - ε) * (windowCountDistinct 0 T' : ℝ) ≤ windowCountOnLine 0 T' := by
    refine le_trans ?_ (hT₀ T' hT'ge)
    have hle : ((windowCountDistinct 0 T' : ℕ) : ℝ) ≤ ((windowCount 0 T' : ℕ) : ℝ) := by
      exact_mod_cast windowCountDistinct_le_windowCount 0 T'
    nlinarith [hle, hsmall]
  rw [zeroCount_eq T T' hT'eq, criticalZeroCount_eq T T' hT'eq, le_div_iff₀ hposR]
  exact hchain

/-- **More than two thirds of the zeroes are on the critical line**, in the counting functions
of `RiemannHypothesis.Partial`: `liminf N₀(T)/N(T) ≥ 2/3`. -/
theorem twoThirds_le_liminf_criticalZeroCount_div :
    (2 / 3 : ℝ) ≤ liminf (fun T : ℝ => (criticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop := by
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun T : ℝ => (criticalZeroCount T : ℝ) / (zeroCount T : ℝ)) := by
    refine IsBoundedUnder.isCoboundedUnder_ge ?_
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with T
    rcases Nat.eq_zero_or_pos (zeroCount T) with h0 | hpos
    · simp [h0]
    · rw [div_le_one (by exact_mod_cast hpos)]
      have : criticalZeroCount T ≤ zeroCount T := by
        refine Set.ncard_le_ncard ?_ ((openWindowZeros_finite T).subset (fun s hs => hs))
        rintro s ⟨hz, -, him, hlt⟩
        exact ⟨hz, him, hlt⟩
      exact_mod_cast this
  refine le_of_forall_sub_le fun ε hε => ?_
  exact le_liminf_of_le hcobdd (eventually_twoThirds_criticalZeroCount ε hε)

/-! ## Selberg, Levinson and Conrey -/

/-- **Selberg's theorem**: a positive proportion of the zeroes lies on the critical line. -/
theorem positiveProportionOnCriticalLine : PositiveProportionOnCriticalLine :=
  lt_of_lt_of_le (by norm_num) twoThirds_le_liminf_criticalZeroCount_div

/-- **Levinson's `1/3`**, as a corollary of the stronger two-thirds bound. -/
theorem oneThirdOnCriticalLine :
    (1 / 3 : ℝ) ≤ liminf (fun T : ℝ => (criticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop :=
  le_trans (by norm_num) twoThirds_le_liminf_criticalZeroCount_div

/-- **Conrey's `2/5`**, as a corollary of the stronger two-thirds bound. -/
theorem twoFifthsOnCriticalLine : TwoFifthsOnCriticalLine :=
  le_trans (by norm_num) twoThirds_le_liminf_criticalZeroCount_div

end RiemannHypothesis

end
