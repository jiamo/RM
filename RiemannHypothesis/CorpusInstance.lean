/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CorpusCeiling
import RiemannHypothesis.SixtySevenPercent
import RiemannHypothesis.RvMCumulative
import RiemannHypothesis.CarlsonDensityPowerSaving
import RiemannHypothesis.OffLineQuadruple
import RiemannHypothesis.ZeroMultiplicityBound
import RiemannHypothesis.ZeroFreeClassical
import RiemannHypothesis.SmallHeight
import RiemannHypothesis.EventualCountingCriterion

/-!
# The corpus of `ζ`: the counting system of `CorpusCeiling` is realized by the zeroes

`RiemannHypothesis/CorpusCeiling.lean` defines the abstract constraint system `ZeroCorpus θ` —
the counting data of the zeroes, with one field for each unconditional fact this repository
proves about them — and shows that everything derivable from the whole system stops at the
proportion `1 − θ` already proved.  Its fields, however, were transcriptions *by hand* of named
theorems of this repository; nothing in Lean checked that the zeroes of `ζ` satisfy them.

This file builds the instance.  `zetaCorpus : ZeroCorpus 0.33` has

* `total T = windowCount 0 T` (all zeroes of `(0, T]`, with multiplicity),
* `distinct T = windowCountDistinct 0 T`,
* `onLine T = windowCountOnLine 0 T`,
* `off T = windowCountOffLine 0 T`,
* `offAt δ T = (offAtSet δ T).ncard`, the off-line zeroes of `(0, T]` at distance at least `δ`
  from the critical line — equal to `(zerosOffCriticalLine δ T).ncard` for every `δ > 0`
  (`ncard_offAtSet_eq` below), which is the counting function the density theorems bound.

Every field is discharged from a theorem of this repository, and the consequences of
`CorpusCeiling` are restated for it.  The point of the exercise is that the non-derivability
results of `CorpusCeiling` become statements about a system that provably holds of `ζ`:
`rh_not_derivable_from_zeta_corpus` says that the corpus of facts formalized here has a model
with a positive proportion of off-line zeroes, so no rearrangement of those facts proves the
Riemann hypothesis.  That is an independence statement relative to the formalized corpus, not
evidence about the conjecture itself.

## Main results

* `RiemannHypothesis.offAtSet` — the counting set of the field `offAt`, and `ncard_offAtSet_eq`,
  its identification with `zerosOffCriticalLine δ T` for `δ > 0`.
* `RiemannHypothesis.windowCountDistinct_add`, `windowCountOnLine_add`, `windowCountOffLine_add`
  — additivity of the three distinct-zero counts over adjacent ordinate windows.
* `RiemannHypothesis.ncard_even_of_criticalReflect` — a finite set of off-line points stable
  under the reflection `ρ ↦ 1 − ρ̄` has even cardinality.
* `RiemannHypothesis.windowCount_le_log_mul_windowCountDistinct` — the cumulative form of the
  `O(log T)` multiplicity bound.
* `RiemannHypothesis.zetaCorpus` — **the instance** `ZeroCorpus 0.33`.
* `RiemannHypothesis.zeta_windowOff_le` — the soundness half, transported to `ζ`.
* `RiemannHypothesis.rh_not_derivable_from_zeta_corpus`,
  `zeta_density_not_sufficient` — the corpus that `ζ` provably satisfies does not entail the
  Riemann hypothesis, and no density bound at a fixed `δ` changes that.

## Scope

Nothing here is evidence for or against the Riemann hypothesis: the content is that a specific,
machine-checked list of facts about the zeroes has models violating it.  A proof of the
conjecture must use a fact outside the list.
-/

noncomputable section

open Complex Set Filter

namespace RiemannHypothesis

/-! ## Additivity of the counting functions over adjacent windows -/

theorem windowZeros_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowZeros a b ∪ windowZeros b c = windowZeros a c := by
  ext ρ
  simp only [windowZeros, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hρ, h3, h4⟩ | ⟨hρ, h3, h4⟩)
    · exact ⟨hρ, h3, le_trans h4 h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 h3, h4⟩
  · rintro ⟨hρ, h3, h4⟩
    rcases le_or_gt ρ.im b with h | h
    · exact Or.inl ⟨hρ, h3, h⟩
    · exact Or.inr ⟨hρ, h, h4⟩

theorem windowZeros_disjoint {a b c : ℝ} : Disjoint (windowZeros a b) (windowZeros b c) := by
  rw [Set.disjoint_left]
  rintro ρ ⟨-, -, h1⟩ ⟨-, h2, -⟩
  exact absurd h2 (not_lt.mpr h1)

/-- Additivity of the distinct-zero count over adjacent ordinate windows. -/
theorem windowCountDistinct_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowCountDistinct a c = windowCountDistinct a b + windowCountDistinct b c := by
  rw [windowCountDistinct, windowCountDistinct, windowCountDistinct, ← windowZeros_union h1 h2,
    Set.ncard_union_eq windowZeros_disjoint (windowZeros_finite a b) (windowZeros_finite b c)]

/-- Additivity of the on-line count over adjacent ordinate windows. -/
theorem windowCountOnLine_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowCountOnLine a c = windowCountOnLine a b + windowCountOnLine b c := by
  rw [windowCountOnLine, windowCountOnLine, windowCountOnLine, ← windowZeros_union h1 h2,
    Set.union_inter_distrib_right]
  refine Set.ncard_union_eq ?_ ((windowZeros_finite a b).subset Set.inter_subset_left)
    ((windowZeros_finite b c).subset Set.inter_subset_left)
  exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left windowZeros_disjoint

/-- Additivity of the off-line count over adjacent ordinate windows. -/
theorem windowCountOffLine_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowCountOffLine a c = windowCountOffLine a b + windowCountOffLine b c := by
  rw [windowCountOffLine, windowCountOffLine, windowCountOffLine, windowZerosOffLine,
    windowZerosOffLine, windowZerosOffLine, ← windowZeros_union h1 h2,
    Set.union_inter_distrib_right]
  refine Set.ncard_union_eq ?_ ((windowZeros_finite a b).subset Set.inter_subset_left)
    ((windowZeros_finite b c).subset Set.inter_subset_left)
  exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left windowZeros_disjoint

theorem windowCountDistinct_mono {a b c : ℝ} (h : b ≤ c) :
    windowCountDistinct a b ≤ windowCountDistinct a c := by
  refine Set.ncard_le_ncard (fun ρ hρ => ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 h⟩)
    (windowZeros_finite a c)

theorem windowCountOffLine_mono {a b c : ℝ} (h : b ≤ c) :
    windowCountOffLine a b ≤ windowCountOffLine a c := by
  refine Set.ncard_le_ncard (fun ρ hρ => ⟨⟨hρ.1.1, hρ.1.2.1, le_trans hρ.1.2.2 h⟩, hρ.2⟩)
    ((windowZeros_finite a c).subset Set.inter_subset_left)

/-- Below the real axis the window is empty. -/
theorem windowZeros_zero_eq_empty {T : ℝ} (hT : T ≤ 0) : windowZeros 0 T = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ρ ⟨-, hpos, hle⟩
  linarith

theorem windowCountDistinct_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    windowCountDistinct 0 T = 0 := by
  rw [windowCountDistinct, windowZeros_zero_eq_empty hT, Set.ncard_empty]

theorem windowCount_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) : windowCount 0 T = 0 := by
  rw [windowCount, windowZeros_zero_eq_empty hT]
  simp

/-! ## The counting set of the field `offAt` -/

/-- The off-line zeroes of ordinate in `(0, T]` at distance at least `δ` from the critical
line. -/
def offAtSet (δ T : ℝ) : Set ℂ := windowZerosOffLine 0 T ∩ {ρ : ℂ | δ ≤ |ρ.re - 1 / 2|}

theorem offAtSet_subset (δ T : ℝ) : offAtSet δ T ⊆ windowZerosOffLine 0 T :=
  Set.inter_subset_left

theorem offAtSet_finite (δ T : ℝ) : (offAtSet δ T).Finite :=
  ((windowZeros_finite 0 T).subset Set.inter_subset_left).subset (offAtSet_subset δ T)

/-- For `δ > 0` the counting set of the field `offAt` is exactly the set the density theorems
of this repository bound. -/
theorem offAtSet_eq_zerosOffCriticalLine {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    offAtSet δ T = zerosOffCriticalLine δ T := by
  ext ρ
  constructor
  · rintro ⟨⟨⟨⟨hz, -, -⟩, hpos, hle⟩, -⟩, hdist⟩
    exact ⟨hz, hdist, hpos, hle⟩
  · rintro ⟨hz, hdist, hpos, hle⟩
    have hstrip := mem_strip_of_zero_of_im_pos hz hpos
    have hne : ρ.re ≠ 1 / 2 := by
      intro hre
      rw [hre] at hdist
      simp only [sub_self, abs_zero] at hdist
      linarith
    exact ⟨⟨⟨⟨hz, hstrip.1, hstrip.2⟩, hpos, hle⟩, hne⟩, hdist⟩

theorem ncard_offAtSet_eq {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    (offAtSet δ T).ncard = (zerosOffCriticalLine δ T).ncard := by
  rw [offAtSet_eq_zerosOffCriticalLine hδ]

theorem offAtSet_antitone {δ δ' : ℝ} (h : δ ≤ δ') (T : ℝ) : offAtSet δ' T ⊆ offAtSet δ T :=
  fun _ hρ => ⟨hρ.1, le_trans h hρ.2⟩

theorem offAtSet_mono {T T' : ℝ} (h : T ≤ T') (δ : ℝ) : offAtSet δ T ⊆ offAtSet δ T' :=
  fun _ hρ => ⟨⟨⟨hρ.1.1.1, hρ.1.1.2.1, le_trans hρ.1.1.2.2 h⟩, hρ.1.2⟩, hρ.2⟩

/-! ## Evenness from the reflection in the critical line -/

/-- A finite set of points off the critical line that is stable under the reflection
`ρ ↦ 1 − ρ̄` has an even number of elements: the reflection is an involution without fixed
points, and it exchanges the two sides of the line. -/
theorem ncard_even_of_criticalReflect {S : Set ℂ} (hfin : S.Finite)
    (hmaps : ∀ s ∈ S, criticalReflect s ∈ S) (hne : ∀ s ∈ S, s.re ≠ 1 / 2) :
    ∃ k : ℕ, S.ncard = 2 * k := by
  classical
  set L : Set ℂ := {s ∈ S | s.re < 1 / 2} with hL
  set R : Set ℂ := {s ∈ S | 1 / 2 < s.re} with hR
  have himage : criticalReflect '' L = R := by
    ext s
    constructor
    · rintro ⟨t, ⟨htS, htlt⟩, rfl⟩
      exact ⟨hmaps t htS, by simp only [criticalReflect_re]; linarith⟩
    · rintro ⟨hsS, hslt⟩
      refine ⟨criticalReflect s, ⟨hmaps s hsS, ?_⟩, criticalReflect_criticalReflect s⟩
      simp only [criticalReflect_re]; linarith
  have hcard : R.ncard = L.ncard := by
    rw [← himage, Set.ncard_image_of_injective _ criticalReflect_injective]
  have hunion : L ∪ R = S := by
    ext s
    constructor
    · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
    · intro hs
      rcases lt_trichotomy s.re (1 / 2) with h | h | h
      · exact Or.inl ⟨hs, h⟩
      · exact absurd h (hne s hs)
      · exact Or.inr ⟨hs, h⟩
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    rintro s ⟨-, h1⟩ ⟨-, h2⟩
    linarith
  refine ⟨L.ncard, ?_⟩
  rw [← hunion, Set.ncard_union_eq hdisj (hfin.subset (fun s hs => hs.1))
    (hfin.subset (fun s hs => hs.1)), hcard]
  ring

theorem criticalReflect_mem_windowZerosOffLine {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ windowZerosOffLine 0 T) : criticalReflect ρ ∈ windowZerosOffLine 0 T := by
  obtain ⟨⟨⟨hz, h0, h1⟩, hpos, hle⟩, hne⟩ := hρ
  have hmem : ρ ∈ nontrivialZeros T := ⟨hz, h0, h1, by rw [abs_of_pos hpos]; exact hle⟩
  obtain ⟨hz', h0', h1', -⟩ := criticalReflect_mem_nontrivialZeros hmem
  refine ⟨⟨⟨hz', h0', h1'⟩, ?_, ?_⟩, ?_⟩
  · simpa using hpos
  · simpa using hle
  · simp only [criticalReflect_re, Set.mem_ofPred_eq]
    intro h
    exact hne (by linarith)

/-- The off-line zeroes of a window come in pairs. -/
theorem exists_windowCountOffLine_eq_two_mul (T : ℝ) :
    ∃ k : ℕ, windowCountOffLine 0 T = 2 * k :=
  ncard_even_of_criticalReflect ((windowZeros_finite 0 T).subset Set.inter_subset_left)
    (fun _ hs => criticalReflect_mem_windowZerosOffLine hs) (fun _ hs => hs.2)

/-- The same for the zeroes at distance at least `δ`: the reflection preserves the distance to
the critical line. -/
theorem exists_ncard_offAtSet_eq_two_mul (δ T : ℝ) :
    ∃ k : ℕ, (offAtSet δ T).ncard = 2 * k := by
  refine ncard_even_of_criticalReflect (offAtSet_finite δ T) (fun s hs => ?_) (fun s hs => hs.1.2)
  refine ⟨criticalReflect_mem_windowZerosOffLine hs.1, ?_⟩
  have := hs.2
  simp only [criticalReflect_re, Set.mem_ofPred_eq] at *
  rw [show (1 : ℝ) - s.re - 1 / 2 = -(s.re - 1 / 2) by ring, abs_neg]
  exact this

/-! ## The cumulative multiplicity bound -/

/-- **The cumulative `O(log T)` multiplicity bound**: the count with multiplicity is at most a
constant times `log T` times the distinct count. -/
theorem windowCount_le_log_mul_windowCountDistinct :
    ∃ C : ℝ, 0 < C ∧ ∃ T₂ : ℝ, ∀ T ≥ T₂,
      (windowCount 0 T : ℝ) ≤ C * Real.log T * (windowCountDistinct 0 T : ℝ) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_zeroMultiplicity_bound_low
  refine ⟨41 + K, by linarith, 25, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    have h3 : Real.exp 1 ≤ T := le_trans (le_of_lt (by linarith [Real.exp_one_lt_d9])) hT
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) h3
  have hfin := windowZeros_finite 0 T
  set F : Finset ℂ := hfin.toFinset with hF
  -- every zero of the window has multiplicity at most `(41 + K) log T`
  have hbound : ∀ ρ ∈ F, (zeroMultiplicity ρ : ℝ) ≤ (41 + K) * Real.log T := by
    intro ρ hρF
    obtain ⟨hρ, hpos, hle⟩ := (Set.Finite.mem_toFinset hfin).1 hρF
    have habs : |ρ.im| = ρ.im := abs_of_pos hpos
    rcases le_or_gt 25 |ρ.im| with him | him
    · have h1 := zeroMultiplicity_le_log_abs_im hρ him
      have h2 : Real.log |ρ.im| ≤ Real.log T := by
        rw [habs]
        exact Real.log_le_log hpos hle
      have hlognn : (0 : ℝ) ≤ Real.log T := by linarith
      nlinarith [hK0]
    · have h1 := hK ρ hρ him.le
      nlinarith [hK0]
  have hsum : (windowCount 0 T : ℝ) = ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) := by
    rw [windowCount, finsum_mem_eq_finite_toFinset_sum _ hfin, ← hF]
    push_cast
    rfl
  have hcard : (windowCountDistinct 0 T : ℝ) = (F.card : ℝ) := by
    rw [windowCountDistinct, Set.ncard_eq_toFinset_card _ hfin, ← hF]
  rw [hsum, hcard]
  calc ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) ≤ ∑ _ρ ∈ F, (41 + K) * Real.log T :=
        Finset.sum_le_sum hbound
    _ = (41 + K) * Real.log T * (F.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## The zero-free region in counting form -/

/-- **The classical zero-free region in counting form**: for large `T` there is no zero of
ordinate in `(0, T]` at distance `1/2 − c/log T` or more from the critical line. -/
theorem exists_offAtSet_eq_empty :
    ∃ c : ℝ, 0 < c ∧ ∃ T₃ : ℝ, ∀ T ≥ T₃, ∀ δ : ℝ,
      1 / 2 - c / Real.log T ≤ δ → offAtSet δ T = ∅ := by
  obtain ⟨c, hc0, hc⟩ := zeroFreeRegion
  refine ⟨c / 2, by linarith, 3, fun T hT δ hδ => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  -- a zero of the window at distance at least `1/2 - (c/2)/log T` from the line is impossible
  have hkey : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T →
      1 - (c / 2) / Real.log T ≤ ρ.re → False := by
    intro ρ hz h0 h1 hpos hle hre
    rcases lt_or_ge ρ.im 3 with him | him
    · exact riemannZeta_ne_zero_of_abs_im_le h0 h1 (by rw [abs_of_pos hpos]; linarith) hz
    · have habs : |ρ.im| = ρ.im := abs_of_pos hpos
      have hlogim : 0 < Real.log |ρ.im| := by
        rw [habs]; exact Real.log_pos (by linarith)
      have hmono : Real.log |ρ.im| ≤ Real.log T := by
        rw [habs]; exact Real.log_le_log hpos hle
      have hdiv : c / Real.log T ≤ c / Real.log |ρ.im| :=
        div_le_div_of_nonneg_left hc0.le hlogim hmono
      have hhalf : (c / 2) / Real.log T < c / Real.log T := by
        rw [div_lt_div_iff_of_pos_right hlogT]; linarith
      have : 1 - c / Real.log |ρ.im| < ρ.re := by linarith
      exact hc ρ (by rw [habs]; linarith) this hz
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ρ ⟨⟨⟨⟨hz, h0, h1⟩, hpos, hle⟩, -⟩, hdist⟩
  have hd : 1 / 2 - (c / 2) / Real.log T ≤ |ρ.re - 1 / 2| := le_trans hδ hdist
  rcases abs_cases (ρ.re - 1 / 2) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he] at hd
    exact hkey ρ hz h0 h1 hpos hle (by linarith)
  · -- reflect in the critical line: the reflected point is a zero to the right of it
    rw [he] at hd
    have hmem : ρ ∈ nontrivialZeros T := ⟨hz, h0, h1, by rw [abs_of_pos hpos]; exact hle⟩
    obtain ⟨hz', h0', h1', -⟩ := criticalReflect_mem_nontrivialZeros hmem
    have hpos' : 0 < (criticalReflect ρ).im := by simpa using hpos
    have hle' : (criticalReflect ρ).im ≤ T := by simpa using hle
    have hre' : 1 - (c / 2) / Real.log T ≤ (criticalReflect ρ).re := by
      simp only [criticalReflect_re]
      linarith
    exact hkey (criticalReflect ρ) hz' h0' h1' hpos' hle' hre'

/-! ## The off-line count is attained at a positive distance -/

theorem exists_ncard_offAtSet_eq_windowCountOffLine (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ (offAtSet δ T).ncard = windowCountOffLine 0 T := by
  classical
  have hfin : (windowZerosOffLine 0 T).Finite :=
    (windowZeros_finite 0 T).subset Set.inter_subset_left
  rcases Set.eq_empty_or_nonempty (windowZerosOffLine 0 T) with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    have hsub : offAtSet 1 T = ∅ := Set.subset_eq_empty (offAtSet_subset 1 T) hemp
    rw [hsub, Set.ncard_empty, windowCountOffLine, hemp, Set.ncard_empty]
  · set F : Finset ℂ := hfin.toFinset with hF
    have hFne : F.Nonempty := by
      obtain ⟨ρ, hρ⟩ := hne
      exact ⟨ρ, (Set.Finite.mem_toFinset hfin).2 hρ⟩
    set δ : ℝ := F.inf' hFne (fun ρ => |ρ.re - 1 / 2|) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef, Finset.lt_inf'_iff]
      intro ρ hρ
      have hρ' := (Set.Finite.mem_toFinset hfin).1 hρ
      exact abs_pos.mpr (sub_ne_zero.mpr hρ'.2)
    refine ⟨δ, hδpos, ?_⟩
    have hset : offAtSet δ T = windowZerosOffLine 0 T := by
      refine Set.Subset.antisymm (offAtSet_subset δ T) fun ρ hρ => ?_
      refine ⟨hρ, ?_⟩
      change δ ≤ |ρ.re - 1 / 2|
      exact Finset.inf'_le (fun ρ => |ρ.re - 1 / 2|) ((Set.Finite.mem_toFinset hfin).2 hρ)
    rw [hset, windowCountOffLine]

/-! ## The instance -/

/-- **The corpus of `ζ`.**  Every field is discharged from a theorem of this repository. -/
def zetaCorpus : ZeroCorpus 0.33 where
  total T := (windowCount 0 T : ℝ)
  distinct T := (windowCountDistinct 0 T : ℝ)
  onLine T := (windowCountOnLine 0 T : ℝ)
  off T := (windowCountOffLine 0 T : ℝ)
  offAt δ T := ((offAtSet δ T).ncard : ℝ)
  total_nonneg T := by positivity
  off_nonneg T := by positivity
  onLine_nonneg T := by positivity
  split T := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountOffLine_add_windowCountOnLine 0 T)
  distinct_le_total T := by
    exact_mod_cast windowCountDistinct_le_windowCount 0 T
  distinct_window_le T₁ T₂ h := by
    rcases le_or_gt T₁ 0 with hT₁ | hT₁
    · rw [windowCountDistinct_zero_of_nonpos hT₁, windowCount_zero_of_nonpos hT₁]
      have := windowCountDistinct_le_windowCount 0 T₂
      have : (windowCountDistinct 0 T₂ : ℝ) ≤ (windowCount 0 T₂ : ℝ) := by exact_mod_cast this
      simpa using this
    · have hd := windowCountDistinct_add hT₁.le h
      have ht := windowCount_add hT₁.le h
      have hle := windowCountDistinct_le_windowCount T₁ T₂
      have hd' : (windowCountDistinct 0 T₂ : ℝ)
          = (windowCountDistinct 0 T₁ : ℝ) + (windowCountDistinct T₁ T₂ : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hd
      have ht' : (windowCount 0 T₂ : ℝ) = (windowCount 0 T₁ : ℝ) + (windowCount T₁ T₂ : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) ht
      have hle' : (windowCountDistinct T₁ T₂ : ℝ) ≤ (windowCount T₁ T₂ : ℝ) := by
        exact_mod_cast hle
      rw [hd', ht']
      linarith
  total_mono := by
    intro a b hab
    have h : ((windowCount 0 a : ℕ) : ℝ) ≤ ((windowCount 0 b : ℕ) : ℝ) := by
      exact_mod_cast windowCount_mono (a := 0) (b := a) (c := 0) (d := b) le_rfl hab
    exact h
  off_mono := by
    intro a b hab
    have h : ((windowCountOffLine 0 a : ℕ) : ℝ) ≤ ((windowCountOffLine 0 b : ℕ) : ℝ) := by
      exact_mod_cast windowCountOffLine_mono (a := 0) hab
    exact h
  offAt_mono δ := by
    intro a b hab
    have h : (((offAtSet δ a).ncard : ℕ) : ℝ) ≤ (((offAtSet δ b).ncard : ℕ) : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (offAtSet_mono hab δ) (offAtSet_finite δ b)
    exact h
  offAt_nonneg δ T := by positivity
  offAt_le_off δ T := by
    exact_mod_cast Set.ncard_le_ncard (offAtSet_subset δ T)
      ((windowZeros_finite 0 T).subset Set.inter_subset_left)
  offAt_antitone δ δ' T hδ hle := by
    exact_mod_cast Set.ncard_le_ncard (offAtSet_antitone hle T) (offAtSet_finite δ T)
  window_onLine := by
    obtain ⟨T₀, hT₀⟩ := sixty_seven_percent_on_critical_line
    refine ⟨max T₀ 0, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
    have hTT : T ≤ 2 * T := by linarith
    have h67 := hT₀ T (le_trans (le_max_left _ _) hT)
    have ht : (windowCount 0 (2 * T) : ℝ)
        = (windowCount 0 T : ℝ) + (windowCount T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCount_add hT0 hTT)
    have ho : (windowCountOnLine 0 (2 * T) : ℝ)
        = (windowCountOnLine 0 T : ℝ) + (windowCountOnLine T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountOnLine_add hT0 hTT)
    rw [ht, ho]
    have hcoe : (1 : ℝ) - 0.33 = 0.67 := by norm_num
    rw [hcoe]
    linarith
  rvm := by
    obtain ⟨A, hA0, T₁, hA⟩ := exists_abs_windowCount_zero_sub_main_le
    exact ⟨A, hA0, T₁, fun T hT => hA T hT⟩
  density δ hδ0 hδ1 := by
    obtain ⟨c, C, hc0, hc1, hC0, hbd⟩ := exists_ncard_zerosOffCriticalLine_le_rpow hδ0 hδ1
    refine ⟨c, C, hc0, hc1, hC0, fun T hT => ?_⟩
    rw [ncard_offAtSet_eq hδ0]
    exact hbd T hT
  off_even T := by
    obtain ⟨k, hk⟩ := exists_windowCountOffLine_eq_two_mul T
    exact ⟨k, by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hk⟩
  offAt_even δ T := by
    obtain ⟨k, hk⟩ := exists_ncard_offAtSet_eq_two_mul δ T
    exact ⟨k, by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hk⟩
  mult := by
    obtain ⟨C, hC0, T₂, hC⟩ := windowCount_le_log_mul_windowCountDistinct
    exact ⟨C, hC0, T₂, fun T hT => hC T hT⟩
  zeroFree := by
    obtain ⟨c, hc0, T₃, hc⟩ := exists_offAtSet_eq_empty
    refine ⟨c, hc0, T₃, fun T hT δ hδ => ?_⟩
    rw [hc T hT δ hδ, Set.ncard_empty]
    norm_num
  off_attained T := by
    obtain ⟨δ, hδ, hcard⟩ := exists_ncard_offAtSet_eq_windowCountOffLine T
    exact ⟨δ, hδ, by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcard⟩

/-! ## The consequences of `CorpusCeiling`, restated for `ζ` -/

/-- **Soundness, for `ζ`.**  The abstract bound `ZeroCorpus.windowOff_le`, unfolded: for all
large `T` at most `33 %` of the zeroes of the dyadic window `(T, 2T]` lie off the critical
line. -/
theorem zeta_windowOff_le : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (windowCountOffLine T (2 * T) : ℝ) ≤ 0.33 * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := zetaCorpus.windowOff_le
  refine ⟨max T₀ 0, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTT : T ≤ 2 * T := by linarith
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  have hoff : (windowCountOffLine 0 (2 * T) : ℝ)
      = (windowCountOffLine 0 T : ℝ) + (windowCountOffLine T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountOffLine_add hT0 hTT)
  have htot : (windowCount 0 (2 * T) : ℝ)
      = (windowCount 0 T : ℝ) + (windowCount T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCount_add hT0 hTT)
  simp only [ZeroCorpus.windowOff, ZeroCorpus.windowTotal, zetaCorpus] at h
  rw [hoff, htot] at h
  linarith

/-- **The Riemann hypothesis is exactly the vanishing of the off-line count of the corpus of
`ζ`.** -/
theorem zetaStripForm_iff_rhCounts_zetaCorpus : ZetaStripForm ↔ RHCounts zetaCorpus := by
  constructor
  · intro h T
    have hempty : windowZerosOffLine 0 T = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ρ ⟨⟨⟨hz, h0, h1⟩, -, -⟩, hne⟩
      exact hne (h ρ h0 h1 hz)
    change ((windowCountOffLine 0 T : ℕ) : ℝ) = 0
    rw [windowCountOffLine, hempty, Set.ncard_empty]
    norm_num
  · intro h
    by_contra hRH
    obtain ⟨ρ, hz, h0, h1, hre, him⟩ := exists_offLine_pos_im_of_not_zetaStripForm hRH
    have hmem : ρ ∈ windowZerosOffLine 0 ρ.im := ⟨⟨⟨hz, h0, h1⟩, him, le_rfl⟩, hre⟩
    have hfin : (windowZerosOffLine 0 ρ.im).Finite :=
      (windowZeros_finite 0 ρ.im).subset Set.inter_subset_left
    have hpos : 0 < windowCountOffLine 0 ρ.im :=
      (Set.ncard_pos hfin).2 ⟨ρ, hmem⟩
    have h0' := h ρ.im
    have : ((windowCountOffLine 0 ρ.im : ℕ) : ℝ) = 0 := h0'
    have : windowCountOffLine 0 ρ.im = 0 := by exact_mod_cast this
    omega

/-- **The Riemann hypothesis is not derivable from the corpus that `ζ` provably satisfies.**
The zeroes of `ζ` are a model of `ZeroCorpus 0.33` (`zetaCorpus`), and there is another model of
the very same list of facts whose off-line count is not identically zero; so no argument that
uses only those facts can prove the Riemann hypothesis.  This says nothing about the truth of
the conjecture: it delimits what the formalized corpus entails. -/
theorem rh_not_derivable_from_zeta_corpus :
    (∃ Z : ZeroCorpus 0.33, ¬ RHCounts Z) ∧ (ZetaStripForm ↔ RHCounts zetaCorpus) := by
  refine ⟨?_, zetaStripForm_iff_rhCounts_zetaCorpus⟩
  by_contra hcon
  push Not at hcon
  exact rh_not_derivable_from_corpus hcon

/-- **No density theorem at a fixed distance closes the gap**, restated against the instance:
the corpus of facts that `ζ` satisfies has a model in which, for every fixed `δ > 0`, the count
at distance at least `δ` is bounded in `T` — stronger than any density estimate — and in which
the Riemann hypothesis fails. -/
theorem zeta_density_not_sufficient :
    ∃ Z : ZeroCorpus 0.33, (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, Z.offAt δ T ≤ C) ∧
      ¬ RHCounts Z :=
  density_not_sufficient

end RiemannHypothesis
