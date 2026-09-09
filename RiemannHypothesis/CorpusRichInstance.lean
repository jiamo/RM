/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CorpusRich
import RiemannHypothesis.CorpusInstance
import RiemannHypothesis.ZeroMultiplicityBound

/-!
# The thicker corpus of `ζ`

`RiemannHypothesis/CorpusRich.lean` enlarges the constraint system `ZeroCorpus` by four further
unconditional facts and shows that its ceiling is unchanged.  This file builds the instance:
the zeroes of `ζ` satisfy the enlarged system, so the independence statement of `CorpusRich` is
a statement about a list of facts that provably holds of `ζ`.

`zetaRichCorpus : RichZeroCorpus 0.33` extends `zetaCorpus` by

* `simpleOnLine T = windowCountSimpleOnLine 0 T`, the zeroes of `(0, T]` that are simple and on
  the critical line, with the `67 %` proportion of
  `sixty_seven_percent_simple_on_critical_line`;
* `distinct_ratio`, Theorem C (`five_sixths_distinct`): at least `5/6 − ε` of the zeroes of a
  dyadic window, counted with multiplicity, are distinct;
* `localCount`, the local Riemann–von Mangoldt bound of
  `sum_zeroMultiplicity_zerosNearHeight_le`: a unit window carries at most `41 log T` zeroes,
  with multiplicity;
* `strip`: no nontrivial zero is at distance `1/2` or more from the critical line.

## Main results

* `RiemannHypothesis.windowCountSimpleOnLine_add` — additivity of the simple-on-line count over
  adjacent ordinate windows.
* `RiemannHypothesis.windowCount_unit_window_le` — the local count `N(T, T+1) ≤ 41 log T`.
* `RiemannHypothesis.zetaRichCorpus` — **the instance**.
* `RiemannHypothesis.rh_not_derivable_from_zeta_rich_corpus` — the thicker corpus, which `ζ`
  provably satisfies, still does not entail the Riemann hypothesis.

## Scope

As in `CorpusInstance`, this says nothing about the truth of the conjecture: it delimits what
the formalized facts entail.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## Additivity of the simple-on-line count -/

/-- Additivity of the simple-on-line count over adjacent ordinate windows. -/
theorem windowCountSimpleOnLine_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    windowCountSimpleOnLine a c = windowCountSimpleOnLine a b + windowCountSimpleOnLine b c := by
  have hfin : ∀ x y : ℝ, (windowZeros x y ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | zeroMultiplicity ρ = 1}).Finite := fun x y =>
    (windowZeros_finite x y).subset (fun _ hρ => hρ.1.1)
  rw [windowCountSimpleOnLine, windowCountSimpleOnLine, windowCountSimpleOnLine,
    ← windowZeros_union h1 h2, Set.union_inter_distrib_right, Set.union_inter_distrib_right]
  refine Set.ncard_union_eq ?_ (hfin a b) (hfin b c)
  exact Set.disjoint_of_subset (fun _ hρ => hρ.1.1) (fun _ hρ => hρ.1.1) windowZeros_disjoint

/-! ## The local Riemann–von Mangoldt bound in the window vocabulary -/

/-- The zeroes of a unit window are zeroes near the corresponding height. -/
theorem windowZeros_subset_zerosNearHeight (T : ℝ) :
    windowZeros T (T + 1) ⊆ zerosNearHeight T := by
  rintro ρ ⟨⟨hz, h0, h1⟩, hlo, hhi⟩
  refine ⟨hz, h0, h1, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- **The local count.**  A unit window carries at most `41 log T` zeroes, with multiplicity. -/
theorem windowCount_unit_window_le {T : ℝ} (hT : 25 ≤ T) :
    (windowCount T (T + 1) : ℝ) ≤ 41 * Real.log T := by
  classical
  have hfinNear : (zerosNearHeight T).Finite := finite_zerosNearHeight hT
  have hfinWin : (windowZeros T (T + 1)).Finite := windowZeros_finite _ _
  have hsub : windowZeros T (T + 1) ⊆ zerosNearHeight T := windowZeros_subset_zerosNearHeight T
  have hle : windowCount T (T + 1) ≤ ∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ := by
    rw [windowCount, finsum_mem_eq_finite_toFinset_sum _ hfinWin,
      finsum_mem_eq_finite_toFinset_sum _ hfinNear]
    refine Finset.sum_le_sum_of_subset ?_
    intro ρ hρ
    exact (Set.Finite.mem_toFinset hfinNear).2 (hsub ((Set.Finite.mem_toFinset hfinWin).1 hρ))
  have hbound := sum_zeroMultiplicity_zerosNearHeight_le hT
  have hcast : (windowCount T (T + 1) : ℝ)
      ≤ ((∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ : ℕ) : ℝ) := by exact_mod_cast hle
  linarith

/-! ## The zeroes lie in the open critical strip -/

/-- No nontrivial zero is at distance `1/2` or more from the critical line. -/
theorem offAtSet_half_eq_empty (T : ℝ) : offAtSet (1 / 2) T = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ρ ⟨⟨⟨⟨-, h0, h1⟩, -, -⟩, -⟩, hdist⟩
  have hlt : |ρ.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hge : (1 : ℝ) / 2 ≤ |ρ.re - 1 / 2| := hdist
  linarith

/-! ## The instance -/

/-- **The thicker corpus of `ζ`.**  Every field is discharged from a theorem of this
repository. -/
def zetaRichCorpus : RichZeroCorpus 0.33 where
  toZeroCorpus := zetaCorpus
  simpleOnLine T := (windowCountSimpleOnLine 0 T : ℝ)
  simpleOnLine_nonneg T := by positivity
  simpleOnLine_le_onLine T := by
    have hsub : windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩ {ρ : ℂ | zeroMultiplicity ρ = 1}
        ⊆ windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} := fun _ hρ => hρ.1
    have hfin : (windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}).Finite :=
      (windowZeros_finite 0 T).subset Set.inter_subset_left
    have hle : windowCountSimpleOnLine 0 T ≤ windowCountOnLine 0 T :=
      Set.ncard_le_ncard hsub hfin
    change ((windowCountSimpleOnLine 0 T : ℕ) : ℝ) ≤ ((windowCountOnLine 0 T : ℕ) : ℝ)
    exact_mod_cast hle
  window_simpleOnLine := by
    obtain ⟨T₀, hT₀⟩ := sixty_seven_percent_simple_on_critical_line
    refine ⟨max T₀ 0, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
    have hTT : T ≤ 2 * T := by linarith
    have h67 := hT₀ T (le_trans (le_max_left _ _) hT)
    have ht : (windowCount 0 (2 * T) : ℝ)
        = (windowCount 0 T : ℝ) + (windowCount T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCount_add hT0 hTT)
    have hs : (windowCountSimpleOnLine 0 (2 * T) : ℝ)
        = (windowCountSimpleOnLine 0 T : ℝ) + (windowCountSimpleOnLine T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountSimpleOnLine_add hT0 hTT)
    change (1 - 0.33) * ((windowCount 0 (2 * T) : ℝ) - (windowCount 0 T : ℝ))
      ≤ (windowCountSimpleOnLine 0 (2 * T) : ℝ) - (windowCountSimpleOnLine 0 T : ℝ)
    rw [ht, hs, show (1 : ℝ) - 0.33 = 0.67 by norm_num]
    linarith
  distinct_ratio := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := five_sixths_distinct ε hε
    refine ⟨max T₀ 0, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
    have hTT : T ≤ 2 * T := by linarith
    have h := hT₀ T (le_trans (le_max_left _ _) hT)
    have ht : (windowCount 0 (2 * T) : ℝ)
        = (windowCount 0 T : ℝ) + (windowCount T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCount_add hT0 hTT)
    have hd : (windowCountDistinct 0 (2 * T) : ℝ)
        = (windowCountDistinct 0 T : ℝ) + (windowCountDistinct T (2 * T) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountDistinct_add hT0 hTT)
    change (5 / 6 - ε) * ((windowCount 0 (2 * T) : ℝ) - (windowCount 0 T : ℝ))
      ≤ (windowCountDistinct 0 (2 * T) : ℝ) - (windowCountDistinct 0 T : ℝ)
    rw [ht, hd]
    linarith
  localCount := by
    refine ⟨41, by norm_num, 25, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have hTT : T ≤ T + 1 := by linarith
    have ht : (windowCount 0 (T + 1) : ℝ)
        = (windowCount 0 T : ℝ) + (windowCount T (T + 1) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCount_add hT0 hTT)
    have hloc := windowCount_unit_window_le hT
    change (windowCount 0 (T + 1) : ℝ) - (windowCount 0 T : ℝ) ≤ 41 * Real.log T
    rw [ht]
    linarith
  strip := by
    intro T
    change (((offAtSet (1 / 2) T).ncard : ℕ) : ℝ) = 0
    rw [offAtSet_half_eq_empty T, Set.ncard_empty]
    norm_num

@[simp] lemma zetaRichCorpus_toZeroCorpus : zetaRichCorpus.toZeroCorpus = zetaCorpus := rfl

/-! ## The consequences, restated for `ζ` -/

/-- **The Riemann hypothesis is not derivable from the thicker corpus that `ζ` provably
satisfies.**  The zeroes of `ζ` are a model of `RichZeroCorpus 0.33`, and the enlarged list of
facts — the simple-zero count with its `67 %`, Theorem C, the local Riemann–von Mangoldt bound
and the critical strip, on top of everything in `ZeroCorpus` — has another model whose off-line
count is not identically zero. -/
theorem rh_not_derivable_from_zeta_rich_corpus :
    (∃ Z : RichZeroCorpus 0.33, ¬ RHCounts Z.toZeroCorpus) ∧
      (ZetaStripForm ↔ RHCounts zetaRichCorpus.toZeroCorpus) := by
  refine ⟨?_, zetaStripForm_iff_rhCounts_zetaCorpus⟩
  by_contra hcon
  push Not at hcon
  exact rh_not_derivable_from_rich_corpus hcon

/-- **The ceiling of the thicker corpus of `ζ`**: `67 %` on the critical line is derivable from
it, and nothing beyond `67 %` is. -/
theorem zeta_rich_corpus_window_ceiling {p : ℝ} :
    (∀ Z : RichZeroCorpus 0.33, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        p * Z.toZeroCorpus.windowTotal T ≤ Z.toZeroCorpus.windowOn T) ↔ p ≤ 0.67 := by
  have h := rich_corpus_window_ceiling (θ := 0.33) (p := p) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 0.33 = 0.67 by norm_num] at h
  exact h

end RiemannHypothesis
