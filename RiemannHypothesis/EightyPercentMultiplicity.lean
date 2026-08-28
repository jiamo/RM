/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SpeiserMultiple

/-!
# Past eighty per cent on the critical line, counted with multiplicity

`RiemannHypothesis.EightyPercentRoute` bounds the number of **distinct** nontrivial zeroes of
`ζ` off the critical line by the `ξ′` bad count, under the unproved counting form of Speiser's
theorem (`SpeiserTransfer`), and deduces `84 %` for the distinct zeroes and `70 %` for the
zeroes counted with multiplicity.  The `70 %` loss came from the multiplicity budget
`N_d ≥ (5/6)·N`, which was needed because the transfer was stated for *distinct* zeroes only.

This file removes that loss.  Two things are done.

* The counting functions of the window are split **with multiplicity** into their on-line and
  off-line parts, `windowCountOnLineMult` and `windowCountOffLineMult`, and the off-line part
  is decomposed as `N_off + (multiplicity excess of the off-line zeroes)`
  (`windowCountOffLineMult_eq`).  Since the excess is bounded *unconditionally* by the `ξ′` bad
  count (`RiemannHypothesis.windowMultipleOffLineExcess_le_bad`), the distinct-zero transfer
  already gives `73.7 %` on the critical line with multiplicity
  (`seventy_three_percent_on_critical_line_mult_of_speiserTransfer`), improving the `70 %` of
  `RiemannHypothesis.EightyPercentRoute`.

* The classical Levinson–Montgomery statement is a statement about zeroes counted **with
  multiplicity**; `SpeiserTransfer` is its weakening to distinct points.  Here the faithful
  multiplicity-weighted form is recorded as `SpeiserTransferMult`, again a `def … : Prop` that
  is **not proved** in this repository, and it is shown to imply `SpeiserTransfer`
  (`speiserTransfer_of_speiserTransferMult`).  Under it the whole `13.136 %` budget of the `ξ′`
  theorem is spent once, not twice, and the conclusion is
  `eighty_six_percent_on_critical_line_mult_of_speiserTransferMult`: at least `86.864 %` of the
  nontrivial zeroes of `ζ`, counted with multiplicity, lie on the critical line — in
  particular the eighty per cent target with multiplicity,
  `EightyPercentOnCriticalLineMult`, is reached on this route
  (`eightyPercentOnCriticalLineMult_of_speiserTransferMult`), which
  `RiemannHypothesis.EightyPercentRoute` could not do.

Nothing here proves `SpeiserTransfer`, `SpeiserTransferMult`, or the Riemann hypothesis, and
the unconditional proportion on the critical line is unchanged at `2/3`.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## Splitting the window count, with multiplicity, along the critical line -/

/-- The nontrivial zeroes of `ζ` with ordinate in `(T₁, T₂]` that lie *on* the critical line. -/
def windowZerosOnLine (T₁ T₂ : ℝ) : Set ℂ := windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}

lemma windowCountOnLine_eq_ncard (T₁ T₂ : ℝ) :
    windowCountOnLine T₁ T₂ = (windowZerosOnLine T₁ T₂).ncard := rfl

lemma windowZerosOnLine_finite (T₁ T₂ : ℝ) : (windowZerosOnLine T₁ T₂).Finite :=
  (windowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1

lemma windowZerosOffLine_finite (T₁ T₂ : ℝ) : (windowZerosOffLine T₁ T₂).Finite :=
  (windowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1

/-- `N₀ᵐ(T₁,T₂)`: the nontrivial zeroes of `ζ` on the critical line in the window, counted
**with multiplicity**. -/
def windowCountOnLineMult (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ windowZerosOnLine T₁ T₂, zeroMultiplicity ρ

/-- `N_offᵐ(T₁,T₂)`: the nontrivial zeroes of `ζ` off the critical line in the window, counted
**with multiplicity**. -/
def windowCountOffLineMult (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ windowZerosOffLine T₁ T₂, zeroMultiplicity ρ

lemma windowZerosOffLine_union_onLine (T₁ T₂ : ℝ) :
    windowZerosOffLine T₁ T₂ ∪ windowZerosOnLine T₁ T₂ = windowZeros T₁ T₂ := by
  ext ρ
  simp only [windowZerosOffLine, windowZerosOnLine, Set.mem_union, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
  · intro hs
    by_cases h : ρ.re = 1 / 2
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨hs, h⟩

lemma windowZerosOffLine_disjoint_onLine (T₁ T₂ : ℝ) :
    Disjoint (windowZerosOffLine T₁ T₂) (windowZerosOnLine T₁ T₂) :=
  Set.disjoint_left.2 fun _ hs hs' => hs.2 hs'.2

/-- **The window count splits, with multiplicity, into its off-line and on-line parts.** -/
lemma windowCountOffLineMult_add_windowCountOnLineMult (T₁ T₂ : ℝ) :
    windowCountOffLineMult T₁ T₂ + windowCountOnLineMult T₁ T₂ = windowCount T₁ T₂ := by
  rw [windowCountOffLineMult, windowCountOnLineMult, windowCount,
    ← windowZerosOffLine_union_onLine T₁ T₂,
    finsum_mem_union (windowZerosOffLine_disjoint_onLine T₁ T₂) (windowZerosOffLine_finite T₁ T₂)
      (windowZerosOnLine_finite T₁ T₂)]

/-- Counting with multiplicity is at least counting distinct points. -/
lemma windowCountOffLine_le_windowCountOffLineMult (T₁ T₂ : ℝ) :
    windowCountOffLine T₁ T₂ ≤ windowCountOffLineMult T₁ T₂ := by
  classical
  have hfin := windowZerosOffLine_finite T₁ T₂
  rw [windowCountOffLineMult, finsum_mem_eq_finite_toFinset_sum _ hfin, windowCountOffLine,
    Set.ncard_eq_toFinset_card _ hfin]
  refine le_trans (le_of_eq (by simp)) (Finset.card_nsmul_le_sum _ _ 1 ?_)
  intro ρ hρ
  exact one_le_zeroMultiplicity_of_mem ((Set.Finite.mem_toFinset hfin).1 hρ).1

lemma windowCountOnLine_le_windowCountOnLineMult (T₁ T₂ : ℝ) :
    windowCountOnLine T₁ T₂ ≤ windowCountOnLineMult T₁ T₂ := by
  classical
  have hfin := windowZerosOnLine_finite T₁ T₂
  rw [windowCountOnLineMult, finsum_mem_eq_finite_toFinset_sum _ hfin, windowCountOnLine_eq_ncard,
    Set.ncard_eq_toFinset_card _ hfin]
  refine le_trans (le_of_eq (by simp)) (Finset.card_nsmul_le_sum _ _ 1 ?_)
  intro ρ hρ
  exact one_le_zeroMultiplicity_of_mem ((Set.Finite.mem_toFinset hfin).1 hρ).1

/-- **The off-line count with multiplicity is the distinct off-line count plus the excess
multiplicity carried by the multiple off-line zeroes.** -/
lemma windowCountOffLineMult_eq (T₁ T₂ : ℝ) :
    windowCountOffLineMult T₁ T₂ =
      windowCountOffLine T₁ T₂ + windowMultipleOffLineExcess T₁ T₂ := by
  classical
  have hfin := windowZerosOffLine_finite T₁ T₂
  set F : Finset ℂ := hfin.toFinset with hF
  have hmem : ∀ ρ, ρ ∈ F ↔ ρ ∈ windowZerosOffLine T₁ T₂ := by
    intro ρ; rw [hF, Set.Finite.mem_toFinset]
  have hM : windowZerosOffLineMultiple T₁ T₂ =
      ↑(F.filter fun ρ => 2 ≤ zeroMultiplicity ρ) := by
    ext ρ
    simp only [windowZerosOffLineMultiple, Finset.coe_filter, Set.mem_setOf_eq, hmem]
  rw [windowCountOffLineMult, finsum_mem_eq_finite_toFinset_sum _ hfin, windowCountOffLine,
    Set.ncard_eq_toFinset_card _ hfin, windowMultipleOffLineExcess, hM, finsum_mem_coe_finset,
    ← hF]
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun ρ => 2 ≤ zeroMultiplicity ρ)
    (fun ρ => zeroMultiplicity ρ)
  have hone : ∀ ρ ∈ F.filter (fun ρ => ¬ 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ = 1 := by
    intro ρ hρ
    obtain ⟨hρF, hρ2⟩ := Finset.mem_filter.1 hρ
    have := one_le_zeroMultiplicity_of_mem ((hmem ρ).1 hρF).1
    omega
  have hsum1 : ∑ ρ ∈ F.filter (fun ρ => ¬ 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ =
      (F.filter fun ρ => ¬ 2 ≤ zeroMultiplicity ρ).card := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
  have hsum2 : ∑ ρ ∈ F.filter (fun ρ => 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ =
      (F.filter fun ρ => 2 ≤ zeroMultiplicity ρ).card +
        ∑ ρ ∈ F.filter (fun ρ => 2 ≤ zeroMultiplicity ρ), (zeroMultiplicity ρ - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have := (Finset.mem_filter.1 hρ).2
    omega
  have hcard := Finset.card_filter_add_card_filter_not (s := F)
    (fun ρ => 2 ≤ zeroMultiplicity ρ)
  omega

/-! ## What the distinct-zero transfer already gives with multiplicity -/

/-- **Under `SpeiserTransfer`: at most `26.272 %` of the zeroes of `ζ`, counted with
multiplicity, lie off the critical line.**  The distinct off-line zeroes cost `13.136 %` (the
transfer), and their excess multiplicity costs another `13.136 %` (unconditionally, by
`windowMultipleOffLineExcess_le_bad`). -/
theorem windowCountOffLineMult_le_of_speiserTransfer (h : SpeiserTransfer) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      (windowCountOffLineMult T (2 * T) : ℝ) ≤ (0.26272 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨S₁, h₁⟩ := offLine_le_of_speiserTransfer h (ε := ε / 2) (by positivity)
  obtain ⟨S₂, h₂⟩ := windowMultipleOffLineExcess_le_windowCount (ε := ε / 2) (by positivity)
  refine ⟨max S₁ S₂, fun T hT => ?_⟩
  have ha := h₁ T (le_trans (le_max_left _ _) hT)
  have hb := h₂ T (le_trans (le_max_right _ _) hT)
  have heq : (windowCountOffLineMult T (2 * T) : ℝ) =
      (windowCountOffLine T (2 * T) : ℝ) + (windowMultipleOffLineExcess T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (windowCountOffLineMult_eq T (2 * T))
  rw [heq]
  linarith

/-- **Under `SpeiserTransfer`: at least `73.7 %` of the nontrivial zeroes of `ζ`, counted with
multiplicity, lie on the critical line** — improving the `70 %` of
`seventy_percent_on_critical_line_of_speiserTransfer`, which counted the on-line zeroes as
distinct points.  `SpeiserTransfer` is **not** proved here. -/
theorem seventy_three_percent_on_critical_line_mult_of_speiserTransfer (h : SpeiserTransfer) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.737 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ) := by
  obtain ⟨S, hS⟩ := windowCountOffLineMult_le_of_speiserTransfer h (ε := 1 / 10000) (by norm_num)
  refine ⟨S, fun T hT => ?_⟩
  have hsplit : (windowCountOffLineMult T (2 * T) : ℝ) + (windowCountOnLineMult T (2 * T) : ℝ)
      = (windowCount T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLineMult_add_windowCountOnLineMult T (2 * T))
  have hN : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  linarith [hS T hT]

/-! ## The multiplicity-weighted form of Speiser's transfer -/

/-- **The counting form of Speiser's theorem, weighted by multiplicity** (Levinson–Montgomery),
as a `Prop`: the zeroes of `ζ` off the critical line in a dyadic window, *counted with
multiplicity*, are at most the `ξ′` bad count `N_{ξ′} − N₀ˢ_{ξ′}` of that window, up to
`O(log T)`.

This is the faithful form of the classical statement — the argument principle counts zeroes
with multiplicity — and `SpeiserTransfer` is its weakening to distinct points
(`speiserTransfer_of_speiserTransferMult`).  Like `SpeiserTransfer`, it is a *statement*: it is
**not** proved in this repository.  Its unconditional half, for the multiple off-line zeroes,
is `RiemannHypothesis.windowMultipleOffLineExcess_le_bad` together with
`RiemannHypothesis.ncard_windowZerosOffLineMultiple_le_bad`; what is missing is the simple
off-line zeroes, which need the argument principle for `ξ′/ξ` on the left half of the critical
strip. -/
def SpeiserTransferMult : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (windowCountOffLineMult T (2 * T) : ℝ) ≤
      xiDerivWindowCountBad T (2 * T) + C * Real.log T

/-- The multiplicity-weighted transfer implies the distinct-point transfer. -/
theorem speiserTransfer_of_speiserTransferMult (h : SpeiserTransferMult) : SpeiserTransfer := by
  obtain ⟨C, S, hS⟩ := h
  refine ⟨C, S, fun T hT => le_trans ?_ (hS T hT)⟩
  exact_mod_cast windowCountOffLine_le_windowCountOffLineMult T (2 * T)

/-- **Under `SpeiserTransferMult`: at most `13.136 %` of the zeroes of `ζ`, counted with
multiplicity, lie off the critical line.** -/
theorem offLineMult_le_of_speiserTransferMult (h : SpeiserTransferMult) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      (windowCountOffLineMult T (2 * T) : ℝ) ≤ (0.13136 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, S₀, hS₀⟩ := h
  obtain ⟨S₁, h₁⟩ := xiDerivWindowCountBad_le (ε := ε / 2) (by positivity)
  obtain ⟨S₂, hS₂, h₂⟩ := exists_le_windowCount_mul_log (2 * |C| / ε)
  refine ⟨max S₀ (max S₁ S₂), fun T hT => ?_⟩
  have hs0 : S₀ ≤ T := le_trans (le_max_left _ _) hT
  have hs1 : S₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hs2 : S₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hS₂ hs2
  have hlog0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT1
  have hspeiser := hS₀ T hs0
  have hbad := h₁ T hs1
  have hgrow := h₂ T hs2
  have hCabs : C * Real.log T ≤ ε / 2 * (windowCount T (2 * T) : ℝ) := by
    have hle : C * Real.log T ≤ |C| * Real.log T := by
      nlinarith [le_abs_self C]
    have hmul : ε / 2 * (2 * |C| / ε * Real.log T) ≤ ε / 2 * (windowCount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_left hgrow (by positivity)
    have heq : ε / 2 * (2 * |C| / ε * Real.log T) = |C| * Real.log T := by
      field_simp
    linarith [hle, hmul, heq.symm.le, heq.le]
  linarith [hspeiser, hbad, hCabs]

/-- **Under `SpeiserTransferMult`: at least `86.864 %` of the nontrivial zeroes of `ζ`, counted
with multiplicity, lie on the critical line.**  `SpeiserTransferMult` is **not** proved here;
unconditionally the repository proves `2/3`. -/
theorem eighty_six_percent_on_critical_line_mult_of_speiserTransferMult
    (h : SpeiserTransferMult) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 - ε) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨S, hS⟩ := offLineMult_le_of_speiserTransferMult h hε
  refine ⟨S, fun T hT => ?_⟩
  have hsplit : (windowCountOffLineMult T (2 * T) : ℝ) + (windowCountOnLineMult T (2 * T) : ℝ)
      = (windowCount T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLineMult_add_windowCountOnLineMult T (2 * T))
  linarith [hS T hT]

/-! ## Eighty per cent on the critical line, with multiplicity -/

/-- **The eighty per cent statement for the critical line, counted with multiplicity**, as a
`Prop`: `liminf N₀ᵐ(T,2T)/N(T,2T) ≥ 4/5`, where both counts are weighted by multiplicity.
Compare `EightyPercentOnCriticalLine`, whose numerator counts the on-line zeroes as distinct
points, and `EightyPercentOnCriticalLineDistinct`, whose denominator counts the zeroes as
distinct points. -/
def EightyPercentOnCriticalLineMult : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (4 / 5 - ε) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ)

/-- **Under `SpeiserTransferMult`, the eighty per cent target with multiplicity holds** (with
`86.864 %` to spare) — the conclusion that `RiemannHypothesis.EightyPercentRoute` could not
reach from the distinct-point transfer.  `SpeiserTransferMult` is **not** proved here. -/
theorem eightyPercentOnCriticalLineMult_of_speiserTransferMult (h : SpeiserTransferMult) :
    EightyPercentOnCriticalLineMult := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    eighty_six_percent_on_critical_line_mult_of_speiserTransferMult h (min ε (1 / 100))
      (lt_min hε (by norm_num))
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hmin : min ε (1 / 100) ≤ 1 / 100 := min_le_right _ _
  have := hT₀ T hT
  nlinarith [this, hN]

/-- The `ε`-free form: under `SpeiserTransferMult`, at least `80 %` of the nontrivial zeroes of
`ζ`, counted with multiplicity, lie on the critical line, for all large `T`. -/
theorem eighty_percent_on_critical_line_mult_of_speiserTransferMult (h : SpeiserTransferMult) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.8 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ) := by
  obtain ⟨T₀, hT₀⟩ :=
    eighty_six_percent_on_critical_line_mult_of_speiserTransferMult h (1 / 100) (by norm_num)
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith [hT₀ T hT]

end RiemannHypothesis

end
