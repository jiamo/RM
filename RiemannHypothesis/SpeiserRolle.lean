/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CriticalLineXi
import RiemannHypothesis.EightyPercentMultiplicity

/-!
# The unconditional half of Speiser's transfer, on the critical line

Rolle's theorem on the critical line (`RiemannHypothesis.exists_xiDerivFn_onLine_eq_zero`) gives
a zero of `ξ′` strictly between any two consecutive zeroes of `ζ` on the critical line.  Adding
to these the multiple zeroes of `ζ` on the line — where `ξ′` vanishes to order `m − 1` — one
gets, in every window and *unconditionally*:

* `windowCountOnLineMult_le_xiDerivWindowCountOnLineMult` :
  `N₀ᵐ(T₁,T₂) ≤ N₀ᵐ_{ξ′}(T₁,T₂) + 1`,

i.e. `ξ′` has at least as many zeroes on the critical line as `ζ` does, counted with
multiplicity, up to a single unit.  The counting consequences for the off-line zeroes are in
`RiemannHypothesis.SpeiserEquivalence`.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## A counting lemma: consecutive points and the points between them -/

/-- If between any two *consecutive* points of a finite set `S ⊆ ℝ` there is a point of `G`,
then `S` has at most one more element than `G`. -/
lemma card_le_card_add_one_of_gap {S G : Finset ℝ}
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ u ∈ S, u ≤ a ∨ b ≤ u) → ∃ c ∈ G, a < c ∧ c < b) :
    S.card ≤ G.card + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  set M : ℝ := S.max' hne with hM
  have hMS : M ∈ S := S.max'_mem hne
  -- the successor of a point of `S`, as a total function
  set nextv : ℝ → ℝ := fun a =>
    if hne' : (S.filter (fun u => a < u)).Nonempty then (S.filter (fun u => a < u)).min' hne'
    else a with hnext
  have hfilter : ∀ a ∈ S.erase M, (S.filter (fun u => a < u)).Nonempty := by
    intro a ha
    obtain ⟨haM, haS⟩ := Finset.mem_erase.1 ha
    exact ⟨M, Finset.mem_filter.2 ⟨hMS, lt_of_le_of_ne (S.le_max' a haS) haM⟩⟩
  have hnextS : ∀ a ∈ S.erase M, nextv a ∈ S ∧ a < nextv a := by
    intro a ha
    rw [hnext]
    simp only [dif_pos (hfilter a ha)]
    have hmem := (S.filter (fun u => a < u)).min'_mem (hfilter a ha)
    exact ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2⟩
  have hnextmin : ∀ a ∈ S.erase M, ∀ u ∈ S, u ≤ a ∨ nextv a ≤ u := by
    intro a ha u hu
    by_cases h' : u ≤ a
    · exact Or.inl h'
    · replace h' : a < u := not_le.1 h'
      refine Or.inr ?_
      rw [hnext]
      simp only [dif_pos (hfilter a ha)]
      exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hu, h'⟩)
  -- pick a point of `G` in each gap
  have key : ∀ a : ℝ, ∃ c : ℝ, a ∈ S.erase M → (c ∈ G ∧ a < c ∧ c < nextv a) := by
    intro a
    by_cases ha : a ∈ S.erase M
    · obtain ⟨hnS, hlt⟩ := hnextS a ha
      obtain ⟨c, hcG, hac, hcn⟩ :=
        h a (Finset.mem_of_mem_erase ha) (nextv a) hnS hlt (hnextmin a ha)
      exact ⟨c, fun _ => ⟨hcG, hac, hcn⟩⟩
    · exact ⟨0, fun h' => absurd h' ha⟩
  choose f hf using key
  have hmaps : ∀ a ∈ S.erase M, f a ∈ G := fun a ha => (hf a ha).1
  have hinj : Set.InjOn f ((S.erase M : Finset ℝ) : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne'
    have ha' : a ∈ S.erase M := Finset.mem_coe.1 ha
    have hb' : b ∈ S.erase M := Finset.mem_coe.1 hb
    rcases lt_trichotomy a b with hlt | heq | hlt
    · obtain ⟨-, -, hcn⟩ := hf a ha'
      obtain ⟨-, hbc, -⟩ := hf b hb'
      have hle : nextv a ≤ b :=
        (hnextmin a ha' b (Finset.mem_of_mem_erase hb')).resolve_left (not_le.2 hlt)
      have : f a < b := lt_of_lt_of_le hcn hle
      rw [hab] at this
      exact absurd hbc (not_lt.2 this.le)
    · exact hne' heq
    · obtain ⟨-, -, hcn⟩ := hf b hb'
      obtain ⟨-, hac, -⟩ := hf a ha'
      have hle : nextv b ≤ a :=
        (hnextmin b hb' a (Finset.mem_of_mem_erase ha')).resolve_left (not_le.2 hlt)
      have : f b < a := lt_of_lt_of_le hcn hle
      rw [← hab] at this
      exact absurd hac (not_lt.2 this.le)
  have hcard : (S.erase M).card ≤ G.card := Finset.card_le_card_of_injOn f hmaps hinj
  have hcarderase : (S.erase M).card = S.card - 1 := Finset.card_erase_of_mem hMS
  have hpos : 1 ≤ S.card := Finset.card_pos.2 hne
  omega

/-! ## The zeroes of `ξ′` on the critical line -/

/-- The zeroes of `ξ′` in the window that lie on the critical line. -/
def xiDerivWindowZerosOnLine (T₁ T₂ : ℝ) : Set ℂ :=
  xiDerivWindowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}

/-- `N₀ᵐ_{ξ′}(T₁,T₂)`: the zeroes of `ξ′` on the critical line in the window, counted with
multiplicity. -/
def xiDerivWindowCountOnLineMult (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ xiDerivWindowZerosOnLine T₁ T₂, xiDerivMultiplicity ρ

/-- `N_offᵐ_{ξ′}(T₁,T₂)`: the zeroes of `ξ′` off the critical line in the window, counted with
multiplicity. -/
def xiDerivWindowCountOffLineMult (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ xiDerivWindowZerosOffLine T₁ T₂, xiDerivMultiplicity ρ

lemma xiDerivWindowZerosOnLine_finite (T₁ T₂ : ℝ) :
    (xiDerivWindowZerosOnLine T₁ T₂).Finite :=
  (xiDerivWindowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1

lemma xiDerivWindowZerosOffLine_finite (T₁ T₂ : ℝ) :
    (xiDerivWindowZerosOffLine T₁ T₂).Finite :=
  (xiDerivWindowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1

lemma xiDerivWindowZeros_split (T₁ T₂ : ℝ) :
    xiDerivWindowZerosOffLine T₁ T₂ ∪ xiDerivWindowZerosOnLine T₁ T₂ =
      xiDerivWindowZeros T₁ T₂ := by
  ext ρ
  simp only [xiDerivWindowZerosOffLine, xiDerivWindowZerosOnLine, Set.mem_union,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
  · intro hs
    by_cases h : ρ.re = 1 / 2
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨hs, h⟩

/-- The `ξ′` window count splits into its off-line and on-line parts. -/
lemma xiDerivWindowCountOffLineMult_add_onLineMult (T₁ T₂ : ℝ) :
    xiDerivWindowCountOffLineMult T₁ T₂ + xiDerivWindowCountOnLineMult T₁ T₂ =
      xiDerivWindowCount T₁ T₂ := by
  have hdisj : Disjoint (xiDerivWindowZerosOffLine T₁ T₂) (xiDerivWindowZerosOnLine T₁ T₂) :=
    Set.disjoint_left.2 fun _ hs hs' => hs.2 hs'.2
  rw [xiDerivWindowCountOffLineMult, xiDerivWindowCountOnLineMult, xiDerivWindowCount,
    ← xiDerivWindowZeros_split T₁ T₂,
    finsum_mem_union hdisj (xiDerivWindowZerosOffLine_finite T₁ T₂)
      (xiDerivWindowZerosOnLine_finite T₁ T₂)]

/-! ## The gap zeroes produced by Rolle's theorem -/

/-- The zeroes of `ξ′` on the critical line in the window that are *not* zeroes of `ζ`: the
zeroes produced by Rolle's theorem between consecutive zeroes of `ζ` on the line. -/
def xiDerivWindowGapZeros (T₁ T₂ : ℝ) : Set ℂ :=
  xiDerivWindowZerosOnLine T₁ T₂ \ windowZeros T₁ T₂

lemma xiDerivWindowGapZeros_finite (T₁ T₂ : ℝ) : (xiDerivWindowGapZeros T₁ T₂).Finite :=
  (xiDerivWindowZerosOnLine_finite T₁ T₂).subset fun _ hρ => hρ.1

/-- A zero of `ζ` on the critical line in the window, written through `onLine`, is a zero
of `ξ`. -/
lemma xiFn_onLine_eq_zero_of_mem {T₁ T₂ : ℝ} {ρ : ℂ} (hρ : ρ ∈ windowZerosOnLine T₁ T₂) :
    xiFn (onLine ρ.im) = 0 := by
  obtain ⟨⟨⟨hz, h0, h1⟩, -⟩, hre⟩ := hρ
  rw [← eq_onLine hre]
  exact xiFn_eq_zero_of_zeta h0 h1 hz

/-! ### The ordinates of the on-line zeroes -/

/-- The ordinates of the zeroes of `ζ` on the critical line in the window. -/
def onLineOrdinates (T₁ T₂ : ℝ) : Set ℝ := Complex.im '' windowZerosOnLine T₁ T₂

/-- The ordinates of the gap zeroes of `ξ′`. -/
def gapOrdinates (T₁ T₂ : ℝ) : Set ℝ := Complex.im '' xiDerivWindowGapZeros T₁ T₂

lemma onLineOrdinates_finite (T₁ T₂ : ℝ) : (onLineOrdinates T₁ T₂).Finite :=
  (windowZerosOnLine_finite T₁ T₂).image _

lemma gapOrdinates_finite (T₁ T₂ : ℝ) : (gapOrdinates T₁ T₂).Finite :=
  (xiDerivWindowGapZeros_finite T₁ T₂).image _

lemma mem_onLineOrdinates {T₁ T₂ t : ℝ} :
    t ∈ onLineOrdinates T₁ T₂ ↔ onLine t ∈ windowZerosOnLine T₁ T₂ := by
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    rwa [← eq_onLine hρ.2]
  · intro h
    exact ⟨onLine t, h, onLine_im t⟩

lemma mem_gapOrdinates {T₁ T₂ t : ℝ} :
    t ∈ gapOrdinates T₁ T₂ ↔ onLine t ∈ xiDerivWindowGapZeros T₁ T₂ := by
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    rwa [← eq_onLine hρ.1.2]
  · intro h
    exact ⟨onLine t, h, onLine_im t⟩

lemma ncard_onLineOrdinates (T₁ T₂ : ℝ) :
    (onLineOrdinates T₁ T₂).ncard = windowCountOnLine T₁ T₂ := by
  rw [onLineOrdinates, windowCountOnLine_eq_ncard]
  refine Set.InjOn.ncard_image ?_
  intro x hx y hy hxy
  rw [eq_onLine hx.2, eq_onLine hy.2, hxy]

lemma ncard_gapOrdinates_le (T₁ T₂ : ℝ) :
    (gapOrdinates T₁ T₂).ncard ≤ (xiDerivWindowGapZeros T₁ T₂).ncard :=
  Set.ncard_image_le (xiDerivWindowGapZeros_finite T₁ T₂)

/-! ### Rolle's theorem in counting form -/

/-- Between two consecutive ordinates of on-line zeroes of `ζ` there is a gap ordinate. -/
lemma exists_gapOrdinate {T₁ T₂ a b : ℝ} (ha : a ∈ onLineOrdinates T₁ T₂)
    (hb : b ∈ onLineOrdinates T₁ T₂) (hab : a < b)
    (hcons : ∀ u ∈ onLineOrdinates T₁ T₂, u ≤ a ∨ b ≤ u) :
    ∃ c ∈ gapOrdinates T₁ T₂, a < c ∧ c < b := by
  have hA := mem_onLineOrdinates.1 ha
  have hB := mem_onLineOrdinates.1 hb
  have hxa : xiFn (onLine a) = 0 := by
    have := xiFn_onLine_eq_zero_of_mem hA
    rwa [onLine_im] at this
  have hxb : xiFn (onLine b) = 0 := by
    have := xiFn_onLine_eq_zero_of_mem hB
    rwa [onLine_im] at this
  obtain ⟨c, hc, hc0⟩ := exists_xiDerivFn_onLine_eq_zero hab hxa hxb
  have hTa : T₁ < a := by
    have := hA.1.2.1
    rwa [onLine_im] at this
  have hTb : b ≤ T₂ := by
    have := hB.1.2.2
    rwa [onLine_im] at this
  have hwin : T₁ < c ∧ c ≤ T₂ := ⟨lt_trans hTa hc.1, le_of_lt (lt_of_lt_of_le hc.2 hTb)⟩
  have hnot : onLine c ∉ windowZeros T₁ T₂ := by
    intro hmem
    have hc' : c ∈ onLineOrdinates T₁ T₂ :=
      mem_onLineOrdinates.2 ⟨hmem, onLine_re c⟩
    rcases hcons c hc' with h | h
    · exact absurd hc.1 (not_lt.2 h)
    · exact absurd hc.2 (not_lt.2 h)
  refine ⟨c, mem_gapOrdinates.2 ⟨⟨⟨hc0, ?_, ?_⟩, onLine_re c⟩, hnot⟩, hc.1, hc.2⟩
  · rw [onLine_im]; exact hwin.1
  · rw [onLine_im]; exact hwin.2

/-- **Rolle's theorem, in counting form.**  The number of distinct zeroes of `ζ` on the critical
line in a window is at most one more than the number of zeroes of `ξ′` on the line in the window
that are not zeroes of `ζ`. -/
theorem windowCountOnLine_le_ncard_gapZeros_add_one (T₁ T₂ : ℝ) :
    windowCountOnLine T₁ T₂ ≤ (xiDerivWindowGapZeros T₁ T₂).ncard + 1 := by
  classical
  have hSfin := onLineOrdinates_finite T₁ T₂
  have hGfin := gapOrdinates_finite T₁ T₂
  have hkey : hSfin.toFinset.card ≤ hGfin.toFinset.card + 1 := by
    refine card_le_card_add_one_of_gap ?_
    intro a ha b hb hab hcons
    rw [Set.Finite.mem_toFinset] at ha hb
    obtain ⟨c, hc, hac, hcb⟩ := exists_gapOrdinate ha hb hab (by
      intro u hu
      exact hcons u ((Set.Finite.mem_toFinset hSfin).2 hu))
    exact ⟨c, (Set.Finite.mem_toFinset hGfin).2 hc, hac, hcb⟩
  have hS : hSfin.toFinset.card = windowCountOnLine T₁ T₂ := by
    rw [← Set.ncard_eq_toFinset_card _ hSfin, ncard_onLineOrdinates]
  have hG : hGfin.toFinset.card = (gapOrdinates T₁ T₂).ncard :=
    (Set.ncard_eq_toFinset_card _ hGfin).symm
  have hGle := ncard_gapOrdinates_le T₁ T₂
  omega

/-! ## The counting theorem -/

/-- The excess multiplicity of the on-line zeroes of `ζ` is carried by `ξ′`. -/
lemma sum_xiDerivMultiplicity_onLine_ge (T₁ T₂ : ℝ) :
    windowCountOnLineMult T₁ T₂ ≤
      (∑ᶠ ρ ∈ windowZerosOnLine T₁ T₂ ∩ {ρ : ℂ | 2 ≤ zeroMultiplicity ρ},
        xiDerivMultiplicity ρ) + windowCountOnLine T₁ T₂ := by
  classical
  have hfin : (windowZerosOnLine T₁ T₂).Finite := windowZerosOnLine_finite T₁ T₂
  set F : Finset ℂ := hfin.toFinset with hF
  have hmem : ∀ ρ, ρ ∈ F ↔ ρ ∈ windowZerosOnLine T₁ T₂ := by
    intro ρ; rw [hF, Set.Finite.mem_toFinset]
  have hM : windowZerosOnLine T₁ T₂ ∩ {ρ : ℂ | 2 ≤ zeroMultiplicity ρ} =
      ↑(F.filter fun ρ => 2 ≤ zeroMultiplicity ρ) := by
    ext ρ
    simp only [Finset.coe_filter, Set.mem_inter_iff, Set.mem_ofPred_eq, hmem]
  rw [windowCountOnLineMult, finsum_mem_eq_finite_toFinset_sum _ hfin, hM,
    finsum_mem_coe_finset, windowCountOnLine_eq_ncard, Set.ncard_eq_toFinset_card _ hfin,
    ← hF]
  have hmult : ∀ ρ ∈ F.filter (fun ρ => 2 ≤ zeroMultiplicity ρ),
      zeroMultiplicity ρ = xiDerivMultiplicity ρ + 1 := by
    intro ρ hρ
    obtain ⟨hρF, -⟩ := Finset.mem_filter.1 hρ
    obtain ⟨⟨⟨hz, h0, h1⟩, -⟩, -⟩ := (hmem ρ).1 hρF
    exact (xiDerivMultiplicity_add_one h0 h1 hz).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not F
    (fun ρ => 2 ≤ zeroMultiplicity ρ) (fun ρ => zeroMultiplicity ρ)
  have h1 : ∑ ρ ∈ F.filter (fun ρ => 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ =
      ∑ ρ ∈ F.filter (fun ρ => 2 ≤ zeroMultiplicity ρ), (xiDerivMultiplicity ρ + 1) :=
    Finset.sum_congr rfl hmult
  have h2 : ∑ ρ ∈ F.filter (fun ρ => ¬ 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ ≤
      (F.filter fun ρ => ¬ 2 ≤ zeroMultiplicity ρ).card := by
    calc ∑ ρ ∈ F.filter (fun ρ => ¬ 2 ≤ zeroMultiplicity ρ), zeroMultiplicity ρ
        ≤ ∑ _ρ ∈ F.filter (fun ρ => ¬ 2 ≤ zeroMultiplicity ρ), 1 := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have := (Finset.mem_filter.1 hρ).2
          omega
      _ = (F.filter fun ρ => ¬ 2 ≤ zeroMultiplicity ρ).card := by simp
  have h3 : (F.filter fun ρ => 2 ≤ zeroMultiplicity ρ).card +
      (F.filter fun ρ => ¬ 2 ≤ zeroMultiplicity ρ).card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) fun ρ => 2 ≤ zeroMultiplicity ρ
  rw [Finset.sum_add_distrib] at h1
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  omega

/-- Each gap zero contributes at least one to the on-line `ξ′` count. -/
lemma ncard_gapZeros_le_sum (T₁ T₂ : ℝ) :
    (xiDerivWindowGapZeros T₁ T₂).ncard ≤
      ∑ᶠ ρ ∈ xiDerivWindowGapZeros T₁ T₂, xiDerivMultiplicity ρ := by
  classical
  have hfin : (xiDerivWindowGapZeros T₁ T₂).Finite := xiDerivWindowGapZeros_finite T₁ T₂
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
  refine le_trans (le_of_eq (by simp)) (Finset.card_nsmul_le_sum _ _ 1 ?_)
  intro ρ hρ
  exact one_le_xiDerivMultiplicity ((Set.Finite.mem_toFinset hfin).1 hρ).1.1.1

/-- The multiple on-line zeroes of `ζ` and the gap zeroes are disjoint sets of on-line zeroes of
`ξ′`, so their contributions add up inside `N₀ᵐ_{ξ′}`. -/
lemma sum_multiple_add_gap_le (T₁ T₂ : ℝ) :
    (∑ᶠ ρ ∈ windowZerosOnLine T₁ T₂ ∩ {ρ : ℂ | 2 ≤ zeroMultiplicity ρ},
        xiDerivMultiplicity ρ) +
      (∑ᶠ ρ ∈ xiDerivWindowGapZeros T₁ T₂, xiDerivMultiplicity ρ) ≤
      xiDerivWindowCountOnLineMult T₁ T₂ := by
  classical
  set B := windowZerosOnLine T₁ T₂ ∩ {ρ : ℂ | 2 ≤ zeroMultiplicity ρ} with hB
  set U := xiDerivWindowGapZeros T₁ T₂ with hU
  have hBfin : B.Finite := (windowZerosOnLine_finite T₁ T₂).subset fun _ hρ => hρ.1
  have hUfin : U.Finite := xiDerivWindowGapZeros_finite T₁ T₂
  have hBsub : B ⊆ xiDerivWindowZerosOnLine T₁ T₂ := by
    rintro ρ ⟨⟨⟨⟨hz, h0, h1⟩, hw1, hw2⟩, hre⟩, hm⟩
    exact ⟨⟨xiDerivFn_eq_zero_of_multiple h0 h1 hz hm, hw1, hw2⟩, hre⟩
  have hUsub : U ⊆ xiDerivWindowZerosOnLine T₁ T₂ := fun _ hρ => hρ.1
  have hdisj : Disjoint B U :=
    Set.disjoint_left.2 fun _ hρB hρU => hρU.2 hρB.1.1
  have hunion : B ∪ U ⊆ xiDerivWindowZerosOnLine T₁ T₂ := Set.union_subset hBsub hUsub
  have hfinOn : (xiDerivWindowZerosOnLine T₁ T₂).Finite := xiDerivWindowZerosOnLine_finite T₁ T₂
  rw [xiDerivWindowCountOnLineMult, ← finsum_mem_union hdisj hBfin hUfin,
    finsum_mem_eq_finite_toFinset_sum _ (hBfin.union hUfin),
    finsum_mem_eq_finite_toFinset_sum _ hfinOn]
  refine Finset.sum_le_sum_of_subset ?_
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hunion hρ

/-- **The zeroes of `ξ′` on the critical line outnumber those of `ζ`, up to one.**  Counted with
multiplicity, `N₀ᵐ(T₁,T₂) ≤ N₀ᵐ_{ξ′}(T₁,T₂) + 1`.  Unconditional: it is Rolle's theorem for
Hardy's function `Ξ`, together with the fact that `ξ′` vanishes to order `m − 1` at a zero of
`ζ` of multiplicity `m`. -/
theorem windowCountOnLineMult_le_xiDerivWindowCountOnLineMult (T₁ T₂ : ℝ) :
    windowCountOnLineMult T₁ T₂ ≤ xiDerivWindowCountOnLineMult T₁ T₂ + 1 := by
  have h1 := sum_xiDerivMultiplicity_onLine_ge T₁ T₂
  have h2 := windowCountOnLine_le_ncard_gapZeros_add_one T₁ T₂
  have h3 := ncard_gapZeros_le_sum T₁ T₂
  have h4 := sum_multiple_add_gap_le T₁ T₂
  omega

end RiemannHypothesis

end
