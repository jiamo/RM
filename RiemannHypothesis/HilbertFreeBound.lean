/-
Copyright (c) 2026 Aristotle. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannHypothesis.HilbertInequality

/-!
# The free bound for the Hilbert bilinear form

`RiemannHypothesis/HilbertInequality.lean` proves Hilbert's inequality with the sharp constant
`π` for frequencies in a lattice, and records the general (Montgomery–Vaughan) statement for
arbitrary `δ`-separated real frequencies as an unproved `Prop`
(`RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`).  That file's own documentation
points out that the *free* bound — the one that follows from the triangle inequality and the
separation alone, at the cost of a logarithm — is elementary.  This file proves it.

## Main results

* `RiemannHypothesis.Hilbert.sum_inv_dist_le` — for `δ`-separated reals `lam` indexed by a
  finset `S`, and any `r ∈ S`,
  `∑_{s ∈ S \ {r}} 1/|lam r − lam s| ≤ 2·H_{#S}/δ`, where `H_m` is the `m`-th harmonic number.
  This is the "sort by distance" step: the `j`-th nearest frequency on either side of `lam r`
  is at distance at least `j δ`.
* `RiemannHypothesis.Hilbert.hilbert_free_bound` — consequently, for `δ`-separated real
  frequencies `lam r` and arbitrary complex coefficients,
  `‖∑_{r ≠ s} x r conj (x s)/(lam r − lam s)‖ ≤ 2 H_n δ⁻¹ ∑_r ‖x r‖²`.
* `RiemannHypothesis.Hilbert.hilbert_free_bound_log` — the same with `H_n` replaced by
  `1 + log n`.

The point of the Montgomery–Vaughan theorem is precisely that the harmonic factor here can be
removed and replaced by the absolute constant `π`; the free bound is what one has without it.

## Implementation notes

The geometric input is `Finset.card_mul_le_of_separated`-style: a `δ`-separated finite set of
reals contained in `[c, d]` has at most `(d − c)/δ + 1` elements (`card_le_of_separated`).
Applied to the points between `lam r` and the `k`-th nearest frequency to its right, it gives
`lam s − lam r ≥ k δ`, and summing `1/k` over an injective rank function produces the harmonic
number.
-/

namespace RiemannHypothesis

namespace Hilbert

open Finset

/-- A `δ`-separated finite set of reals inside `[c, d]` has at most `(d − c)/δ + 1` points:
`#A · δ ≤ (d − c) + δ`. -/
theorem card_le_of_separated {δ : ℝ} (hδ : 0 < δ) :
    ∀ (n : ℕ) (A : Finset ℝ), A.card = n →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b|) →
      ∀ c d : ℝ, c ≤ d → (∀ a ∈ A, c ≤ a ∧ a ≤ d) → (n : ℝ) * δ ≤ (d - c) + δ := by
  intro n
  induction n with
  | zero =>
    intro A _ _ c d hcd _
    simpa using by linarith
  | succ n ih =>
    intro A hcard hsep c d hcd hmem
    have hne : A.Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    set m := A.max' hne with hm
    have hmA : m ∈ A := A.max'_mem hne
    set A' := A.erase m with hA'
    have hcard' : A'.card = n := by
      rw [hA', Finset.card_erase_of_mem hmA, hcard]
      omega
    have hsep' : ∀ a ∈ A', ∀ b ∈ A', a ≠ b → δ ≤ |a - b| := by
      intro a ha b hb hab
      exact hsep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
    have hle : ∀ a ∈ A', a ≤ m - δ := by
      intro a ha
      have haA : a ∈ A := Finset.mem_of_mem_erase ha
      have hane : a ≠ m := Finset.ne_of_mem_erase ha
      have hlt : a ≤ m := A.le_max' a haA
      have := hsep a haA m hmA hane
      rw [abs_of_nonpos (by linarith)] at this
      linarith
    have hmd : m ≤ d := (hmem m hmA).2
    rcases Finset.eq_empty_or_nonempty A' with hA'e | hA'ne
    · have hn0 : n = 0 := by rw [← hcard', hA'e]; simp
      subst hn0
      have : (1 : ℝ) * δ ≤ (d - c) + δ := by
        have : (0 : ℝ) ≤ d - c := by linarith
        linarith
      simpa using this
    · obtain ⟨a₀, ha₀⟩ := hA'ne
      have hca₀ : c ≤ a₀ := (hmem a₀ (Finset.mem_of_mem_erase ha₀)).1
      have hcd' : c ≤ m - δ := le_trans hca₀ (hle a₀ ha₀)
      have hmem' : ∀ a ∈ A', c ≤ a ∧ a ≤ m - δ := by
        intro a ha
        exact ⟨(hmem a (Finset.mem_of_mem_erase ha)).1, hle a ha⟩
      have := ih A' hcard' hsep' c (m - δ) hcd' hmem'
      push_cast
      linarith

/-- Harmonic numbers are monotone. -/
theorem harmonic_le_harmonic {m n : ℕ} (h : m ≤ n) : harmonic m ≤ harmonic n := by
  simp only [harmonic]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h)) ?_
  intro i _ _
  positivity

variable {ι : Type*} [DecidableEq ι]

section Ranks

variable {S : Finset ι} {lam : ι → ℝ} {δ : ℝ}

omit [DecidableEq ι] in
/-- The frequencies are pairwise distinct, as `δ`-separation with `δ > 0` forces. -/
theorem lam_injOn (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) : Set.InjOn lam S := by
  intro r hr s hs hrs
  by_contra hne
  have := hsep r hr s hs hne
  rw [hrs] at this
  simp at this
  linarith

/-- The rank of `s` among the frequencies to the right of `lam r`. -/
private noncomputable def rankR (S : Finset ι) (lam : ι → ℝ) (r s : ι) : ℕ :=
  (((S.erase r).filter fun t => lam r < lam t).filter fun t => lam t ≤ lam s).card

/-- The `k`-th frequency to the right of `lam r` is at distance at least `k δ`. -/
theorem le_dist_of_rankR (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) {r s : ι} (hr : r ∈ S)
    (hs : s ∈ (S.erase r).filter fun t => lam r < lam t) :
    (rankR S lam r s : ℝ) * δ ≤ lam s - lam r := by
  classical
  set P := ((S.erase r).filter fun t => lam r < lam t).filter fun t => lam t ≤ lam s with hP
  have hPsub : P ⊆ S.erase r := by
    intro t ht
    exact Finset.mem_of_mem_filter t (Finset.filter_subset _ _ ht)
  -- the image of `P` under `lam`, together with `lam r`
  set A : Finset ℝ := insert (lam r) (P.image lam) with hA
  have hinj : Set.InjOn lam S := lam_injOn hδ hsep
  have hPS : ∀ t ∈ P, t ∈ S := fun t ht => Finset.mem_of_mem_erase (hPsub ht)
  have hnotmem : lam r ∉ P.image lam := by
    intro hmem
    obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hmem
    have hgt : lam r < lam t := by
      have := Finset.mem_filter.mp (Finset.mem_of_mem_filter t ht)
      exact (Finset.mem_filter.mp (Finset.filter_subset _ _ ht)).2
    rw [hteq] at hgt
    exact lt_irrefl _ hgt
  have hinjP : Set.InjOn lam (P : Set ι) :=
    fun a ha b hb hab => hinj (hPS a ha) (hPS b hb) hab
  have hcardA : A.card = P.card + 1 := by
    rw [hA, Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injOn hinjP]
  have hsepA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b| := by
    have key : ∀ t ∈ insert r (P : Finset ι), ∀ u ∈ insert r (P : Finset ι), lam t ≠ lam u →
        δ ≤ |lam t - lam u| := by
      intro t ht u hu htu
      have htS : t ∈ S := by
        rcases Finset.mem_insert.mp ht with h | h
        · exact h ▸ hr
        · exact hPS t h
      have huS : u ∈ S := by
        rcases Finset.mem_insert.mp hu with h | h
        · exact h ▸ hr
        · exact hPS u h
      exact hsep t htS u huS (fun h => htu (by rw [h]))
    intro a ha b hb hab
    have hA' : A = (insert r P).image lam := by
      rw [hA, Finset.image_insert]
    rw [hA'] at ha hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact key t ht u hu hab
  have hmemA : ∀ a ∈ A, lam r ≤ a ∧ a ≤ lam s := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h | h
    · subst h
      have : lam r < lam s := (Finset.mem_filter.mp hs).2
      exact ⟨le_refl _, this.le⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      refine ⟨?_, (Finset.mem_filter.mp ht).2⟩
      exact ((Finset.mem_filter.mp (Finset.filter_subset _ _ ht)).2).le
  have hcd : lam r ≤ lam s := ((Finset.mem_filter.mp hs).2).le
  have := card_le_of_separated hδ A.card A rfl hsepA (lam r) (lam s) hcd hmemA
  rw [hcardA] at this
  have hrank : rankR S lam r s = P.card := rfl
  rw [hrank]
  push_cast at this ⊢
  linarith

/-- The rank is a positive number. -/
theorem rankR_pos {r s : ι}
    (hs : s ∈ (S.erase r).filter fun t => lam r < lam t) : 0 < rankR S lam r s := by
  classical
  have : s ∈ ((S.erase r).filter fun t => lam r < lam t).filter fun t => lam t ≤ lam s :=
    Finset.mem_filter.mpr ⟨hs, le_refl _⟩
  exact Finset.card_pos.mpr ⟨s, this⟩

/-- The rank is at most the number of frequencies on that side. -/
theorem rankR_le_card {r s : ι} :
    rankR S lam r s ≤ ((S.erase r).filter fun t => lam r < lam t).card :=
  Finset.card_filter_le _ _

/-- Ranks are strictly monotone in the frequency, hence injective. -/
theorem rankR_injOn (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) {r : ι} :
    Set.InjOn (rankR S lam r) (((S.erase r).filter fun t => lam r < lam t) : Set ι) := by
  classical
  have hmono : ∀ s ∈ (S.erase r).filter fun t => lam r < lam t,
      ∀ u ∈ (S.erase r).filter fun t => lam r < lam t, lam s < lam u →
      rankR S lam r s < rankR S lam r u := by
    intro s hs u hu hlt
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro t ht
      have h1 := Finset.mem_of_mem_filter t ht
      have h2 := (Finset.mem_filter.mp ht).2
      exact Finset.mem_filter.mpr ⟨h1, le_trans h2 hlt.le⟩
    · intro hsub
      have : u ∈ ((S.erase r).filter fun t => lam r < lam t).filter fun t => lam t ≤ lam s :=
        hsub (Finset.mem_filter.mpr ⟨hu, le_refl _⟩)
      have := (Finset.mem_filter.mp this).2
      linarith
  intro s hs u hu hsu
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs hu
  have hs' : s ∈ (S.erase r).filter fun t => lam r < lam t :=
    Finset.mem_filter.mpr ⟨hs.1, hs.2⟩
  have hu' : u ∈ (S.erase r).filter fun t => lam r < lam t :=
    Finset.mem_filter.mpr ⟨hu.1, hu.2⟩
  have hinj : Set.InjOn lam S := lam_injOn hδ hsep
  rcases lt_trichotomy (lam s) (lam u) with h | h | h
  · exact absurd hsu (by have := hmono s hs' u hu' h; omega)
  · exact hinj (Finset.mem_of_mem_erase hs.1) (Finset.mem_of_mem_erase hu.1) h
  · exact absurd hsu (by have := hmono u hu' s hs' h; omega)

end Ranks

omit [DecidableEq ι] in
/-- The harmonic bound for a sum of reciprocals of an injective positive rank function. -/
theorem sum_inv_rank_le {T : Finset ι} {k : ι → ℕ} (hpos : ∀ s ∈ T, 0 < k s)
    (hle : ∀ s ∈ T, k s ≤ T.card) (hinj : Set.InjOn k (T : Set ι)) :
    ∑ s ∈ T, (1 : ℝ) / k s ≤ (harmonic T.card : ℝ) := by
  classical
  have himg : ∑ s ∈ T, (1 : ℝ) / k s = ∑ j ∈ T.image k, (1 : ℝ) / j := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  rw [himg]
  have hsub : T.image k ⊆ Finset.Icc 1 T.card := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_Icc.mpr ⟨hpos s hs, hle s hs⟩
  have hharm : (harmonic T.card : ℝ) = ∑ j ∈ Finset.Icc 1 T.card, (1 : ℝ) / j := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [hharm]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro j _ _
  positivity

/-- **The free bound, one row at a time.**  For `δ`-separated frequencies, the sum of the
reciprocal distances from any one frequency to all the others is at most `2 H_{#S}/δ`. -/
theorem sum_inv_dist_le {S : Finset ι} {lam : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) {r : ι} (hr : r ∈ S) :
    ∑ s ∈ S.erase r, 1 / |lam r - lam s| ≤ 2 * (harmonic S.card : ℝ) / δ := by
  classical
  set Tp := (S.erase r).filter fun t => lam r < lam t with hTp
  set Tm := (S.erase r).filter fun t => lam t < lam r with hTm
  have hsplit : S.erase r = Tp ∪ Tm := by
    ext t
    simp only [hTp, hTm, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      have htS : t ∈ S := Finset.mem_of_mem_erase ht
      have hne : t ≠ r := Finset.ne_of_mem_erase ht
      have := hsep r hr t htS (fun h => hne h.symm)
      rcases lt_trichotomy (lam r) (lam t) with h | h | h
      · exact Or.inl ⟨ht, h⟩
      · rw [h] at this; simp at this; linarith
      · exact Or.inr ⟨ht, h⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  have hdisj : Disjoint Tp Tm := by
    rw [Finset.disjoint_left]
    intro t htp htm
    have h1 := (Finset.mem_filter.mp htp).2
    have h2 := (Finset.mem_filter.mp htm).2
    linarith
  -- the bound on each side
  have hside : ∀ (T : Finset ι) (k : ι → ℕ), T ⊆ S.erase r → (∀ s ∈ T, 0 < k s) →
      (∀ s ∈ T, k s ≤ T.card) → Set.InjOn k (T : Set ι) →
      (∀ s ∈ T, (k s : ℝ) * δ ≤ |lam r - lam s|) →
      ∑ s ∈ T, 1 / |lam r - lam s| ≤ (harmonic S.card : ℝ) / δ := by
    intro T k hTsub hpos hle hinj hdist
    have hstep : ∑ s ∈ T, 1 / |lam r - lam s| ≤ ∑ s ∈ T, (1 / (k s : ℝ)) / δ := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hk : (0 : ℝ) < k s := by exact_mod_cast hpos s hs
      have hd : (0 : ℝ) < (k s : ℝ) * δ := by positivity
      have hdd : (k s : ℝ) * δ ≤ |lam r - lam s| := hdist s hs
      have hpos' : (0 : ℝ) < |lam r - lam s| := lt_of_lt_of_le hd hdd
      rw [div_div]
      exact one_div_le_one_div_of_le hd (by linarith [hdd])
    have hsum : ∑ s ∈ T, (1 / (k s : ℝ)) / δ = (∑ s ∈ T, 1 / (k s : ℝ)) / δ := by
      rw [Finset.sum_div]
    rw [hsum] at hstep
    have hcard : (harmonic T.card : ℝ) ≤ (harmonic S.card : ℝ) := by
      have hTc : T.card ≤ S.card :=
        Finset.card_le_card (hTsub.trans (Finset.erase_subset _ _))
      have := harmonic_le_harmonic hTc
      exact_mod_cast this
    have h1 := sum_inv_rank_le hpos hle hinj
    calc ∑ s ∈ T, 1 / |lam r - lam s| ≤ (∑ s ∈ T, 1 / (k s : ℝ)) / δ := hstep
      _ ≤ (harmonic T.card : ℝ) / δ := by gcongr
      _ ≤ (harmonic S.card : ℝ) / δ := by gcongr
  -- the right-hand side
  have hright : ∑ s ∈ Tp, 1 / |lam r - lam s| ≤ (harmonic S.card : ℝ) / δ := by
    refine hside Tp (rankR S lam r) (Finset.filter_subset _ _)
      (fun s hs => rankR_pos hs) (fun s _ => rankR_le_card) (rankR_injOn hδ hsep) ?_
    intro s hs
    have h := le_dist_of_rankR hδ hsep hr hs
    have hlt : lam r < lam s := (Finset.mem_filter.mp hs).2
    rw [abs_of_nonpos (by linarith)]
    linarith
  -- the left-hand side, by reflection
  have hleft : ∑ s ∈ Tm, 1 / |lam r - lam s| ≤ (harmonic S.card : ℝ) / δ := by
    have hsep' : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ |(-lam) a - (-lam) b| := by
      intro a ha b hb hab
      have h := hsep a ha b hb hab
      have hrw : (-lam) a - (-lam) b = -(lam a - lam b) := by
        simp only [Pi.neg_apply]; ring
      rw [hrw, abs_neg]
      exact h
    have hTm' : Tm = (S.erase r).filter fun t => (-lam) r < (-lam) t := by
      ext t
      simp only [hTm, Finset.mem_filter, Pi.neg_apply, neg_lt_neg_iff]
    rw [hTm']
    refine hside _ (rankR S (-lam) r) (Finset.filter_subset _ _) (fun s hs => rankR_pos hs)
      (fun s _ => rankR_le_card) (rankR_injOn hδ hsep') ?_
    intro s hs
    have h := le_dist_of_rankR hδ hsep' hr hs
    have hlt : (-lam) r < (-lam) s := (Finset.mem_filter.mp hs).2
    simp only [Pi.neg_apply] at h hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [hsplit, Finset.sum_union hdisj]
  have : (harmonic S.card : ℝ) / δ + (harmonic S.card : ℝ) / δ
      = 2 * (harmonic S.card : ℝ) / δ := by ring
  linarith

/-- Off-diagonal double sums may be transposed. -/
theorem sum_offDiag_comm {M : Type*} [AddCommMonoid M] (S : Finset ι) (F : ι → ι → M) :
    ∑ r ∈ S, ∑ s ∈ S.erase r, F r s = ∑ r ∈ S, ∑ s ∈ S.erase r, F s r := by
  classical
  exact Finset.sum_comm' (by intro x y; simp only [Finset.mem_erase]; tauto)

/-- **The free bound for the Hilbert bilinear form.**  For `δ`-separated real frequencies
`lam` on a finset `S` and arbitrary complex coefficients `x`,

`‖∑_{r ≠ s} x r conj (x s)/(lam r − lam s)‖ ≤ 2 H_{#S} δ⁻¹ ∑ ‖x r‖²`,

`H_m` the `m`-th harmonic number.  This is the elementary bound the Montgomery–Vaughan theorem
improves: there the harmonic factor is replaced by the absolute constant `π`. -/
theorem hilbert_free_bound_finset {S : Finset ι} {lam : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) (x : ι → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r,
        x r * (starRingEnd ℂ) (x s) / ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 2 * (harmonic S.card : ℝ) / δ * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  classical
  set a : ι → ℝ := fun r => ‖x r‖ ^ 2 with ha
  set D : ι → ι → ℝ := fun r s => 1 / |lam r - lam s| with hD
  -- termwise bound
  have hterm : ∀ r ∈ S, ∀ s ∈ S.erase r,
      ‖x r * (starRingEnd ℂ) (x s) / ((lam r : ℂ) - (lam s : ℂ))‖
        ≤ (a r + a s) / 2 * D r s := by
    intro r hr s hs
    have hsS : s ∈ S := Finset.mem_of_mem_erase hs
    have hne : s ≠ r := Finset.ne_of_mem_erase hs
    have hsep' := hsep r hr s hsS (fun h => hne h.symm)
    have hdpos : (0 : ℝ) < |lam r - lam s| := lt_of_lt_of_le hδ hsep'
    have hden : ((lam r : ℂ) - (lam s : ℂ)) ≠ 0 := by
      intro h
      have : (lam r : ℝ) = lam s := by
        have := sub_eq_zero.mp h
        exact_mod_cast this
      rw [this] at hdpos
      simp at hdpos
    have hnormden : ‖((lam r : ℂ) - (lam s : ℂ))‖ = |lam r - lam s| := by
      rw [show ((lam r : ℂ) - (lam s : ℂ)) = ((lam r - lam s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [norm_div, norm_mul, RCLike.norm_conj, hnormden, hD]
    have hab : ‖x r‖ * ‖x s‖ ≤ (a r + a s) / 2 := by
      have := sq_nonneg (‖x r‖ - ‖x s‖)
      rw [ha]
      nlinarith
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hab (by positivity)
  have hnorm : ‖∑ r ∈ S, ∑ s ∈ S.erase r,
      x r * (starRingEnd ℂ) (x s) / ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ ∑ r ∈ S, ∑ s ∈ S.erase r, (a r + a s) / 2 * D r s := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r hr => ?_)
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s hs => hterm r hr s hs)
  -- symmetrize
  have hsymm : ∑ r ∈ S, ∑ s ∈ S.erase r, (a r + a s) / 2 * D r s
      = ∑ r ∈ S, a r * ∑ s ∈ S.erase r, D r s := by
    have hsplit : ∑ r ∈ S, ∑ s ∈ S.erase r, (a r + a s) / 2 * D r s
        = (∑ r ∈ S, ∑ s ∈ S.erase r, a r * D r s) / 2
          + (∑ r ∈ S, ∑ s ∈ S.erase r, a s * D r s) / 2 := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    have hswap : ∑ r ∈ S, ∑ s ∈ S.erase r, a s * D r s
        = ∑ r ∈ S, ∑ s ∈ S.erase r, a r * D r s := by
      have := sum_offDiag_comm S (fun r s => a s * D r s)
      rw [this]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      rw [hD]
      simp [abs_sub_comm]
    rw [hsplit, hswap]
    have : ∑ r ∈ S, ∑ s ∈ S.erase r, a r * D r s
        = ∑ r ∈ S, a r * ∑ s ∈ S.erase r, D r s := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
    rw [this]
    ring
  rw [hsymm] at hnorm
  refine le_trans hnorm ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hrow : ∑ s ∈ S.erase r, D r s ≤ 2 * (harmonic S.card : ℝ) / δ :=
    sum_inv_dist_le hδ hsep hr
  have hapos : 0 ≤ a r := by rw [ha]; positivity
  calc a r * ∑ s ∈ S.erase r, D r s ≤ a r * (2 * (harmonic S.card : ℝ) / δ) := by
        exact mul_le_mul_of_nonneg_left hrow hapos
    _ = 2 * (harmonic S.card : ℝ) / δ * ‖x r‖ ^ 2 := by rw [ha]; ring

/-- **The free bound**, in the shape of `GeneralizedHilbertInequality`: the Montgomery–Vaughan
constant `π` is replaced by the harmonic number `2 H_n`, which is what the triangle inequality
and the separation alone give. -/
theorem hilbert_free_bound {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 2 * (harmonic n : ℝ) / δ * ∑ r, ‖x r‖ ^ 2 := by
  have h := hilbert_free_bound_finset (S := (Finset.univ : Finset (Fin n))) (lam := lam)
    hδ (fun r _ s _ hrs => hsep r s hrs) x
  simpa using h

/-- The free bound with the harmonic number estimated by `1 + log n`. -/
theorem hilbert_free_bound_log {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
        ((lam r : ℂ) - (lam s : ℂ))‖
      ≤ 2 * (1 + Real.log n) / δ * ∑ r, ‖x r‖ ^ 2 := by
  refine le_trans (hilbert_free_bound lam x hδ hsep) ?_
  have hH : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have hsum : (0 : ℝ) ≤ ∑ r, ‖x r‖ ^ 2 := by positivity
  have hstep : 2 * (harmonic n : ℝ) / δ ≤ 2 * (1 + Real.log n) / δ := by
    have hinv : (0 : ℝ) < δ⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hinv.le
  exact mul_le_mul_of_nonneg_right hstep hsum

end Hilbert

end RiemannHypothesis
