/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EightyPercentRoute
import RiemannHypothesis.ZeroMultiplicityBound
import RiemannHypothesis.ZeroInfinite

/-!
# The multiple-zero half of Speiser's transfer

Speiser's theorem says that the Riemann hypothesis is equivalent to `ξ′` having no zero to the
left of the critical line, and its counting form (Levinson–Montgomery) compares the number of
zeroes of `ζ` off the critical line with the number of zeroes of `ξ′` that are off the line or
multiple.  That counting form is stated, but *not* proved, in
`RiemannHypothesis.EightyPercentRoute` (as the `Prop` `SpeiserTransfer`): proving it needs the
argument principle for `ξ′/ξ` on the left half of the critical strip.

This file proves the part of the transfer that is purely local, and therefore unconditional:
the part carried by the *multiple* zeroes.  Since `ξ` is entire and, inside the critical strip,
vanishes exactly where `ζ` does and to the same order, a zero of `ζ` of multiplicity `m` is a
zero of `ξ′` of multiplicity `m − 1`.  In particular a *multiple* zero of `ζ` off the critical
line is a zero of `ξ′` off the critical line — one of the two sources of "bad" `ξ′` zeroes that
`SpeiserTransfer` counts.  Nothing here proves `SpeiserTransfer`, whose content is the transfer
for the *simple* zeroes.

## Main results

* `analyticOrderAt_xiDerivFn_add_one` — `ord_{ξ′}(ρ) + 1 = ord_ζ(ρ)` at a nontrivial zero `ρ`,
  and `xiDerivMultiplicity_add_one`, the same in terms of the multiplicities.
* `xiDerivFn_eq_zero_of_multiple` — a multiple nontrivial zero of `ζ` is a zero of `ξ′`.
* `xiDerivFn_ne_zero_of_simple` — a simple nontrivial zero of `ζ` is *not* a zero of `ξ′`; so
  the multiple zeroes are exactly the ones this local argument transfers, which is why the
  counting form of Speiser's theorem needs a global input.
* `ncard_windowZerosOffLineMultiple_le_bad` — the counting form of what is proved here: the
  number of multiple off-line zeroes of `ζ` in a window is at most the `ξ′` bad count
  `N_{ξ′} − N₀ˢ_{ξ′}`, which is the inequality `SpeiserTransfer` asserts for *all* the off-line
  zeroes (and with an `O(log T)` term, which is not needed here).
* `ncard_windowZerosOffLineMultiple_le_windowCount` — hence, unconditionally, at most
  `13.136 %` of the zeroes of `ζ` are both multiple and off the critical line.
* `windowMultipleOffLineExcess_le_bad` and `windowMultipleOffLineExcess_le_windowCount` — the
  same two bounds with each multiple off-line zero weighted by its excess multiplicity
  `m_ζ(ρ) − 1` rather than counted once.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- `ξ` is not identically zero, so all its vanishing orders are finite. -/
theorem analyticOrderAt_xiFn_ne_top (s : ℂ) : analyticOrderAt xiFn s ≠ ⊤ :=
  analyticOrderAt_ne_top differentiable_xiFn xiFn_two_ne_zero s

/-- **`ξ′` loses exactly one order of vanishing at a zero of `ζ`.**  At a zero `ρ` of `ζ` in the
open critical strip, `ord_{ξ′}(ρ) + 1 = ord_ζ(ρ)`. -/
theorem analyticOrderAt_xiDerivFn_add_one {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    analyticOrderAt xiDerivFn s + 1 = analyticOrderAt riemannZeta s := by
  have hxi : xiFn s = 0 := xiFn_eq_zero_of_zeta h0 h1 hz
  have hkey := (differentiable_xiFn.analyticAt s).analyticOrderAt_deriv_add_one
  rw [hxi] at hkey
  simp only [sub_zero] at hkey
  rw [xiDerivFn, hkey, analyticOrderAt_xiFn_eq h0 h1]

/-- The vanishing order of `ξ′` at a zero of `ζ` in the strip is finite. -/
theorem analyticOrderAt_xiDerivFn_ne_top {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : analyticOrderAt xiDerivFn s ≠ ⊤ := by
  intro htop
  have h := analyticOrderAt_xiDerivFn_add_one h0 h1 hz
  rw [htop] at h
  rw [← analyticOrderAt_xiFn_eq h0 h1] at h
  exact analyticOrderAt_xiFn_ne_top s (by simpa using h.symm)

/-- **The multiplicity form.**  At a zero `ρ` of `ζ` in the open critical strip, the
multiplicity of `ρ` as a zero of `ξ′` is one less than its multiplicity as a zero of `ζ`. -/
theorem xiDerivMultiplicity_add_one {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : xiDerivMultiplicity s + 1 = zeroMultiplicity s := by
  have h := analyticOrderAt_xiDerivFn_add_one h0 h1 hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_xiDerivFn_ne_top h0 h1 hz)
  have hcast : ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
  unfold xiDerivMultiplicity zeroMultiplicity
  rw [← h, ← hn, hcast]
  simp only [ENat.toNat_natCast]

/-- **A multiple nontrivial zero of `ζ` is a zero of `ξ′`.**  This is the local — and
unconditional — half of Speiser's transfer: it moves every zero of `ζ` of multiplicity at least
two to a zero of `ξ′` at the *same point*, hence on the same side of the critical line. -/
theorem xiDerivFn_eq_zero_of_multiple {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (hm : 2 ≤ zeroMultiplicity s) : xiDerivFn s = 0 := by
  by_contra hne
  have hord : analyticOrderAt xiDerivFn s = 0 :=
    ((differentiable_xiFn.analyticAt s).deriv.congr
      (Filter.EventuallyEq.rfl : xiDerivFn =ᶠ[nhds s] deriv xiFn)).analyticOrderAt_eq_zero.2 hne
  have h := analyticOrderAt_xiDerivFn_add_one h0 h1 hz
  rw [hord, zero_add] at h
  have : zeroMultiplicity s = 1 := by
    unfold zeroMultiplicity
    rw [← h]
    rfl
  omega

/-- Conversely, a *simple* nontrivial zero of `ζ` is not a zero of `ξ′`: this local argument
transfers the multiple zeroes and nothing else, which is why the counting form of Speiser's
theorem needs a global (argument-principle) input. -/
theorem xiDerivFn_ne_zero_of_simple {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (hm : zeroMultiplicity s = 1) : xiDerivFn s ≠ 0 := by
  have hxiAt : AnalyticAt ℂ xiDerivFn s :=
    (differentiable_xiFn.analyticAt s).deriv.congr
      (Filter.EventuallyEq.rfl : xiDerivFn =ᶠ[nhds s] deriv xiFn)
  refine hxiAt.analyticOrderAt_eq_zero.1 ?_
  have h := xiDerivMultiplicity_add_one h0 h1 hz
  rw [hm] at h
  have hzero : xiDerivMultiplicity s = 0 := by omega
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_xiDerivFn_ne_top h0 h1 hz)
  rw [← hn]
  unfold xiDerivMultiplicity at hzero
  rw [← hn] at hzero
  simpa using hzero

/-! ## The counting form of the multiple-zero transfer -/

/-- The zeroes of `ξ′` in the window that lie off the critical line. -/
def xiDerivWindowZerosOffLine (T₁ T₂ : ℝ) : Set ℂ :=
  xiDerivWindowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re ≠ 1 / 2}

/-- A zero of `ξ′` has multiplicity at least one. -/
theorem one_le_xiDerivMultiplicity {ρ : ℂ} (h : xiDerivFn ρ = 0) : 1 ≤ xiDerivMultiplicity ρ := by
  rw [xiDerivMultiplicity_eq]
  exact (Zeta23.XiPrime.one_le_xiDerivMult_iff ρ).2 (by rwa [← xiDerivFn_eq])

/-- The off-line zeroes of `ξ′`, **counted with multiplicity**, and its simple on-line zeroes are
counted separately inside `N_{ξ′}`. -/
theorem sum_xiDerivMultiplicity_offLine_add_simpleOnLine_le (T₁ T₂ : ℝ) :
    (∑ᶠ ρ ∈ xiDerivWindowZerosOffLine T₁ T₂, xiDerivMultiplicity ρ) +
      xiDerivWindowCountSimpleOnLine T₁ T₂ ≤ xiDerivWindowCount T₁ T₂ := by
  classical
  have hZ : (xiDerivWindowZeros T₁ T₂).Finite := xiDerivWindowZeros_finite T₁ T₂
  set s : Finset ℂ := hZ.toFinset with hs
  set sA : Finset ℂ := s.filter (fun ρ => ρ.re ≠ 1 / 2) with hsA
  set sB : Finset ℂ := s.filter (fun ρ => ρ.re = 1 / 2 ∧ xiDerivMultiplicity ρ = 1) with hsB
  have hA : xiDerivWindowZerosOffLine T₁ T₂ = ↑sA := by
    ext ρ
    simp [hsA, hs, xiDerivWindowZerosOffLine, Set.Finite.mem_toFinset]
  have hB : xiDerivWindowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | xiDerivMultiplicity ρ = 1} = ↑sB := by
    ext ρ
    simp only [hsB, hs, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    tauto
  have hcount : xiDerivWindowCount T₁ T₂ = ∑ ρ ∈ s, xiDerivMultiplicity ρ := by
    rw [xiDerivWindowCount, finsum_mem_eq_finite_toFinset_sum _ hZ]
  have hdisj : Disjoint sA sB := by
    refine Finset.disjoint_left.2 fun ρ hρA hρB => ?_
    rw [hsA, Finset.mem_filter] at hρA
    rw [hsB, Finset.mem_filter] at hρB
    exact hρA.2 hρB.2.1
  have hsub : sA ∪ sB ⊆ s := by
    intro ρ hρ
    rcases Finset.mem_union.1 hρ with h | h
    · exact (Finset.mem_filter.1 h).1
    · exact (Finset.mem_filter.1 h).1
  have hcardB : sB.card ≤ ∑ ρ ∈ sB, xiDerivMultiplicity ρ := by
    have := Finset.card_nsmul_le_sum sB (fun ρ => xiDerivMultiplicity ρ) 1 ?_
    · simpa using this
    · intro ρ hρ
      rw [hsB, Finset.mem_filter] at hρ
      exact le_of_eq hρ.2.2.symm
  calc (∑ᶠ ρ ∈ xiDerivWindowZerosOffLine T₁ T₂, xiDerivMultiplicity ρ) +
        xiDerivWindowCountSimpleOnLine T₁ T₂
      = ∑ ρ ∈ sA, xiDerivMultiplicity ρ + sB.card := by
        rw [hA, finsum_mem_coe_finset, xiDerivWindowCountSimpleOnLine, hB, Set.ncard_coe_finset]
    _ ≤ ∑ ρ ∈ sA, xiDerivMultiplicity ρ + ∑ ρ ∈ sB, xiDerivMultiplicity ρ :=
        Nat.add_le_add_left hcardB _
    _ = ∑ ρ ∈ sA ∪ sB, xiDerivMultiplicity ρ := (Finset.sum_union hdisj).symm
    _ ≤ ∑ ρ ∈ s, xiDerivMultiplicity ρ := Finset.sum_le_sum_of_subset hsub
    _ = xiDerivWindowCount T₁ T₂ := hcount.symm

/-- Each off-line zero of `ξ′` contributes at least one to the multiplicity-weighted count. -/
theorem ncard_le_sum_xiDerivMultiplicity_offLine (T₁ T₂ : ℝ) :
    (xiDerivWindowZerosOffLine T₁ T₂).ncard ≤
      ∑ᶠ ρ ∈ xiDerivWindowZerosOffLine T₁ T₂, xiDerivMultiplicity ρ := by
  classical
  have hfin : (xiDerivWindowZerosOffLine T₁ T₂).Finite :=
    (xiDerivWindowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
  refine le_trans (le_of_eq (by simp)) (Finset.card_nsmul_le_sum _ _ 1 ?_)
  intro ρ hρ
  exact one_le_xiDerivMultiplicity (Set.Finite.mem_toFinset hfin |>.1 hρ).1.1

/-- The off-line zeroes of `ξ′` and its simple on-line zeroes are counted separately inside
`N_{ξ′}`. -/
theorem ncard_xiDerivWindowZerosOffLine_add_simpleOnLine_le (T₁ T₂ : ℝ) :
    (xiDerivWindowZerosOffLine T₁ T₂).ncard + xiDerivWindowCountSimpleOnLine T₁ T₂ ≤
      xiDerivWindowCount T₁ T₂ :=
  le_trans (Nat.add_le_add_right (ncard_le_sum_xiDerivMultiplicity_offLine T₁ T₂) _)
    (sum_xiDerivMultiplicity_offLine_add_simpleOnLine_le T₁ T₂)

/-- The nontrivial zeroes of `ζ` in the window that lie off the critical line **and** are
multiple. -/
def windowZerosOffLineMultiple (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ windowZerosOffLine T₁ T₂ | 2 ≤ zeroMultiplicity ρ}

/-- **Speiser's transfer for the multiple zeroes.**  Every multiple zero of `ζ` off the critical
line is a zero of `ξ′` off the critical line. -/
theorem windowZerosOffLineMultiple_subset (T₁ T₂ : ℝ) :
    windowZerosOffLineMultiple T₁ T₂ ⊆ xiDerivWindowZerosOffLine T₁ T₂ := by
  rintro ρ ⟨⟨⟨⟨hz, h0, h1⟩, hw⟩, hoff⟩, hmult⟩
  exact ⟨⟨xiDerivFn_eq_zero_of_multiple h0 h1 hz hmult, hw⟩, hoff⟩

/-- The counting form of the transfer: the multiple off-line zeroes of `ζ` are at most the
off-line zeroes of `ξ′`. -/
theorem ncard_windowZerosOffLineMultiple_le (T₁ T₂ : ℝ) :
    (windowZerosOffLineMultiple T₁ T₂).ncard ≤ (xiDerivWindowZerosOffLine T₁ T₂).ncard :=
  Set.ncard_le_ncard (windowZerosOffLineMultiple_subset T₁ T₂)
    ((xiDerivWindowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1)

/-- **The unconditional part of `SpeiserTransfer`.**  The number of *multiple* zeroes of `ζ` off
the critical line in a window is at most the `ξ′` bad count `N_{ξ′} − N₀ˢ_{ξ′}` of that window —
the inequality that `SpeiserTransfer` asserts for *all* the off-line zeroes, and that is proved
here for the multiple ones (with no `O(log T)` term).  The simple off-line zeroes are exactly
what this local argument does not reach. -/
theorem ncard_windowZerosOffLineMultiple_le_bad (T₁ T₂ : ℝ) :
    ((windowZerosOffLineMultiple T₁ T₂).ncard : ℝ) ≤ xiDerivWindowCountBad T₁ T₂ := by
  have h := ncard_xiDerivWindowZerosOffLine_add_simpleOnLine_le T₁ T₂
  have h' := ncard_windowZerosOffLineMultiple_le T₁ T₂
  have hcast : ((windowZerosOffLineMultiple T₁ T₂).ncard : ℝ) +
      (xiDerivWindowCountSimpleOnLine T₁ T₂ : ℝ) ≤ (xiDerivWindowCount T₁ T₂ : ℝ) := by
    exact_mod_cast le_trans (Nat.add_le_add_right h' _) h
  rw [xiDerivWindowCountBad]
  linarith

/-! ### The multiplicity-weighted form -/

/-- The **excess multiplicity** carried by the multiple off-line zeroes of `ζ` in a window: each
such zero is counted `m_ζ(ρ) − 1` times, not once. -/
def windowMultipleOffLineExcess (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ windowZerosOffLineMultiple T₁ T₂, (zeroMultiplicity ρ - 1)

/-- The excess multiplicity of `ζ` at a multiple off-line zero is exactly the multiplicity of
`ξ′` there. -/
theorem windowMultipleOffLineExcess_eq (T₁ T₂ : ℝ) :
    windowMultipleOffLineExcess T₁ T₂ =
      ∑ᶠ ρ ∈ windowZerosOffLineMultiple T₁ T₂, xiDerivMultiplicity ρ := by
  refine finsum_mem_congr rfl ?_
  rintro ρ ⟨⟨⟨⟨hz, h0, h1⟩, _⟩, _⟩, _⟩
  have := xiDerivMultiplicity_add_one h0 h1 hz
  omega

/-- Weighted by multiplicity, the multiple off-line zeroes of `ζ` are still dominated by the
off-line zeroes of `ξ′`. -/
theorem sum_xiDerivMultiplicity_multiple_le (T₁ T₂ : ℝ) :
    (∑ᶠ ρ ∈ windowZerosOffLineMultiple T₁ T₂, xiDerivMultiplicity ρ) ≤
      ∑ᶠ ρ ∈ xiDerivWindowZerosOffLine T₁ T₂, xiDerivMultiplicity ρ := by
  classical
  have hOff : (xiDerivWindowZerosOffLine T₁ T₂).Finite :=
    (xiDerivWindowZeros_finite T₁ T₂).subset fun _ hρ => hρ.1
  have hW : (windowZerosOffLineMultiple T₁ T₂).Finite :=
    hOff.subset (windowZerosOffLineMultiple_subset T₁ T₂)
  rw [finsum_mem_eq_finite_toFinset_sum _ hW, finsum_mem_eq_finite_toFinset_sum _ hOff]
  exact Finset.sum_le_sum_of_subset
    (Set.Finite.toFinset_subset_toFinset.2 (windowZerosOffLineMultiple_subset T₁ T₂))

/-- **The multiplicity-weighted form of the unconditional transfer.**  Counting each multiple
off-line zero of `ζ` with its excess multiplicity `m_ζ(ρ) − 1`, the total is still at most the
`ξ′` bad count of the window. -/
theorem windowMultipleOffLineExcess_le_bad (T₁ T₂ : ℝ) :
    (windowMultipleOffLineExcess T₁ T₂ : ℝ) ≤ xiDerivWindowCountBad T₁ T₂ := by
  have h := le_trans (Nat.add_le_add_right
    (le_trans (le_of_eq (windowMultipleOffLineExcess_eq T₁ T₂))
      (sum_xiDerivMultiplicity_multiple_le T₁ T₂)) (xiDerivWindowCountSimpleOnLine T₁ T₂))
    (sum_xiDerivMultiplicity_offLine_add_simpleOnLine_le T₁ T₂)
  have hcast : (windowMultipleOffLineExcess T₁ T₂ : ℝ) +
      (xiDerivWindowCountSimpleOnLine T₁ T₂ : ℝ) ≤ (xiDerivWindowCount T₁ T₂ : ℝ) := by
    exact_mod_cast h
  rw [xiDerivWindowCountBad]
  linarith

/-- **At most `13.136 %` of the zeroes of `ζ`, counted with their excess multiplicity, are
multiple and off the critical line.** -/
theorem windowMultipleOffLineExcess_le_windowCount {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      (windowMultipleOffLineExcess T (2 * T) : ℝ) ≤
        (0.13136 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨S, hS⟩ := xiDerivWindowCountBad_le hε
  exact ⟨S, fun T hT => le_trans (windowMultipleOffLineExcess_le_bad T (2 * T)) (hS T hT)⟩

/-- **At most `13.136 %` of the zeroes of `ζ` are multiple and off the critical line** — an
unconditional consequence, for this restricted count, of the `86.864 %` theorem for `ξ′`.  (The
same bound for *all* the off-line zeroes is what `SpeiserTransfer` would give, and it is not
proved.) -/
theorem ncard_windowZerosOffLineMultiple_le_windowCount {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      ((windowZerosOffLineMultiple T (2 * T)).ncard : ℝ) ≤
        (0.13136 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨S, hS⟩ := xiDerivWindowCountBad_le hε
  exact ⟨S, fun T hT => le_trans (ncard_windowZerosOffLineMultiple_le_bad T (2 * T)) (hS T hT)⟩

end RiemannHypothesis

end
