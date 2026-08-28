/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SpeiserRolle

/-!
# What Speiser's transfer is equivalent to, and what it would give

The zeroes of `ζ` and the zeroes of `ξ′` in a dyadic window have the same Riemann–von Mangoldt
main term, so the two counting functions differ by `O(log T)`
(`RiemannHypothesis.abs_xiDerivWindowCount_sub_windowCount_le`).  Splitting each of them into
its on-line and off-line parts (with multiplicity) therefore turns any comparison of the
off-line counts into the *opposite* comparison of the on-line counts, and conversely.  That is
the content of `speiserOffLineTransfer_iff_xiDerivOnLineDominates`.

Two consequences, which is why the file matters for the eighty per cent problem.

* **The elementary direction is a theorem.**  Rolle's theorem on the critical line
  (`RiemannHypothesis.windowCountOnLineMult_le_xiDerivWindowCountOnLineMult`) says that `ξ′` has
  at least as many zeroes on the line as `ζ` does; hence, unconditionally,
  `xiDerivWindowCountOffLineMult_le_windowCountOffLineMult` : `ξ′` has *at most* as many
  off-line zeroes as `ζ`, up to `O(log T)`.  So the `86.864 %` theorem for `ξ′` says nothing
  about `ζ` by itself: the inequality it could be pushed through points the wrong way.

* **The other direction is not a technical input.**  `SpeiserOffLineTransfer` — the inequality
  in the direction that would transfer the `ξ′` theorem to `ζ` — is *equivalent* (given the
  Riemann–von Mangoldt comparison) to the statement that `ξ′` has no more zeroes on the critical
  line than `ζ` has, up to `O(log T)`; and, by
  `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer`, it already implies that
  at least `86.864 %` of the zeroes of `ζ` lie on the critical line.  It is therefore *stronger*
  than the eighty per cent target it was introduced to reach, and assuming it is not a route to
  the target.  The unconditional proportion in this repository stays at `2/3`.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## The two hypotheses -/

/-- The off-line form of Speiser's transfer, with multiplicity: the zeroes of `ζ` off the
critical line are at most the zeroes of `ξ′` off the critical line, up to `O(log T)`.  A
`Prop`: it is **not** proved here. -/
def SpeiserOffLineTransfer : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (windowCountOffLineMult T (2 * T) : ℝ) ≤
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) + C * Real.log T

/-- The on-line form: `ξ′` has no more zeroes on the critical line than `ζ` has, up to
`O(log T)`.  A `Prop`: it is **not** proved here. -/
def XiDerivOnLineDominates : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (xiDerivWindowCountOnLineMult T (2 * T) : ℝ) ≤
      (windowCountOnLineMult T (2 * T) : ℝ) + C * Real.log T

/-! ## The splittings, as real identities -/

lemma windowCount_split_real (T₁ T₂ : ℝ) :
    (windowCountOffLineMult T₁ T₂ : ℝ) + (windowCountOnLineMult T₁ T₂ : ℝ)
      = (windowCount T₁ T₂ : ℝ) := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
    (windowCountOffLineMult_add_windowCountOnLineMult T₁ T₂)

lemma xiDerivWindowCount_split_real (T₁ T₂ : ℝ) :
    (xiDerivWindowCountOffLineMult T₁ T₂ : ℝ) + (xiDerivWindowCountOnLineMult T₁ T₂ : ℝ)
      = (xiDerivWindowCount T₁ T₂ : ℝ) := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
    (xiDerivWindowCountOffLineMult_add_onLineMult T₁ T₂)

/-! ## The equivalence -/

/-- **The off-line and the on-line forms of Speiser's transfer are equivalent.**  The Riemann–von
Mangoldt comparison of `N` and `N_{ξ′}` converts one into the other. -/
theorem speiserOffLineTransfer_iff_xiDerivOnLineDominates :
    SpeiserOffLineTransfer ↔ XiDerivOnLineDominates := by
  obtain ⟨C₀, S₀, hC₀, hS₀, hrvm⟩ := abs_xiDerivWindowCount_sub_windowCount_le
  constructor
  · rintro ⟨C, S, hS⟩
    refine ⟨C + C₀, max S S₀, fun T hT => ?_⟩
    have h1 := hS T (le_trans (le_max_left _ _) hT)
    have h2 := abs_le.1 (hrvm T (le_trans (le_max_right _ _) hT))
    have e1 := windowCount_split_real T (2 * T)
    have e2 := xiDerivWindowCount_split_real T (2 * T)
    have hlog : 0 ≤ Real.log T :=
      Real.log_nonneg (le_trans hS₀ (le_trans (le_max_right _ _) hT))
    nlinarith [h1, h2.1, h2.2, e1, e2, hlog]
  · rintro ⟨C, S, hS⟩
    refine ⟨C + C₀, max S S₀, fun T hT => ?_⟩
    have h1 := hS T (le_trans (le_max_left _ _) hT)
    have h2 := abs_le.1 (hrvm T (le_trans (le_max_right _ _) hT))
    have e1 := windowCount_split_real T (2 * T)
    have e2 := xiDerivWindowCount_split_real T (2 * T)
    have hlog : 0 ≤ Real.log T :=
      Real.log_nonneg (le_trans hS₀ (le_trans (le_max_right _ _) hT))
    nlinarith [h1, h2.1, h2.2, e1, e2, hlog]

/-! ## The elementary direction, unconditionally -/

/-- **Unconditionally, `ξ′` has at most as many off-line zeroes as `ζ`, up to `O(log T)`.**
This is the Rolle direction: `ξ′` has at least as many zeroes on the critical line as `ζ`, so it
has at most as many off it.  (The opposite inequality is `SpeiserOffLineTransfer`, which is not
proved.) -/
theorem xiDerivWindowCountOffLineMult_le_windowCountOffLineMult :
    ∃ C S : ℝ, ∀ T ≥ S,
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤
        (windowCountOffLineMult T (2 * T) : ℝ) + C * Real.log T := by
  obtain ⟨C₀, S₀, hC₀, hS₀, hrvm⟩ := abs_xiDerivWindowCount_sub_windowCount_le
  refine ⟨C₀ + 1, max S₀ (Real.exp 1), fun T hT => ?_⟩
  have h2 := abs_le.1 (hrvm T (le_trans (le_max_left _ _) hT))
  have e1 := windowCount_split_real T (2 * T)
  have e2 := xiDerivWindowCount_split_real T (2 * T)
  have hrolle : (windowCountOnLineMult T (2 * T) : ℝ) ≤
      (xiDerivWindowCountOnLineMult T (2 * T) : ℝ) + 1 := by
    exact_mod_cast windowCountOnLineMult_le_xiDerivWindowCountOnLineMult T (2 * T)
  have hlog : (1 : ℝ) ≤ Real.log T := by
    have hexp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  nlinarith [h2.1, h2.2, e1, e2, hrolle, hlog]

/-! ## What the unproved direction would give -/

/-- The simple on-line zeroes of `ξ′` are counted inside the on-line count with
multiplicity. -/
lemma xiDerivWindowCountSimpleOnLine_le_onLineMult (T₁ T₂ : ℝ) :
    xiDerivWindowCountSimpleOnLine T₁ T₂ ≤ xiDerivWindowCountOnLineMult T₁ T₂ := by
  classical
  have hfin : (xiDerivWindowZerosOnLine T₁ T₂).Finite := xiDerivWindowZerosOnLine_finite T₁ T₂
  have hsub : xiDerivWindowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | xiDerivMultiplicity ρ = 1} ⊆ xiDerivWindowZerosOnLine T₁ T₂ := fun _ hρ => hρ.1
  have hsfin : (xiDerivWindowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | xiDerivMultiplicity ρ = 1}).Finite := hfin.subset hsub
  rw [xiDerivWindowCountSimpleOnLine, xiDerivWindowCountOnLineMult,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hsfin]
  calc hsfin.toFinset.card
      ≤ ∑ ρ ∈ hsfin.toFinset, xiDerivMultiplicity ρ := by
        refine le_trans (le_of_eq (by simp)) (Finset.card_nsmul_le_sum _ _ 1 ?_)
        intro ρ hρ
        exact one_le_xiDerivMultiplicity ((Set.Finite.mem_toFinset hsfin).1 hρ).1.1.1
    _ ≤ ∑ ρ ∈ hfin.toFinset, xiDerivMultiplicity ρ := by
        refine Finset.sum_le_sum_of_subset ?_
        intro ρ hρ
        rw [Set.Finite.mem_toFinset] at hρ ⊢
        exact hsub hρ

/-- The off-line count of `ξ′`, with multiplicity, is part of its bad count. -/
lemma xiDerivWindowCountOffLineMult_le_bad (T₁ T₂ : ℝ) :
    (xiDerivWindowCountOffLineMult T₁ T₂ : ℝ) ≤ xiDerivWindowCountBad T₁ T₂ := by
  have hsplit := xiDerivWindowCountOffLineMult_add_onLineMult T₁ T₂
  have hle := xiDerivWindowCountSimpleOnLine_le_onLineMult T₁ T₂
  have : (xiDerivWindowCountOffLineMult T₁ T₂ : ℝ) +
      (xiDerivWindowCountSimpleOnLine T₁ T₂ : ℝ) ≤ (xiDerivWindowCount T₁ T₂ : ℝ) := by
    exact_mod_cast le_trans (Nat.add_le_add_left hle _) (le_of_eq hsplit)
  rw [xiDerivWindowCountBad]
  linarith

/-- `SpeiserOffLineTransfer` implies the multiplicity-weighted transfer of
`RiemannHypothesis.EightyPercentMultiplicity`. -/
theorem speiserTransferMult_of_speiserOffLineTransfer (h : SpeiserOffLineTransfer) :
    SpeiserTransferMult := by
  obtain ⟨C, S, hS⟩ := h
  exact ⟨C, S, fun T hT =>
    le_trans (hS T hT) (by linarith [xiDerivWindowCountOffLineMult_le_bad T (2 * T)])⟩

/-- **Under `SpeiserOffLineTransfer`, at least `86.864 %` of the nontrivial zeroes of `ζ`,
counted with multiplicity, lie on the critical line.**  The hypothesis therefore implies far
more than the eighty per cent target: it is not an auxiliary input on the way to it. -/
theorem eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer
    (h : SpeiserOffLineTransfer) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 - ε) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ) :=
  eighty_six_percent_on_critical_line_mult_of_speiserTransferMult
    (speiserTransferMult_of_speiserOffLineTransfer h)

/-- Consequently the eighty per cent target with multiplicity follows from
`SpeiserOffLineTransfer` — with `6.8 %` to spare, which is the precise sense in which the
hypothesis overshoots the target. -/
theorem eightyPercentOnCriticalLineMult_of_speiserOffLineTransfer
    (h : SpeiserOffLineTransfer) : EightyPercentOnCriticalLineMult :=
  eightyPercentOnCriticalLineMult_of_speiserTransferMult
    (speiserTransferMult_of_speiserOffLineTransfer h)

end RiemannHypothesis

end
