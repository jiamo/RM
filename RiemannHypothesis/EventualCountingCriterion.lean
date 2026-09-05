/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeta23Verification
import RiemannHypothesis.Symmetry

/-!
# The Riemann hypothesis is an *eventual* counting statement

The two-thirds theorem (`RiemannHypothesis.two_thirds_on_critical_line_cumulative`) says that
the proportion of zeroes on the critical line is at least `2/3` in the limit.  The obvious
question is what separates that from the Riemann hypothesis, and the naive answer — "raise the
proportion to `1`, and then check the finitely many low zeroes by hand" — is *too pessimistic*:
no low-height verification is needed at all.

An off-line zero is a permanent, fixed deficiency.  If `ζ` had a zero `ρ` off the critical line,
then `ρ` (or its conjugate — and `ρ` cannot be real, `riemannZeta_ofReal_ne_zero_of_lt_one`) has
positive ordinate `γ`, and then *every* window `(0, T]` with `T ≥ γ` misses it: the on-line count
is strictly below the total count, for ever after.  So an asymptotic statement is enough:

* `zetaStripForm_of_eventually_windowCountOnLine_eq` — if the on-line and the total distinct
  counts agree for all sufficiently large `T`, the Riemann hypothesis holds;
* `zetaStripForm_iff_eventually_windowCountOnLine_eq` — the equivalence;
* `zetaStripForm_iff_eventually_windowCountOnLine_eq_windowCount` — the same with the total
  counted *with multiplicity*, the exact denominator of the two-thirds theorem, so that the
  criterion is stated in the very quantity that theorem bounds;
* `zetaStripForm_iff_eventually_windowCountDistinct_le` — the same in the shape the two-thirds
  theorem approximates: the conjecture is the endpoint `c = 1` of the family of statements
  `(c − ε)·N ≤ N₀*`, of which `c = 2/3` is proved.

This is where the repository's strongest unconditional result stands relative to the conjecture:
what is proved is `liminf N₀*(0,T)/N(0,T) ≥ 2/3`, and what the conjecture needs is
`N₀*(0,T) = N(0,T)` for all large `T`.  Nothing here proves the conjecture, and the gap is the
whole difficulty; what these theorems remove is only the belief that a separate finite
verification of the low zeroes would also be required.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace RiemannHypothesis

/-- The zeroes of a window form a finite set (through the vendored library's seam facts, which
are classical facts about `ζ`: isolated zeroes and the pole at `1`). -/
lemma finite_windowZeros (T₁ T₂ : ℝ) : (windowZeros T₁ T₂).Finite := by
  have h := Zeta23.zetaSeam.finite_window T₁ T₂
  refine h.subset ?_
  rintro ρ ⟨⟨hz, h0, h1⟩, hT₁, hT₂⟩
  exact ⟨⟨hz, h0, h1⟩, hT₁, hT₂⟩

/-- If the Riemann hypothesis fails, some zero off the critical line has **positive** ordinate:
`ζ` has no real zero in `(0, 1)`, and the zero set is stable under conjugation. -/
lemma exists_offLine_pos_im_of_not_zetaStripForm (h : ¬ ZetaStripForm) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2 ∧ 0 < ρ.im := by
  unfold ZetaStripForm at h
  push Not at h
  obtain ⟨ρ, h0, h1, hz, hre⟩ := h
  rcases lt_trichotomy ρ.im 0 with him | him | him
  · refine ⟨(starRingEnd ℂ) ρ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [riemannZeta_conj_of_mem_strip h0 h1, hz, map_zero]
    · simpa using h0
    · simpa using h1
    · simpa using hre
    · simpa using him
  · exfalso
    have hρ : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hρ] at hz
    exact riemannZeta_ofReal_ne_zero_of_lt_one h0 h1 hz
  · exact ⟨ρ, hz, h0, h1, hre, him⟩

/-- **The Riemann hypothesis from an eventual count.**  If, for all sufficiently large `T`, every
nontrivial zero of ordinate in `(0, T]` is on the critical line *in the sense of counting* —
`N₀*(0,T) = N_d(0,T)` — then every nontrivial zero is on the critical line.  No verification of
the low zeroes is needed: an off-line zero would spoil the count at every height above it. -/
theorem zetaStripForm_of_eventually_windowCountOnLine_eq
    (h : ∀ᶠ T in atTop, windowCountOnLine 0 T = windowCountDistinct 0 T) : ZetaStripForm := by
  by_contra hRH
  obtain ⟨ρ, hz, h0, h1, hre, him⟩ := exists_offLine_pos_im_of_not_zetaStripForm hRH
  obtain ⟨T, hT, hTρ⟩ := (h.and (eventually_ge_atTop ρ.im)).exists
  have hmem : ρ ∈ windowZeros 0 T := ⟨⟨hz, h0, h1⟩, him, hTρ⟩
  have hssub : windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ⊂ windowZeros 0 T := by
    refine ⟨inter_subset_left, fun hsub => ?_⟩
    exact hre (hsub hmem).2
  have hlt : windowCountOnLine 0 T < windowCountDistinct 0 T :=
    Set.ncard_lt_ncard hssub (finite_windowZeros 0 T)
  omega

/-- Under the Riemann hypothesis the two counts agree at *every* height. -/
theorem windowCountOnLine_eq_of_zetaStripForm (h : ZetaStripForm) (T₁ T₂ : ℝ) :
    windowCountOnLine T₁ T₂ = windowCountDistinct T₁ T₂ := by
  have hset : windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} = windowZeros T₁ T₂ :=
    inter_eq_left.2 fun ρ hρ => h ρ hρ.1.2.1 hρ.1.2.2 hρ.1.1
  rw [windowCountOnLine, windowCountDistinct, hset]

/-- **The Riemann hypothesis is exactly an eventual counting statement.**  It holds if and only
if the number of distinct zeroes on the critical line of ordinate in `(0, T]` equals the number
of distinct zeroes of ordinate in `(0, T]` for all large `T`. -/
theorem zetaStripForm_iff_eventually_windowCountOnLine_eq :
    ZetaStripForm ↔ ∀ᶠ T in atTop, windowCountOnLine 0 T = windowCountDistinct 0 T := by
  refine ⟨fun h => .of_forall fun T => windowCountOnLine_eq_of_zetaStripForm h 0 T,
    zetaStripForm_of_eventually_windowCountOnLine_eq⟩

/-- Under the Riemann hypothesis all zeroes are on the line, and there they are counted the same
way with and without multiplicity only if they are simple; the statement that survives without
simplicity is the one with the *multiplicity* count on both sides. -/
theorem windowCountOnLineMult_eq_windowCount_of_zetaStripForm (h : ZetaStripForm) (T₁ T₂ : ℝ) :
    ∑ᶠ ρ ∈ windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity ρ
      = windowCount T₁ T₂ := by
  have hset : windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} = windowZeros T₁ T₂ :=
    inter_eq_left.2 fun ρ hρ => h ρ hρ.1.2.1 hρ.1.2.2 hρ.1.1
  rw [windowCount, hset]

/-- The criterion in the exact denominator of the two-thirds theorem: the Riemann hypothesis
holds if and only if, for all large `T`, the zeroes of `(0, T]` counted with multiplicity are all
accounted for on the critical line, again counted with multiplicity. -/
theorem zetaStripForm_iff_eventually_windowCountOnLine_eq_windowCount :
    ZetaStripForm ↔ ∀ᶠ T in atTop,
      ∑ᶠ ρ ∈ windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity ρ = windowCount 0 T := by
  refine ⟨fun h => .of_forall fun T =>
    windowCountOnLineMult_eq_windowCount_of_zetaStripForm h 0 T, fun h => ?_⟩
  by_contra hRH
  obtain ⟨ρ, hz, h0, h1, hre, him⟩ := exists_offLine_pos_im_of_not_zetaStripForm hRH
  obtain ⟨T, hT, hTρ⟩ := (h.and (eventually_ge_atTop ρ.im)).exists
  -- the on-line part of the window misses `ρ`, whose multiplicity is at least one
  have hmem : ρ ∈ windowZeros 0 T := ⟨⟨hz, h0, h1⟩, him, hTρ⟩
  have hfin : (windowZeros 0 T).Finite := finite_windowZeros 0 T
  have hone : 1 ≤ zeroMultiplicity ρ := Zeta23.zetaSeam.one_le_mult ρ ⟨hz, h0, h1⟩
  classical
  have hsplit :
      ∑ᶠ σ ∈ windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity σ
        + ∑ᶠ σ ∈ windowZeros 0 T \ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity σ
        = windowCount 0 T :=
    finsum_mem_inter_add_sdiff (f := zeroMultiplicity) _ hfin
  have hdiff : (windowZeros 0 T \ {ρ : ℂ | ρ.re = 1 / 2}).Finite := hfin.sdiff
  have hpos : 0 < ∑ᶠ σ ∈ windowZeros 0 T \ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity σ := by
    have hmem' : ρ ∈ hdiff.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq]
      exact ⟨hmem, hre⟩
    have hsum : ∑ᶠ σ ∈ windowZeros 0 T \ {ρ : ℂ | ρ.re = 1 / 2}, zeroMultiplicity σ
        = ∑ σ ∈ hdiff.toFinset, zeroMultiplicity σ := by
      rw [← finsum_mem_coe_finset]
      simp
    rw [hsum]
    exact lt_of_lt_of_le hone (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem')
  omega

/-- The on-line count never exceeds the total count. -/
lemma windowCountOnLine_le_windowCountDistinct (T₁ T₂ : ℝ) :
    windowCountOnLine T₁ T₂ ≤ windowCountDistinct T₁ T₂ :=
  Set.ncard_le_ncard inter_subset_left (finite_windowZeros T₁ T₂)

/-- The criterion in the shape the two-thirds theorem approximates: the Riemann hypothesis holds
if and only if the *proportion* of distinct zeroes on the critical line is eventually at least
`1`.  The reverse inequality is free, so this is the endpoint `c = 1` of the family of
statements `(c − ε)·N ≤ N₀*` that `two_thirds_on_critical_line_cumulative` proves for `c = 2/3`.
-/
theorem zetaStripForm_iff_eventually_windowCountDistinct_le :
    ZetaStripForm ↔ ∀ᶠ T in atTop, windowCountDistinct 0 T ≤ windowCountOnLine 0 T := by
  rw [zetaStripForm_iff_eventually_windowCountOnLine_eq]
  constructor
  · exact fun h => h.mono fun T hT => hT.ge
  · exact fun h => h.mono fun T hT =>
      le_antisymm (windowCountOnLine_le_windowCountDistinct 0 T) hT

end RiemannHypothesis

end
