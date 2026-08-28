/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CriticalLine
import RiemannHypothesis.Xi
import RiemannHypothesis.ZeroSymmetryCount

/-!
# The ordinates of the zeroes on the critical line are unbounded

`RiemannHypothesis.CriticalLine` proves Hardy's theorem — the set `criticalLineZeroSet` of
zeroes of `ζ` on the line `re s = 1/2` is infinite — and its strengthening to simple zeroes.
Infinitude on its own does not say *where* those zeroes are; this file locates them along the
line, and transfers the statement to the Riemann `Ξ` function of `RiemannHypothesis.Xi`.

## Main results

* `exists_mem_criticalLineZeroSet_lt_im`, `exists_mem_criticalLineZeroSet_im_lt`: above every
  height there is a zero of `ζ` on the critical line, and below every height there is one too.
* `exists_mem_simpleCriticalLineZeroSet_lt_im`: the same, with the zero *simple*.
* `infinite_setOf_riemannXi_ofReal_eq_zero`: **`Ξ` has infinitely many real zeroes**, and
  `not_bddAbove_setOf_riemannXi_ofReal_eq_zero`,
  `not_bddBelow_setOf_riemannXi_ofReal_eq_zero`: they are unbounded in both directions.

The proofs use only what is already in the repository: the divergence of the counting
functions along the line (`tendsto_windowCountOnLine_atTop`,
`tendsto_windowCountSimpleOnLine_atTop`), the conjugation symmetry of the zero set
(`conj_mem_nontrivialZeroSet`), and the description of the zeroes of `Ξ`
(`riemannXi_eq_zero_iff`).
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-- The zeroes in a window form a finite set. -/
lemma finite_windowZeros (T₁ T₂ : ℝ) : (windowZeros T₁ T₂).Finite := by
  rw [windowZeros_eq]
  exact Zeta23.zerosIn_finite T₁ T₂

/-! ## Zeroes on the line above every height -/

/-- If every zero of `ζ` on the critical line had ordinate at most `T`, the counting function
`N₀*(0, ·)` would be bounded — but it tends to infinity.  Hence there are zeroes on the line of
arbitrarily large ordinate. -/
theorem exists_mem_criticalLineZeroSet_lt_im (T : ℝ) :
    ∃ s ∈ criticalLineZeroSet, T < s.im := by
  by_contra hcon
  push Not at hcon
  set T₀ : ℝ := max T 0 with hT₀
  -- with all ordinates at most `T`, the window `(0, T']` sees no more than the window `(0, T₀]`
  have hmono : ∀ T' : ℝ, windowCountOnLine 0 T' ≤ windowCountOnLine 0 T₀ := by
    intro T'
    unfold windowCountOnLine
    refine Set.ncard_le_ncard ?_ ((finite_windowZeros 0 T₀).subset fun s hs => hs.1)
    rintro s ⟨⟨hmem, hpos, -⟩, hre⟩
    exact ⟨⟨hmem, hpos, le_trans (hcon s ⟨hmem.1, hre⟩) (le_max_left _ _)⟩, hre⟩
  obtain ⟨T', hT'⟩ :=
    (tendsto_windowCountOnLine_atTop.eventually_ge_atTop
      ((windowCountOnLine 0 T₀ : ℝ) + 1)).exists
  have : ((windowCountOnLine 0 T' : ℕ) : ℝ) ≤ (windowCountOnLine 0 T₀ : ℝ) := by
    exact_mod_cast hmono T'
  linarith

/-- The same for *simple* zeroes: above every height there is a simple zero of `ζ` on the
critical line. -/
theorem exists_mem_simpleCriticalLineZeroSet_lt_im (T : ℝ) :
    ∃ s ∈ simpleCriticalLineZeroSet, T < s.im := by
  by_contra hcon
  push Not at hcon
  set T₀ : ℝ := max T 0 with hT₀
  have hmono : ∀ T' : ℝ, windowCountSimpleOnLine 0 T' ≤ windowCountSimpleOnLine 0 T₀ := by
    intro T'
    unfold windowCountSimpleOnLine
    refine Set.ncard_le_ncard ?_ ((finite_windowZeros 0 T₀).subset fun s hs => hs.1.1)
    rintro s ⟨⟨⟨hmem, hpos, -⟩, hre⟩, hmult⟩
    exact ⟨⟨⟨hmem, hpos,
      le_trans (hcon s ⟨hmem.1, hre, hmult⟩) (le_max_left _ _)⟩, hre⟩, hmult⟩
  obtain ⟨T', hT'⟩ :=
    (tendsto_windowCountSimpleOnLine_atTop.eventually_ge_atTop
      ((windowCountSimpleOnLine 0 T₀ : ℝ) + 1)).exists
  have : ((windowCountSimpleOnLine 0 T' : ℕ) : ℝ) ≤ (windowCountSimpleOnLine 0 T₀ : ℝ) := by
    exact_mod_cast hmono T'
  linarith

/-- The zero set on the line is stable under conjugation. -/
theorem conj_mem_criticalLineZeroSet {s : ℂ} (hs : s ∈ criticalLineZeroSet) :
    (starRingEnd ℂ) s ∈ criticalLineZeroSet := by
  obtain ⟨hz, -, -⟩ :=
    conj_mem_nontrivialZeroSet (criticalLineZeroSet_subset_nontrivialZeroSet hs)
  exact ⟨hz, by simpa using hs.2⟩

/-- Below every height there is a zero of `ζ` on the critical line. -/
theorem exists_mem_criticalLineZeroSet_im_lt (T : ℝ) :
    ∃ s ∈ criticalLineZeroSet, s.im < T := by
  obtain ⟨s, hs, hlt⟩ := exists_mem_criticalLineZeroSet_lt_im (-T)
  exact ⟨(starRingEnd ℂ) s, conj_mem_criticalLineZeroSet hs, by
    rw [Complex.conj_im]; linarith⟩

/-! ## The real zeroes of `Ξ` -/

/-- A real number `t` is a zero of `Ξ` exactly when `1/2 + i t` is a zero of `ζ`. -/
theorem riemannXi_ofReal_eq_zero_iff (t : ℝ) :
    riemannXi (t : ℂ) = 0 ↔ xiPoint (t : ℂ) ∈ criticalLineZeroSet := by
  have hre : (xiPoint (t : ℂ)).re = 1 / 2 := by simp [xiPoint]
  rw [riemannXi_eq_zero_iff]
  constructor
  · rintro ⟨-, -, hz⟩
    exact ⟨hz, hre⟩
  · rintro ⟨hz, -⟩
    exact ⟨by rw [hre]; norm_num, by rw [hre]; norm_num, hz⟩

/-- **The Riemann `Ξ` function has infinitely many real zeroes** — Hardy's theorem in the
`Ξ`-variable. -/
theorem infinite_setOf_riemannXi_ofReal_eq_zero :
    {t : ℝ | riemannXi (t : ℂ) = 0}.Infinite := by
  have himg : criticalLineZeroSet ⊆
      (fun t : ℝ => xiPoint (t : ℂ)) '' {t : ℝ | riemannXi (t : ℂ) = 0} := by
    intro s hs
    have hpt : xiPoint ((s.im : ℝ) : ℂ) = s := by
      apply Complex.ext <;> simp [xiPoint, hs.2]
    have hzero : riemannXi ((s.im : ℝ) : ℂ) = 0 := by
      rw [riemannXi_ofReal_eq_zero_iff, hpt]
      exact hs
    exact ⟨s.im, hzero, hpt⟩
  exact Set.Infinite.of_image _ (infinite_criticalLineZeroSet.mono himg)

/-- The real zeroes of `Ξ` are unbounded above. -/
theorem exists_riemannXi_ofReal_eq_zero_lt (T : ℝ) :
    ∃ t : ℝ, T < t ∧ riemannXi (t : ℂ) = 0 := by
  obtain ⟨s, hs, hlt⟩ := exists_mem_criticalLineZeroSet_lt_im T
  have hpt : xiPoint ((s.im : ℝ) : ℂ) = s := by
    apply Complex.ext <;> simp [xiPoint, hs.2]
  exact ⟨s.im, hlt, by rw [riemannXi_ofReal_eq_zero_iff, hpt]; exact hs⟩

/-- The real zeroes of `Ξ` are unbounded below: below every height there is one. -/
theorem exists_riemannXi_ofReal_eq_zero_gt (T : ℝ) :
    ∃ t : ℝ, t < T ∧ riemannXi (t : ℂ) = 0 := by
  obtain ⟨s, hs, hlt⟩ := exists_mem_criticalLineZeroSet_im_lt T
  have hpt : xiPoint ((s.im : ℝ) : ℂ) = s := by
    apply Complex.ext <;> simp [xiPoint, hs.2]
  exact ⟨s.im, hlt, by rw [riemannXi_ofReal_eq_zero_iff, hpt]; exact hs⟩

/-- The set of real zeroes of `Ξ` is not bounded above. -/
theorem not_bddAbove_setOf_riemannXi_ofReal_eq_zero :
    ¬ BddAbove {t : ℝ | riemannXi (t : ℂ) = 0} := by
  rintro ⟨B, hB⟩
  obtain ⟨t, hlt, ht⟩ := exists_riemannXi_ofReal_eq_zero_lt B
  exact absurd (hB ht) (not_le.2 hlt)

/-- The set of real zeroes of `Ξ` is not bounded below. -/
theorem not_bddBelow_setOf_riemannXi_ofReal_eq_zero :
    ¬ BddBelow {t : ℝ | riemannXi (t : ℂ) = 0} := by
  rintro ⟨B, hB⟩
  obtain ⟨t, hlt, ht⟩ := exists_riemannXi_ofReal_eq_zero_gt B
  exact absurd (hB ht) (not_le.2 hlt)

end RiemannHypothesis

end
