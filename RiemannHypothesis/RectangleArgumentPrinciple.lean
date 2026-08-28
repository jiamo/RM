/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.RectangleZeroCount
import Zeta23.Analytic.RectangleLogDeriv

/-!
# The argument principle on a rectangle

This is the analytic half of the rectangle infrastructure; the combinatorial half — the
definitions `rectZeros`, `rectZeroCount`, `leftCorner`, the finiteness of the zero set, and
Littlewood's counting identity — is in `RiemannHypothesis.RectangleZeroCount` and depends on
mathlib only.

Three of the open rows of the task board — Bohr–Landau (`M1-ALMOST-ALL-STRIP`), the density
theorem (`M2-DENSITY`) and any zero-counting argument for `ζ`, `ξ` or `ξ′` — need the same
missing tool: a way to turn a contour integral around a rectangle into a *count of zeroes with
multiplicity*.  Mathlib has no argument principle.  The vendored `Zeta23` library has a general
weighted form of it (`Zeta23.Analytic.rectangleIntegral'_mul_logDeriv`), but states it with the
zero set passed in as a `Finset` together with a proof that it is the zero set, and it is used
there only through function-specific wrappers.  What follows repackages it as a statement about
`rectZeroCount`, so that a counting argument can use it without carrying a `Finset` around.

* `rectangle_argument_principle` —
  `(1/2πi) ∮_{∂R} f′/f = rectZeroCount f z w`, for `f` analytic on a neighbourhood of the
  closed rectangle and nonvanishing on its border.  The right-hand side is a natural number.
* `rectangle_argument_principle_weighted` — the same with an analytic weight `g`, giving
  `∑_ρ ord_ρ(f) · g ρ`; the unweighted statement is the case `g = 1`.
* `rectangleIntegral'_logDeriv_eq_zero_of_forall_ne_zero` — the zero-free case.
* `integral_rectangleIntegral'_logDeriv_eq_finsum_of_border` — the argument principle and the
  layer-cake identity combined: the `σ`-integral of the contour integrals of `f′/f` over the
  rectangles truncated at `re s = σ` equals `∑_ρ ord_ρ(f)·(re ρ − z.re)`, assuming only that `f`
  does not vanish on the border of the rectangle itself.  Littlewood's lemma proper replaces the
  inner contour integral by `∫ log f` along the border; that step is *not* proved here.
* `integral_rectangleIntegral'_logDeriv_eq_finsum` — an earlier form of the same identity whose
  hypothesis asks zero-freeness on the border of *every* truncation.  That hypothesis turns out
  to be vacuous: `rectZeros_eq_empty_of_forall_leftCorner_border` shows it forces the zero set
  to be empty, so both sides are zero.  The statement is kept, with a warning, and superseded by
  the previous item.
* `rectangleBorder_leftCorner_subset` — the border of a truncated rectangle is contained in the
  border of the whole rectangle together with the cutting line `re s = σ`; this is what makes
  the corrected identity work for almost every `σ`.

`Rectangle` is mathlib's; `RectangleBorder`, `RectangleIntegral'` are `Zeta23`'s; the notation
`[[a, b]]` is `Set.uIcc`.

## Verification status

The session that wrote this file could not compile it against `Zeta23`, and its proofs were
only checked relative to restated signatures for the four `Zeta23` names used here —
`RectangleBorder`, `RectangleIntegral'`, `rectangleBorder_subset_rectangle`,
`Zeta23.Analytic.rectangleIntegral'_mul_logDeriv`.  That caveat is now discharged: with the
toolchain pinned to the Lean version that the mathlib revision of `lakefile.toml` requires, a
full `lake build` compiles the whole repository, this file included, so the proofs below are
checked against the real `Zeta23` declarations.  `./scripts/audit.sh` is green, and the results
here depend only on `propext`, `Classical.choice` and `Quot.sound`.

The specialization to `ζ` and `ξ` — the statement that these counts are counts of nontrivial
zeroes of `ζ`, with the analyticity and finiteness hypotheses discharged — is in
`RiemannHypothesis.ZetaRectangleCount`.
-/

open Complex Set MeasureTheory Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

variable {f g : ℂ → ℂ} {z w : ℂ}

/-- If `f` does not vanish on the border, the zero set inside the rectangle is finite. -/
theorem rectZeros_finite_of_border (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) : (rectZeros f z w).Finite := by
  have hz : z ∈ RectangleBorder z w := Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  exact rectZeros_finite hf (rectangleBorder_subset_rectangle z w hz) (hborder z hz)

/-! ## The argument principle -/

/-- **The weighted argument principle on a rectangle.**  For `f` and `g` analytic on a
neighbourhood of every point of the closed rectangle with corners `z` and `w`, and `f`
nonvanishing on its border,
`(1/2πi) ∮_{∂R} g · (f′/f) = ∑_ρ ord_ρ(f) · g ρ`, the sum being over the zeroes of `f`
inside the rectangle. -/
theorem rectangle_argument_principle_weighted (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  classical
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hborder
  have hZ : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    simp [rectZeros, hs]
  have hZsub : (hfin.toFinset : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    simpa using ((Set.Finite.mem_toFinset _).mp hs).1
  have h := rectangleIntegral'_mul_logDeriv hre him hf hg hborder hfin.toFinset hZ hZsub
  rw [h, ← finsum_mem_coe_finset]
  congr 1
  simp

/-- **The argument principle on a rectangle, in counting form.**  For `f` analytic on a
neighbourhood of every point of the closed rectangle with corners `z` and `w` and nonvanishing
on its border, `(1/2πi) ∮_{∂R} f′/f` is the number of zeroes of `f` inside the rectangle,
counted with multiplicity. -/
theorem rectangle_argument_principle (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (logDeriv f) z w = (rectZeroCount f z w : ℂ) := by
  classical
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hborder
  have h := rectangle_argument_principle_weighted (g := fun _ => (1 : ℂ)) hre him hf
    analyticOnNhd_const hborder
  simp only [mul_one, one_mul] at h
  have e1 : ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℂ)
      = ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℂ) := by
    rw [← finsum_mem_coe_finset]
    congr 1
    ext s
    simp
  have e2 : rectZeroCount f z w = ∑ ρ ∈ hfin.toFinset, analyticOrderNatAt f ρ :=
    rectZeroCount_eq_sum (fun s => by simp)
  rw [h, e1, e2]
  push_cast
  ring

/-- The contour integral of `f′/f` around a rectangle on which `f` is analytic and
nonvanishing is zero. -/
theorem rectangleIntegral'_logDeriv_eq_zero_of_forall_ne_zero (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (h : ∀ s ∈ Rectangle z w, f s ≠ 0) :
    RectangleIntegral' (logDeriv f) z w = 0 := by
  rw [rectangle_argument_principle hre him hf
      (fun s hs => h s (rectangleBorder_subset_rectangle z w hs)),
    rectZeroCount_eq_zero_of_forall_ne_zero h]
  simp

/-! ## Littlewood's identity, analytic form -/

/-- **The border of a truncated rectangle is covered by the border of the whole rectangle
together with the cutting line.**  Three of the four edges of the rectangle truncated at
`re s = σ` — bottom, top and right — are contained in the corresponding edges of the original
rectangle; the fourth, the new left edge, lies on the line `re s = σ`. -/
theorem rectangleBorder_leftCorner_subset (hre : z.re ≤ w.re) {σ : ℝ} (hσ : σ ∈ Icc z.re w.re) :
    RectangleBorder (leftCorner σ z) w ⊆ RectangleBorder z w ∪ {s : ℂ | s.re = σ} := by
  have hsub : [[σ, w.re]] ⊆ [[z.re, w.re]] :=
    Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le hre]; exact hσ) right_mem_uIcc
  rintro s (((hs | hs) | hs) | hs) <;>
    rw [Complex.mem_reProdIm] at hs <;>
    simp only [leftCorner_re, leftCorner_im, Set.mem_singleton_iff] at hs
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr ⟨hsub hs.1, hs.2⟩))))
  · exact Or.inr hs.1
  · exact Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨hsub hs.1, hs.2⟩)))
  · exact Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨hs.1, hs.2⟩))

/-- **The hypothesis of `integral_rectangleIntegral'_logDeriv_eq_finsum` is vacuous.**
Asking `f` to be nonvanishing on the border of *every* truncation of the rectangle forces `f`
to have no zero at all inside it: a zero `ρ` lies on the left edge of the rectangle truncated
at `σ = re ρ`.  So both sides of that theorem are zero whenever its hypotheses hold; the
statement is true but carries no content.  The version with content is
`integral_rectangleIntegral'_logDeriv_eq_finsum_of_border` below, whose zero-freeness
hypothesis concerns only the border of the original rectangle. -/
theorem rectZeros_eq_empty_of_forall_leftCorner_border (hre : z.re ≤ w.re)
    (hborder : ∀ σ ∈ Icc z.re w.re, ∀ s ∈ RectangleBorder (leftCorner σ z) w, f s ≠ 0) :
    rectZeros f z w = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hρ, hfρ⟩
  rw [Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hre] at hρ
  refine hborder ρ.re hρ.1 ρ ?_ hfρ
  refine Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨?_, ?_⟩)))
  · simp
  · simpa using hρ.2

/-- The argument principle and the layer-cake identity combined: the `σ`-integral of the
contour integrals of `f′/f` over the rectangles truncated at `re s = σ` is the sum of the
distances of the zeroes from the left edge, weighted by multiplicity.  (Littlewood's lemma
proper rewrites the inner contour integral as an integral of `log f` over the border; that
step is not proved here.)

WARNING: as stated, this theorem is vacuous — `rectZeros_eq_empty_of_forall_leftCorner_border`
shows that its hypothesis `hborder` forces `rectZeros f z w = ∅`, so both sides are zero.  It
is kept because earlier work refers to it; the usable form is
`integral_rectangleIntegral'_logDeriv_eq_finsum_of_border`, which assumes zero-freeness only
on the border of the rectangle itself. -/
theorem integral_rectangleIntegral'_logDeriv_eq_finsum (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ σ ∈ Icc z.re w.re, ∀ s ∈ RectangleBorder (leftCorner σ z) w, f s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re) := by
  have hbz : ∀ s ∈ RectangleBorder z w, f s ≠ 0 := by
    intro s hs
    refine hborder z.re ⟨le_refl _, hre⟩ s ?_
    rwa [leftCorner_self]
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hbz
  rw [← integral_rectZeroCount_eq_finsum hre hfin]
  refine intervalIntegral.integral_congr ?_
  intro σ hσ
  rw [Set.uIcc_of_le hre] at hσ
  have hre' : (leftCorner σ z).re ≤ w.re := by simpa using hσ.2
  have him' : (leftCorner σ z).im ≤ w.im := by simpa using him
  change (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re
      = ((rectZeroCount f (leftCorner σ z) w : ℕ) : ℝ)
  rw [rectangle_argument_principle hre' him'
    (hf.mono (rectangle_leftCorner_subset hre hσ)) (hborder σ hσ)]
  simp

/-- **Littlewood's identity, analytic form.**  For `f` analytic on a neighbourhood of the closed
rectangle and nonvanishing on its border, the `σ`-integral over `[z.re, w.re]` of the contour
integrals of `f′/f` around the rectangles truncated at `re s = σ` equals
`∑_ρ ord_ρ(f) · (re ρ − z.re)`, the sum being over the zeroes of `f` in the rectangle.

Unlike `integral_rectangleIntegral'_logDeriv_eq_finsum`, this version is not vacuous: the only
zero-freeness assumed is on the border of the rectangle itself.  The truncated border can meet
a zero, but only for the finitely many `σ` that are real parts of zeroes, a null set, so the
inner contour integral equals the truncated zero count almost everywhere. -/
theorem integral_rectangleIntegral'_logDeriv_eq_finsum_of_border (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re) := by
  have hfin : (rectZeros f z w).Finite := rectZeros_finite_of_border hf hborder
  rw [← integral_rectZeroCount_eq_finsum hre hfin]
  have hSfin : ((fun ρ : ℂ => ρ.re) '' rectZeros f z w).Finite := hfin.image _
  have hae : ∀ᵐ σ : ℝ, σ ∉ (fun ρ : ℂ => ρ.re) '' rectZeros f z w :=
    hSfin.countable.ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with σ hσS hσ
  rw [Set.uIoc_of_le hre] at hσ
  have hσ' : σ ∈ Icc z.re w.re := ⟨hσ.1.le, hσ.2⟩
  have hb : ∀ s ∈ RectangleBorder (leftCorner σ z) w, f s ≠ 0 := by
    intro s hs hfs
    rcases rectangleBorder_leftCorner_subset hre hσ' hs with hs' | hs'
    · exact hborder s hs' hfs
    · refine hσS ⟨s, ⟨?_, hfs⟩, hs'⟩
      exact rectangle_leftCorner_subset hre hσ' (rectangleBorder_subset_rectangle _ _ hs)
  have hre' : (leftCorner σ z).re ≤ w.re := by simpa using hσ.2
  have him' : (leftCorner σ z).im ≤ w.im := by simpa using him
  change (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re
      = ((rectZeroCount f (leftCorner σ z) w : ℕ) : ℝ)
  rw [rectangle_argument_principle hre' him'
    (hf.mono (rectangle_leftCorner_subset hre hσ')) hb]
  simp

end RiemannHypothesis
