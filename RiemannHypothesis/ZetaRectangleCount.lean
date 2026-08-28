/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.RectangleArgumentPrinciple
import RiemannHypothesis.ZeroInfinite
import RiemannHypothesis.ZeroMultiplicityBound

/-!
# Counting the nontrivial zeroes of `ζ` in a rectangle

`RiemannHypothesis.RectangleZeroCount` and `RiemannHypothesis.RectangleArgumentPrinciple` build
the rectangle machinery for an arbitrary function of a complex variable: the count with
multiplicity `rectZeroCount`, the argument principle, and the layer-cake identity.  This file
attaches that machinery to the object of the repository, `ζ` and its completion `ξ`.

* `rectZeros_xiFn_eq` — the zeroes of `ξ` in a rectangle are exactly the nontrivial zeroes of
  `ζ` that lie in it, so `rectZeroCount xiFn` counts nontrivial zeroes and nothing else.
* `rectZeros_xiFn_finite` — that set is finite, with no hypothesis on the rectangle: `ξ` is
  entire and not identically zero.  (The general lemma `rectZeros_finite` asks for a point of
  the rectangle where the function does not vanish, which a bare rectangle need not provide.)
* `rectZeroCount_riemannZeta_eq_xiFn` — inside the open critical strip `ζ` and `ξ` have the
  same zeroes with the same multiplicities, so the two counts agree.
* `zeta_rectangle_argument_principle` — for a rectangle contained in the open critical strip and
  carrying no zero of `ζ` on its border, `(1/2πi) ∮ ζ′/ζ` is the number of nontrivial zeroes of
  `ζ` inside it, counted with multiplicity.  This is the tool the counting rows of the task
  board need; it is stated for `ζ` itself rather than for a general analytic function, and the
  analyticity hypothesis is discharged here (the rectangle avoids the pole at `s = 1` because
  it lies in the strip).
* `integral_rectZeroCount_riemannZeta_eq_finsum`, and its contour-integral form
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border` — Littlewood's identity
  in counting form for `ζ`: integrating the number of zeroes to the right of `re s = σ` over
  `σ ∈ [σ₀, σ₁]` gives `∑_ρ m_ρ (re ρ − σ₀)`.  The contour-integral form assumes only that `ζ`
  does not vanish on the border of the rectangle itself.  (The earlier variant
  `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum`, which assumes zero-freeness on
  the border of every truncation, is vacuous — that hypothesis forces the rectangle to contain
  no zero — and is kept only with a warning.)

Nothing here is conditional: every statement is about `ζ` unconditionally, and the hypotheses
are geometric (the rectangle lies in the strip, `ζ` does not vanish on its border).
-/

open Complex Set MeasureTheory Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

variable {z w : ℂ}

/-! ## Rectangles inside the critical strip -/

lemma mem_rectangle_iff {s z w : ℂ} :
    s ∈ Rectangle z w ↔ s.re ∈ uIcc z.re w.re ∧ s.im ∈ uIcc z.im w.im := Iff.rfl

/-- A point of a rectangle whose left edge is to the right of `re s = 0` and whose right edge is
to the left of `re s = 1` lies in the open critical strip. -/
lemma mem_strip_of_mem_rectangle (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re)
    {s : ℂ} (hs : s ∈ Rectangle z w) : 0 < s.re ∧ s.re < 1 := by
  have h := (mem_rectangle_iff.mp hs).1
  rw [Set.uIcc_of_le hre] at h
  exact ⟨lt_of_lt_of_le hz0 h.1, lt_of_le_of_lt h.2 hw1⟩

/-- The imaginary parts of a rectangle are bounded by those of its corners. -/
lemma abs_im_le_of_mem_rectangle {s : ℂ} (hs : s ∈ Rectangle z w) :
    |s.im| ≤ max |z.im| |w.im| := by
  have h : s.im ∈ uIcc z.im w.im := (mem_rectangle_iff.mp hs).2
  rw [Set.uIcc, Set.mem_Icc] at h
  have hz : -max |z.im| |w.im| ≤ z.im :=
    le_trans (neg_le_neg (le_max_left |z.im| |w.im|)) (neg_abs_le z.im)
  have hw : -max |z.im| |w.im| ≤ w.im :=
    le_trans (neg_le_neg (le_max_right |z.im| |w.im|)) (neg_abs_le w.im)
  refine abs_le.mpr ⟨le_trans (le_min hz hw) h.1, le_trans h.2 (max_le ?_ ?_)⟩
  · exact le_trans (le_abs_self z.im) (le_max_left _ _)
  · exact le_trans (le_abs_self w.im) (le_max_right _ _)

/-! ## The zeroes of `ξ` in a rectangle -/

/-- The zeroes of `ξ` in a rectangle are exactly the nontrivial zeroes of `ζ` inside it. -/
theorem rectZeros_xiFn_eq (z w : ℂ) :
    rectZeros xiFn z w = Rectangle z w ∩ nontrivialZeroSet := by
  ext s
  simp only [mem_rectZeros_iff, Set.mem_inter_iff, xiFn_eq_zero_iff_mem_nontrivialZeroSet]

/-- The zeroes of `ξ` in a rectangle form a finite set.  No hypothesis is needed: `ξ` is entire
and `ξ(2) ≠ 0`, and every zero of `ξ` is a nontrivial zero of `ζ`, of which there are finitely
many below any height. -/
theorem rectZeros_xiFn_finite (z w : ℂ) : (rectZeros xiFn z w).Finite := by
  refine Set.Finite.subset (finite_nontrivialZeros (max |z.im| |w.im|)) ?_
  intro s hs
  obtain ⟨hrect, hs0⟩ := hs
  obtain ⟨hz, h0, h1⟩ := xiFn_eq_zero_iff_mem_nontrivialZeroSet.mp hs0
  exact ⟨hz, h0, h1, abs_im_le_of_mem_rectangle hrect⟩

/-! ## `ζ` and `ξ` count the same zeroes inside the strip -/

/-- Inside the open critical strip the zero sets of `ζ` and of `ξ` coincide. -/
theorem rectZeros_riemannZeta_eq_xiFn (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    rectZeros riemannZeta z w = rectZeros xiFn z w := by
  ext s
  simp only [mem_rectZeros_iff]
  refine and_congr_right fun hs => ?_
  obtain ⟨h0, h1⟩ := mem_strip_of_mem_rectangle hz0 hw1 hre hs
  rw [xiFn_eq_zero_iff_mem_nontrivialZeroSet]
  exact ⟨fun h => ⟨h, h0, h1⟩, fun h => h.1⟩

/-- Inside the open critical strip `ζ` and `ξ` vanish to the same order, so their zero counts in
a rectangle agree. -/
theorem rectZeroCount_riemannZeta_eq_xiFn (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    rectZeroCount riemannZeta z w = rectZeroCount xiFn z w := by
  rw [rectZeroCount, rectZeroCount, rectZeros_riemannZeta_eq_xiFn hz0 hw1 hre]
  refine finsum_mem_congr rfl fun s hs => ?_
  obtain ⟨h0, h1⟩ := mem_strip_of_mem_rectangle hz0 hw1 hre hs.1
  simp only [analyticOrderNatAt, analyticOrderAt_xiFn_eq h0 h1]

/-- The zeroes of `ζ` in a rectangle inside the open critical strip form a finite set. -/
theorem rectZeros_riemannZeta_finite (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    (rectZeros riemannZeta z w).Finite := by
  rw [rectZeros_riemannZeta_eq_xiFn hz0 hw1 hre]
  exact rectZeros_xiFn_finite z w

/-! ## The argument principle for `ζ` -/

/-- `ζ` is analytic on a neighbourhood of a rectangle lying in the open critical strip: such a
rectangle avoids the pole at `s = 1`. -/
theorem analyticOnNhd_riemannZeta_rectangle (hz0 : 0 < z.re) (hw1 : w.re < 1)
    (hre : z.re ≤ w.re) : AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
  intro s hs
  have h1 : s ≠ 1 := by
    intro h
    have := (mem_strip_of_mem_rectangle hz0 hw1 hre hs).2
    rw [h] at this
    simp at this
  exact DifferentiableOn.analyticAt (s := {u : ℂ | u ≠ 1})
    (fun u hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_ne.mem_nhds h1)

/-- **The argument principle for `ζ` on a rectangle inside the critical strip.**  If the closed
rectangle with corners `z` and `w` lies in the open strip `0 < re s < 1` and `ζ` has no zero on
its border, then `(1/2πi) ∮_{∂R} ζ′/ζ` is the number of zeroes of `ζ` inside, counted with
multiplicity — equivalently, the number of nontrivial zeroes of `ζ` in the rectangle. -/
theorem zeta_rectangle_argument_principle (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    RectangleIntegral' (logDeriv riemannZeta) z w = (rectZeroCount riemannZeta z w : ℂ) :=
  rectangle_argument_principle hre him (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) hborder

/-- The contour integral of `ζ′/ζ` around a rectangle inside the critical strip on which `ζ`
does not vanish is zero. -/
theorem zeta_rectangleIntegral'_logDeriv_eq_zero (hz0 : 0 < z.re) (hw1 : w.re < 1)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h : ∀ s ∈ Rectangle z w, riemannZeta s ≠ 0) :
    RectangleIntegral' (logDeriv riemannZeta) z w = 0 :=
  rectangleIntegral'_logDeriv_eq_zero_of_forall_ne_zero hre him
    (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) h

/-! ## Littlewood's identity in counting form, for `ζ` -/

/-- **Littlewood's counting identity for `ζ`.**  For a rectangle inside the open critical strip,
integrating over `σ ∈ [z.re, w.re]` the number of zeroes of `ζ` in the part of the rectangle to
the right of the line `re s = σ` gives `∑_ρ m_ρ (re ρ − z.re)`, the sum over the zeroes in the
rectangle of their multiplicity times their distance from the left edge. -/
theorem integral_rectZeroCount_riemannZeta_eq_finsum (hz0 : 0 < z.re) (hw1 : w.re < 1)
    (hre : z.re ≤ w.re) :
    (∫ σ in z.re..w.re, (rectZeroCount riemannZeta (leftCorner σ z) w : ℝ))
      = ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  integral_rectZeroCount_eq_finsum hre (rectZeros_riemannZeta_finite hz0 hw1 hre)

/-- **Littlewood's counting identity for `ζ`, in contour-integral form.**  Combining the
argument principle with the layer-cake identity: for a rectangle inside the open critical strip
whose truncations carry no zero of `ζ` on their borders, the `σ`-integral of the contour
integrals of `ζ′/ζ` is the sum of the distances of the zeroes from the left edge, weighted by
multiplicity.

WARNING: this hypothesis is vacuous — by `rectZeros_eq_empty_of_forall_leftCorner_border` it
forces `ζ` to have no zero in the rectangle at all, so both sides are zero.  The version with
content is `integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border` below. -/
theorem integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum (hz0 : 0 < z.re)
    (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ σ ∈ Icc z.re w.re, ∀ s ∈ RectangleBorder (leftCorner σ z) w,
      riemannZeta s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv riemannZeta) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  integral_rectangleIntegral'_logDeriv_eq_finsum hre him
    (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) hborder

/-- **Littlewood's identity for `ζ`, analytic form.**  For a rectangle inside the open critical
strip carrying no zero of `ζ` on its border, the `σ`-integral over `[z.re, w.re]` of the
contour integrals of `ζ′/ζ` around the truncated rectangles equals `∑_ρ m_ρ (re ρ − z.re)`,
the sum over the nontrivial zeroes of `ζ` in the rectangle of their multiplicity times their
distance from the left edge.

Only the border of the rectangle itself is assumed zero-free, so the statement has content:
the right-hand side is nonzero as soon as the rectangle contains a zero. -/
theorem integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border (hz0 : 0 < z.re)
    (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv riemannZeta) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  integral_rectangleIntegral'_logDeriv_eq_finsum_of_border hre him
    (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) hborder

end RiemannHypothesis
