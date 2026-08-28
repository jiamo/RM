/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Zeroes in a rectangle, and Littlewood's identity in counting form

This file is *infrastructure*, not a step of one particular route.  Several of the open rows of
the task board — Bohr–Landau (`M1-ALMOST-ALL-STRIP`), a density theorem (`M2-DENSITY`), and any
zero-counting argument for `ζ`, `ξ` or `ξ′` — need the same two tools: a count of the zeroes of
a function in a rectangle *with multiplicity*, and the identity that turns that count,
integrated across the rectangle, into a sum of distances of the zeroes from the left edge.
Neither is in mathlib.  Everything here is about an arbitrary function of a complex variable;
nothing about `ζ` is used.

* `rectZeros f z w` — the zeroes of `f` in the closed rectangle with corners `z` and `w`.
* `rectZeroCount f z w` — their number with multiplicity.  It is a `finsum`, so the definition
  carries no finiteness hypothesis; finiteness is assumed where it is needed.
* `rectZeros_finite` — that set is finite as soon as `f` is analytic on a neighbourhood of the
  rectangle and does not vanish identically on it.
* `rectZeroCount_mono` — the count is monotone in the rectangle.
* `rectZeros_leftCorner` — truncating the rectangle at the vertical line `re s = σ` keeps
  exactly the zeroes with `σ ≤ re ρ`; `rectZeroCount_leftCorner_antitone` is the resulting
  monotonicity of `σ ↦ N(σ)`, the counting function a density theorem bounds.
* `integral_rectZeroCount_eq_finsum` — **Littlewood's identity in counting form**: the integral
  over `σ ∈ [z.re, w.re]` of the number of zeroes in the truncated rectangle equals
  `∑_ρ ord_ρ(f)·(re ρ − z.re)`.  This is the layer-cake half of Littlewood's lemma; it is
  unconditional and needs no analyticity, only that the zero set is finite.

The analytic half — the argument principle, which identifies `rectZeroCount` with a contour
integral of `f′/f` — is in `RiemannHypothesis.RectangleArgumentPrinciple`.
-/

open Complex Set MeasureTheory

open scoped Interval

namespace RiemannHypothesis

variable {f : ℂ → ℂ} {z w : ℂ}

/-! ## The zeroes of a function inside a rectangle -/

/-- The zeroes of `f` in the closed rectangle with corners `z` and `w`. -/
def rectZeros (f : ℂ → ℂ) (z w : ℂ) : Set ℂ := {s ∈ Rectangle z w | f s = 0}

/-- The number of zeroes of `f` in the closed rectangle with corners `z` and `w`, counted with
multiplicity.  Written as a `finsum`, so that it is defined without a finiteness hypothesis. -/
noncomputable def rectZeroCount (f : ℂ → ℂ) (z w : ℂ) : ℕ :=
  ∑ᶠ ρ ∈ rectZeros f z w, analyticOrderNatAt f ρ

lemma mem_rectZeros_iff {s : ℂ} : s ∈ rectZeros f z w ↔ s ∈ Rectangle z w ∧ f s = 0 := Iff.rfl

lemma rectZeros_eq_inter : rectZeros f z w = Rectangle z w ∩ f ⁻¹' {0} := by
  ext s
  simp [rectZeros, Set.mem_preimage]

/-- A rectangle is compact. -/
lemma isCompact_rectangle (z w : ℂ) : IsCompact (Rectangle z w) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- A rectangle is convex. -/
lemma convex_rectangle (z w : ℂ) : Convex ℝ (Rectangle z w) := by
  rw [rectangle_eq_convexHull]
  exact convex_convexHull ℝ _

/-- The zero set of a function analytic on a neighbourhood of a rectangle, and nonvanishing at
one point of it, is finite.  (Without the nonvanishing point the statement is false: `f = 0`
has the whole rectangle as its zero set.) -/
theorem rectZeros_finite (hf : AnalyticOnNhd ℂ f (Rectangle z w)) {x : ℂ}
    (hx : x ∈ Rectangle z w) (hfx : f x ≠ 0) : (rectZeros f z w).Finite := by
  have hcomp : IsCompact (Rectangle z w) := isCompact_rectangle z w
  rw [rectZeros_eq_inter]
  refine IsCompact.finite ?_ ?_
  · exact hcomp.of_isClosed_subset
      (hf.continuousOn.preimage_isClosed_of_isClosed hcomp.isClosed isClosed_singleton)
      inter_subset_left
  · rw [inter_comm]
    exact isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hfx hx
        ⟨⟨x, hx⟩, (convex_rectangle z w).isPreconnected⟩)

lemma rectZeroCount_eq_sum {Z : Finset ℂ} (hZ : ∀ s, s ∈ rectZeros f z w ↔ s ∈ Z) :
    rectZeroCount f z w = ∑ ρ ∈ Z, analyticOrderNatAt f ρ := by
  have hset : rectZeros f z w = (Z : Set ℂ) := by
    ext s; simpa using hZ s
  rw [rectZeroCount, hset, finsum_mem_coe_finset]

/-- The count is monotone in the rectangle: a bigger rectangle has at least as many zeroes,
counted with multiplicity. -/
theorem rectZeroCount_mono {z' w' : ℂ} (hfin : (rectZeros f z' w').Finite)
    (hsub : Rectangle z w ⊆ Rectangle z' w') :
    rectZeroCount f z w ≤ rectZeroCount f z' w' := by
  classical
  have hZsub : rectZeros f z w ⊆ rectZeros f z' w' := fun s hs => ⟨hsub hs.1, hs.2⟩
  have hfin' : (rectZeros f z w).Finite := hfin.subset hZsub
  rw [rectZeroCount_eq_sum (Z := hfin'.toFinset) (fun s => by simp),
    rectZeroCount_eq_sum (Z := hfin.toFinset) (fun s => by simp)]
  refine Finset.sum_le_sum_of_subset ?_
  intro s hs
  simp only [Set.Finite.mem_toFinset] at hs ⊢
  exact hZsub hs

/-- A rectangle on which `f` does not vanish carries no zeroes. -/
theorem rectZeroCount_eq_zero_of_forall_ne_zero (h : ∀ s ∈ Rectangle z w, f s ≠ 0) :
    rectZeroCount f z w = 0 := by
  have hempty : rectZeros f z w = ∅ := by
    ext s
    simp only [mem_rectZeros_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hs => h s hs
  simp [rectZeroCount, hempty]

/-! ## Truncating the rectangle at a vertical line -/

/-- The lower-left corner of the rectangle with corners `z` and `w`, moved to the vertical line
`re s = σ`. -/
noncomputable def leftCorner (σ : ℝ) (z : ℂ) : ℂ := (σ : ℂ) + z.im * I

@[simp] lemma leftCorner_re (σ : ℝ) (z : ℂ) : (leftCorner σ z).re = σ := by
  simp [leftCorner]

@[simp] lemma leftCorner_im (σ : ℝ) (z : ℂ) : (leftCorner σ z).im = z.im := by
  simp [leftCorner]

lemma leftCorner_self (z : ℂ) : leftCorner z.re z = z := by
  apply Complex.ext <;> simp

/-- Truncating the rectangle at the vertical line `re s = σ` keeps exactly the zeroes with
`σ ≤ re ρ`. -/
theorem rectZeros_leftCorner (hre : z.re ≤ w.re) {σ : ℝ} (hσ : σ ∈ Icc z.re w.re) :
    rectZeros f (leftCorner σ z) w = {ρ ∈ rectZeros f z w | σ ≤ ρ.re} := by
  ext s
  simp only [mem_rectZeros_iff, Set.mem_setOf_eq, Rectangle, Complex.mem_reProdIm,
    leftCorner_re, leftCorner_im, Set.uIcc_of_le hre, Set.uIcc_of_le hσ.2]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hi⟩, hs⟩
    exact ⟨⟨⟨⟨le_trans hσ.1 h1, h2⟩, hi⟩, hs⟩, h1⟩
  · rintro ⟨⟨⟨⟨-, h2⟩, hi⟩, hs⟩, hσs⟩
    exact ⟨⟨⟨hσs, h2⟩, hi⟩, hs⟩

/-- The truncated rectangle is contained in the original one. -/
theorem rectangle_leftCorner_subset (hre : z.re ≤ w.re) {σ : ℝ} (hσ : σ ∈ Icc z.re w.re) :
    Rectangle (leftCorner σ z) w ⊆ Rectangle z w := by
  intro s hs
  simp only [Rectangle, Complex.mem_reProdIm, leftCorner_re, leftCorner_im,
    Set.uIcc_of_le hre, Set.uIcc_of_le hσ.2] at hs ⊢
  exact ⟨⟨le_trans hσ.1 hs.1.1, hs.1.2⟩, hs.2⟩

@[simp] lemma leftCorner_leftCorner (σ τ : ℝ) (z : ℂ) :
    leftCorner τ (leftCorner σ z) = leftCorner τ z := by
  apply Complex.ext <;> simp

/-- The zeroes of the truncated rectangle are zeroes of the whole one. -/
theorem rectZeros_leftCorner_subset (hre : z.re ≤ w.re) {σ : ℝ} (hσ : σ ∈ Icc z.re w.re) :
    rectZeros f (leftCorner σ z) w ⊆ rectZeros f z w :=
  fun _ hs => ⟨rectangle_leftCorner_subset hre hσ hs.1, hs.2⟩

/-- **The counting function of the truncated rectangle is antitone in the cut.**  Pushing the
left edge to the right can only lose zeroes.  This is the monotonicity of `N(σ, T)` that a
density theorem is a bound for. -/
theorem rectZeroCount_leftCorner_antitone (hre : z.re ≤ w.re)
    (hfin : (rectZeros f z w).Finite) {σ τ : ℝ} (hσ : σ ∈ Icc z.re w.re)
    (hτ : τ ∈ Icc z.re w.re) (hστ : σ ≤ τ) :
    rectZeroCount f (leftCorner τ z) w ≤ rectZeroCount f (leftCorner σ z) w := by
  have hfinσ : (rectZeros f (leftCorner σ z) w).Finite :=
    hfin.subset (rectZeros_leftCorner_subset hre hσ)
  have hre' : (leftCorner σ z).re ≤ w.re := by simpa using hσ.2
  have hτ' : τ ∈ Icc (leftCorner σ z).re w.re := by simpa using ⟨hστ, hτ.2⟩
  have hsub := rectangle_leftCorner_subset (z := leftCorner σ z) (w := w) hre' hτ'
  rw [leftCorner_leftCorner] at hsub
  exact rectZeroCount_mono hfinσ hsub

/-- Every truncation has at most as many zeroes as the whole rectangle. -/
theorem rectZeroCount_leftCorner_le (hre : z.re ≤ w.re) (hfin : (rectZeros f z w).Finite)
    {σ : ℝ} (hσ : σ ∈ Icc z.re w.re) :
    rectZeroCount f (leftCorner σ z) w ≤ rectZeroCount f z w :=
  rectZeroCount_mono hfin (rectangle_leftCorner_subset hre hσ)

/-! ## Littlewood's identity in counting form -/

private lemma intervalIntegrable_indicator (a b c k : ℝ) :
    IntervalIntegrable (Set.indicator {x : ℝ | x ≤ c} (fun _ => k)) volume a b := by
  constructor <;> exact (integrable_const k).indicator measurableSet_Iic

private lemma integral_indicator_step {a b c k : ℝ} (h : c ∈ Icc a b) :
    ∫ σ in a..b, Set.indicator {x : ℝ | x ≤ c} (fun _ => k) σ = k * (c - a) := by
  rw [intervalIntegral.integral_indicator h, intervalIntegral.integral_const, smul_eq_mul,
    mul_comm]

/-- **Littlewood's identity, counting form.**  Integrating over `σ ∈ [z.re, w.re]` the number of
zeroes of `f`, with multiplicity, in the truncated rectangle `[σ, w.re] × [z.im, w.im]` gives
`∑_ρ ord_ρ(f) · (re ρ − z.re)`.

This is the layer-cake identity behind Littlewood's lemma.  It is unconditional: no analyticity
is used, only that `f` has finitely many zeroes in the rectangle. -/
theorem integral_rectZeroCount_eq_finsum (hre : z.re ≤ w.re)
    (hfin : (rectZeros f z w).Finite) :
    (∫ σ in z.re..w.re, (rectZeroCount f (leftCorner σ z) w : ℝ))
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re) := by
  classical
  set Z := hfin.toFinset with hZdef
  have hmem : ∀ s, s ∈ rectZeros f z w ↔ s ∈ Z := by
    intro s; simp [hZdef]
  have hstep : ∀ σ ∈ uIcc z.re w.re,
      ((rectZeroCount f (leftCorner σ z) w : ℝ))
        = ∑ ρ ∈ Z, Set.indicator {x : ℝ | x ≤ ρ.re}
            (fun _ => (analyticOrderNatAt f ρ : ℝ)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hre] at hσ
    have hcount : rectZeroCount f (leftCorner σ z) w
        = ∑ ρ ∈ Z.filter (fun ρ => σ ≤ ρ.re), analyticOrderNatAt f ρ := by
      refine rectZeroCount_eq_sum ?_
      intro s
      rw [rectZeros_leftCorner hre hσ]
      simp [hmem s, Finset.mem_filter]
    rw [hcount, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro ρ _
    by_cases h : σ ≤ ρ.re <;> simp [h]
  rw [intervalIntegral.integral_congr hstep,
    intervalIntegral.integral_finset_sum
      (fun ρ _ => intervalIntegrable_indicator z.re w.re ρ.re _)]
  have hcalc : ∀ ρ ∈ Z,
      (∫ σ in z.re..w.re, Set.indicator {x : ℝ | x ≤ ρ.re}
          (fun _ => (analyticOrderNatAt f ρ : ℝ)) σ)
        = (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re) := by
    intro ρ hρ
    have hmemρ : ρ ∈ rectZeros f z w := (hmem ρ).mpr hρ
    have hrec : ρ.re ∈ uIcc z.re w.re := (Complex.mem_reProdIm.mp hmemρ.1).1
    rw [Set.uIcc_of_le hre] at hrec
    exact integral_indicator_step hrec
  rw [Finset.sum_congr rfl hcalc, ← finsum_mem_coe_finset]
  congr 1
  ext s
  simp [hmem s]

end RiemannHypothesis
