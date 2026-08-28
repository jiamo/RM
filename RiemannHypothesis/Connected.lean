/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Convex

/-!
# Connectivity of the punctured right half-plane

The analytic identity `η(s) = (1 - 2^(1-s)) ζ(s)` is proved by the identity theorem for
analytic functions.  The natural domain of that identity is the right half-plane with the
point `s = 1` removed: `s = 1` is excluded because `ζ` has its pole there, and the identity
itself fails there (`η(1) = log 2 ≠ 0`).  The identity theorem needs the domain to be
*preconnected*, so this file proves:

* `isPreconnected_punctured_halfPlane` : `{s : ℂ | 0 < re s} \ {1}` is preconnected.

The proof uses the elementary criterion `isPreconnected_of_forall_pair`: every point of the
domain is joined to the fixed point `2` by a preconnected subset of the domain.  For a point
off the real axis the straight segment to `2` already avoids `1`.  For a real point `0 < x`,
`x ≠ 1`, the segment to `2` would pass through `1` when `0 < x < 1`, so we detour through
`x + i` first; the two segments then stay in the domain, whatever the value of `x`.  Two such
subsets (for two points `x, y`) share the point `2`, so their union is preconnected.
-/

noncomputable section

open Set Complex

namespace RiemannHypothesis

/-- A point of the segment `[x -[ℝ] y]`, unpacked as an affine combination
`z = a • x + b • y` with `0 ≤ a`, `0 ≤ b`, `a + b = 1`. -/
lemma mem_segment_real_comb {x y z : ℂ} (hz : z ∈ segment ℝ x y) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ z = a • x + b • y := by
  rcases hz with ⟨a, b, ha, hb, hab, hzdef⟩
  exact ⟨a, b, ha, hb, hab, hzdef.symm⟩

/-- A preconnected subset of `{s | 0 < re s} \ {1}` containing both `x` and `2`, for any
`x` in the punctured right half-plane.  If `x` is off the real axis, the straight segment
`[x, 2]` avoids `1`; if `x` is real we detour through `x + i`. -/
def joinedToTwo (x : ℂ) : Set ℂ :=
  if x.im = 0 then segment ℝ x (x + I) ∪ segment ℝ (x + I) (2 : ℂ) else segment ℝ x 2

lemma mem_joinedToTwo_left (x : ℂ) : x ∈ joinedToTwo x := by
  by_cases h : x.im = 0 <;> simp [joinedToTwo, h, left_mem_segment]

lemma mem_joinedToTwo_two (x : ℂ) : (2 : ℂ) ∈ joinedToTwo x := by
  by_cases h : x.im = 0 <;> simp [joinedToTwo, h, right_mem_segment]

lemma isPreconnected_joinedToTwo (x : ℂ) : IsPreconnected (joinedToTwo x) := by
  by_cases h : x.im = 0
  · rw [joinedToTwo, if_pos h]
    exact IsPreconnected.union (x + I) (right_mem_segment ℝ x (x + I))
      (left_mem_segment ℝ (x + I) 2) (convex_segment (𝕜 := ℝ) x (x + I)).isPreconnected
      (convex_segment (𝕜 := ℝ) (x + I) 2).isPreconnected
  · rw [joinedToTwo, if_neg h]
    exact (convex_segment (𝕜 := ℝ) x 2).isPreconnected

/-- For `x` real (and not equal to `1`), every point of the segment `[x -[ℝ] (x + I)]` lies
in the punctured right half-plane. -/
lemma segment_x_x_add_I_subset {x : ℂ} (hx : 0 < x.re) (hx1 : x ≠ 1) (him : x.im = 0) :
    segment ℝ x (x + I) ⊆ {s : ℂ | 0 < s.re} \ {1} := by
  intro z hz
  rcases mem_segment_real_comb hz with ⟨a, b, ha, hb, hab, hzdef⟩
  have hzr : 0 < z.re := by
    rw [hzdef]
    simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul]
    ring_nf
    calc
      a * x.re + x.re * b = (a + b) * x.re := by ring
      _ = x.re := by rw [hab]; ring
      _ > 0 := hx
  have hzne : z ≠ 1 := by
    intro hz1
    have hz1i : z.im = 0 := by rw [hz1]; simp
    have hb0 : b = 0 := by
      have : z.im = b := by
        rw [hzdef]
        simp only [Complex.add_im, Complex.smul_im, Complex.I_im, him, smul_eq_mul,
          mul_one, mul_zero, zero_add]
      rw [← this]
      exact hz1i
    have ha1 : a = 1 := by nlinarith [hab, hb0]
    have hzx : z = x := by
      rw [hzdef]
      simp [hb0, ha1]
    exact hx1 (by simpa [hzx] using hz1)
  exact ⟨hzr, hzne⟩

/-- For `x` real (and not equal to `1`), every point of the segment `[(x + I) -[ℝ] 2]` lies
in the punctured right half-plane. -/
lemma segment_x_add_I_two_subset {x : ℂ} (hx : 0 < x.re) (him : x.im = 0) :
    segment ℝ (x + I) (2 : ℂ) ⊆ {s : ℂ | 0 < s.re} \ {1} := by
  intro z hz
  rcases mem_segment_real_comb hz with ⟨a, b, ha, hb, hab, hzdef⟩
  have hzr : 0 < z.re := by
    rw [hzdef]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by nlinarith [hab, ha0]
      simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul,
        ha0, hb1]
      norm_num
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul]
      norm_num
      nlinarith [mul_pos hapos hx, mul_nonneg hb (by norm_num : (0 : ℝ) ≤ 2)]
  have hzne : z ≠ 1 := by
    intro hz1
    have hz1i : z.im = 0 := by rw [hz1]; simp
    have ha0 : a = 0 := by
      have : z.im = a := by
        rw [hzdef]
        simp only [Complex.add_im, Complex.smul_im, Complex.I_im, him,
          smul_eq_mul, mul_one, zero_add]
        norm_num
      rw [← this]
      exact hz1i
    have hb1 : b = 1 := by nlinarith [hab, ha0]
    have hz2 : z = 2 := by
      rw [hzdef]
      simp [ha0, hb1]
    rw [hz2] at hz1
    norm_num at hz1
  exact ⟨hzr, hzne⟩

/-- For `x` off the real axis, every point of the segment `[x -[ℝ] 2]` lies in the punctured
right half-plane. -/
lemma segment_x_two_subset {x : ℂ} (hx : 0 < x.re) (him : x.im ≠ 0) :
    segment ℝ x (2 : ℂ) ⊆ {s : ℂ | 0 < s.re} \ {1} := by
  intro z hz
  rcases mem_segment_real_comb hz with ⟨a, b, ha, hb, hab, hzdef⟩
  have hzr : 0 < z.re := by
    rw [hzdef]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by nlinarith [hab, ha0]
      simp only [ha0, hb1]
      norm_num
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      norm_num
      nlinarith [mul_pos hapos hx, mul_nonneg hb (by norm_num : (0 : ℝ) ≤ 2)]
  have hzne : z ≠ 1 := by
    intro hz1
    have hz1i : z.im = 0 := by rw [hz1]; simp
    have ha0 : a = 0 := by
      have : z.im = a • x.im := by
        rw [hzdef]
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        norm_num
      have haxim : a • x.im = 0 := by rwa [this] at hz1i
      have : a * x.im = 0 := by simpa [smul_eq_mul] using haxim
      exact (mul_eq_zero.mp this).resolve_right him
    have hb1 : b = 1 := by nlinarith [hab, ha0]
    have hz2 : z = 2 := by
      rw [hzdef]
      simp [ha0, hb1]
    rw [hz2] at hz1
    norm_num at hz1
  exact ⟨hzr, hzne⟩

/-- The set `joinedToTwo x` is contained in the punctured right half-plane, for `x` itself
in the punctured right half-plane. -/
lemma joinedToTwo_subset_punctured_halfPlane {x : ℂ} (hx : 0 < x.re) (hx1 : x ≠ 1) :
    joinedToTwo x ⊆ {s : ℂ | 0 < s.re} \ {1} := by
  by_cases him : x.im = 0
  · rw [joinedToTwo, if_pos him]
    exact union_subset (segment_x_x_add_I_subset hx hx1 him) (segment_x_add_I_two_subset hx him)
  · rw [joinedToTwo, if_neg him]
    exact segment_x_two_subset hx him

/-- The punctured right half-plane `{s | 0 < re s} \ {1}` is preconnected. -/
lemma isPreconnected_punctured_halfPlane :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  refine ⟨joinedToTwo x ∪ joinedToTwo y, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · exact joinedToTwo_subset_punctured_halfPlane hx.1 hx.2 hz
    · exact joinedToTwo_subset_punctured_halfPlane hy.1 hy.2 hz
  · exact Or.inl (mem_joinedToTwo_left x)
  · exact Or.inr (mem_joinedToTwo_left y)
  · exact IsPreconnected.union (2 : ℂ) (mem_joinedToTwo_two x) (mem_joinedToTwo_two y)
      (isPreconnected_joinedToTwo x) (isPreconnected_joinedToTwo y)

end RiemannHypothesis

end
