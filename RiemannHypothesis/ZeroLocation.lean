/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroFreeRegion
import RiemannHypothesis.Symmetry

/-!
# The zeroes of `ζ` lie in a shrinking sub-strip

`RiemannHypothesis.ZeroFreeRegion` proves `ζ(s) ≠ 0` to the right of
`re s = 1 - 2^(-45)/(log|im s|)^9`.  Reflecting that region in the critical line, using the
symmetry `ζ(s) = 0 → ζ(1-s) = 0` of `RiemannHypothesis.Symmetry`, confines every zero with
`|im s| ≥ 4` to the closed strip

`2^(-45)/(log|im s|)^9 ≤ re s ≤ 1 - 2^(-45)/(log|im s|)^9`,

which is strictly narrower than the critical strip `0 < re s < 1` and shrinks to it as
`|im s| → ∞`.  Equivalently, the distance of a zero from the critical line is at most
`1/2 - 2^(-45)/(log|im s|)^9`.

This is the exact shape of statement that the classical Bohr–Landau and density arguments
sharpen; it is *not* the Riemann hypothesis, since the sub-strip still has width tending
to `1`.

## Main results

* `zero_re_le_one_sub` : a zero with `|im s| ≥ 4` has `re s ≤ 1 - 2^(-45)/(log|im s|)^9`.
* `zero_le_re` : a zero with `|im s| ≥ 4` has `2^(-45)/(log|im s|)^9 ≤ re s`.
* `zero_mem_shrinking_strip` : the two bounds together.
* `zero_abs_re_sub_half_le` : `|re s - 1/2| ≤ 1/2 - 2^(-45)/(log|im s|)^9`.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- A zero of `ζ` with `|im s| ≥ 4` lies to the left of `re s = 1 - 2^(-45)/(log|im s|)^9`.
This is the contrapositive of `riemannZeta_ne_zero_of_near_one`. -/
theorem zero_re_le_one_sub {s : ℂ} (hz : riemannZeta s = 0) (ht : 4 ≤ |s.im|) :
    s.re ≤ 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 := by
  by_contra hlt
  exact riemannZeta_ne_zero_of_near_one ht (lt_of_not_ge hlt) hz

/-- A zero of `ζ` with `|im s| ≥ 4` lies to the right of `re s = 2^(-45)/(log|im s|)^9`.
It is the reflection in the critical line of `zero_re_le_one_sub`. -/
theorem zero_le_re {s : ℂ} (hz : riemannZeta s = 0) (ht : 4 ≤ |s.im|) :
    (1 / 2 ^ 45) / Real.log |s.im| ^ 9 ≤ s.re := by
  -- a zero this high up is not one of the trivial (real) zeroes, so it lies in the strip
  have him : s.im ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
    rintro ⟨n, rfl⟩
    apply him
    simp
  obtain ⟨hs0, hs1⟩ := zero_of_nontrivial_mem_strip hz htriv
  -- reflect
  have hz' : riemannZeta (1 - s) = 0 := riemannZeta_one_sub_eq_zero_of_mem_strip hs0 hs1 hz
  have hIm : |(1 - s).im| = |s.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h := zero_re_le_one_sub hz' (by rw [hIm]; exact ht)
  rw [hIm, Complex.sub_re, Complex.one_re] at h
  linarith

/-- **Every zero of `ζ` with `|im s| ≥ 4` lies in a strip strictly inside the critical
strip**, of width `1 - 2^(-44)/(log|im s|)^9`. -/
theorem zero_mem_shrinking_strip {s : ℂ} (hz : riemannZeta s = 0) (ht : 4 ≤ |s.im|) :
    (1 / 2 ^ 45) / Real.log |s.im| ^ 9 ≤ s.re ∧
      s.re ≤ 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 :=
  ⟨zero_le_re hz ht, zero_re_le_one_sub hz ht⟩

/-- The distance of a zero of `ζ` with `|im s| ≥ 4` from the critical line is at most
`1/2 - 2^(-45)/(log|im s|)^9`, a quantity strictly smaller than `1/2`. -/
theorem zero_abs_re_sub_half_le {s : ℂ} (hz : riemannZeta s = 0) (ht : 4 ≤ |s.im|) :
    |s.re - 1 / 2| ≤ 1 / 2 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 := by
  obtain ⟨hlo, hhi⟩ := zero_mem_shrinking_strip hz ht
  rw [abs_le]
  constructor <;> linarith

/-- The sub-strip really is strictly narrower than the critical strip: the excluded margin
`2^(-45)/(log|im s|)^9` is positive whenever `|im s| ≥ 4`. -/
theorem zero_margin_pos {s : ℂ} (ht : 4 ≤ |s.im|) :
    0 < (1 / 2 ^ 45) / Real.log |s.im| ^ 9 := by
  have hL : 0 < Real.log |s.im| :=
    Real.log_pos (by linarith)
  positivity

end RiemannHypothesis

end
