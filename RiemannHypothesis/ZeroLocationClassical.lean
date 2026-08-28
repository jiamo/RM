/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroFreeClassical
import RiemannHypothesis.ZeroLocation

/-!
# The zeroes of `ζ` lie in a sub-strip of width `1 - 2c/log|Im s|`

`RiemannHypothesis.zeroFreeRegion` (in `RiemannHypothesis/ZeroFreeClassical.lean`) proves the
de la Vallée Poussin region `ζ(s) ≠ 0` for `Re s > 1 - c/log|Im s|`, `|Im s| ≥ 3`.  Reflecting
it in the critical line, exactly as `RiemannHypothesis/ZeroLocation.lean` does for the weaker
exponent-nine region, confines every zero with `|Im s| ≥ 3` to

`c/log|Im s| ≤ Re s ≤ 1 - c/log|Im s|`.

This is the same shape of statement as `RiemannHypothesis.zero_mem_shrinking_strip`, but with
the classical exponent one in the denominator instead of nine, so the sub-strip is much
narrower at every height.

## Main results

* `exists_zero_mem_shrinking_strip_classical` — the two-sided bound, with an absolute `c > 0`.
* `exists_zero_abs_re_sub_half_le_classical` — the same, as a bound on the distance of a zero
  from the critical line.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- A zero of `ζ` with `|Im s| ≥ 3` lies to the left of `Re s = 1 - c/log|Im s|`, the
contrapositive of the de la Vallée Poussin region. -/
theorem exists_zero_re_le_one_sub_classical :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
      s.re ≤ 1 - c / Real.log |s.im| := by
  obtain ⟨c, hc, h⟩ := zeroFreeRegion
  refine ⟨c, hc, fun s hz ht => ?_⟩
  by_contra hlt
  exact h s ht (lt_of_not_ge hlt) hz

/-- **Every zero of `ζ` with `|Im s| ≥ 3` lies in the strip
`c/log|Im s| ≤ Re s ≤ 1 - c/log|Im s|`**, of width `1 - 2c/log|Im s|`.  The lower bound is the
reflection of the upper one in the critical line. -/
theorem exists_zero_mem_shrinking_strip_classical :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
      c / Real.log |s.im| ≤ s.re ∧ s.re ≤ 1 - c / Real.log |s.im| := by
  obtain ⟨c, hc, hup⟩ := exists_zero_re_le_one_sub_classical
  refine ⟨c, hc, fun s hz ht => ⟨?_, hup s hz ht⟩⟩
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
  have hz' : riemannZeta (1 - s) = 0 := riemannZeta_one_sub_eq_zero_of_mem_strip hs0 hs1 hz
  have hIm : |(1 - s).im| = |s.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h := hup (1 - s) hz' (by rw [hIm]; exact ht)
  rw [hIm, Complex.sub_re, Complex.one_re] at h
  linarith

/-- The distance of a zero of `ζ` with `|Im s| ≥ 3` from the critical line is at most
`1/2 - c/log|Im s|`. -/
theorem exists_zero_abs_re_sub_half_le_classical :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
      |s.re - 1 / 2| ≤ 1 / 2 - c / Real.log |s.im| := by
  obtain ⟨c, hc, h⟩ := exists_zero_mem_shrinking_strip_classical
  refine ⟨c, hc, fun s hz ht => ?_⟩
  obtain ⟨hlo, hhi⟩ := h s hz ht
  rw [abs_le]
  constructor <;> linarith

end RiemannHypothesis

end
