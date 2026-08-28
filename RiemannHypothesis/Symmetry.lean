/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeros
import RiemannHypothesis.Partial

/-!
# Symmetries of the zeroes, and further equivalent formulations

This file proves the classical symmetries of the zero set of `ζ` inside the critical strip
and uses them to add three further equivalent formulations of the Riemann hypothesis to the
three of `RiemannHypothesis.Main`.

## The symmetries

* `dirichletEta_conj`, `riemannZeta_conj_of_re_pos`: `η(conj s) = conj (η s)` for `0 < re s`,
  and the same for `ζ` on the punctured right half-plane.  For `η` this is immediate from the
  paired series, whose terms are `n ^ (-s)` with `n` a positive integer; for `ζ` it follows
  through the identity `η(s) = (1 - 2^(1-s)) ζ(s)`.  Consequently the zeroes of `ζ` in the
  strip are symmetric about the real axis.

* `riemannZeta_one_sub_eq_zero_of_mem_strip`: the zeroes of `ζ` in the strip are symmetric
  about the critical line, by the functional equation.

* `dirichletEta_ofReal_ne_zero`, `riemannZeta_ofReal_ne_zero_of_lt_one`: `η(x) > 0` for real
  `x > 0` (every paired term `(2j+1)^{-x} - (2j+2)^{-x}` is positive), hence `ζ` has no real
  zero in `(0, 1)`.

## The new formulations

* `ZetaUpperStripForm` — only the zeroes of positive imaginary part are constrained.
* `ZetaRightStripForm` — `ζ` has no zero in the right half `1/2 < re s < 1` of the strip.
* `ZetaNonvanishingRightForm` — `ζ` has no zero at all with `re s > 1/2` (other than at the
  pole `s = 1`, where `ζ` is not zero anyway but which is excluded for safety).

with `zeta_strip_iff_upper_strip`, `zeta_strip_iff_right_strip`,
`zeta_strip_iff_nonvanishing_right`, and

* `zeta_strip_iff_forall_verifiedUpToHeight` — the Riemann hypothesis is equivalent to the
  statement that the numerical verification `VerifiedUpToHeight H` (of
  `RiemannHypothesis.Partial`) succeeds at every height `H`.
-/

noncomputable section

open Complex Filter
open scoped Real

namespace RiemannHypothesis

/-! ## Conjugation symmetry -/

/-- For a natural number `n`, the function `s ↦ n ^ (-s)` commutes with conjugation. -/
lemma natCast_cpow_neg_conj (n : ℕ) (s : ℂ) :
    ((n : ℂ)) ^ (-(starRingEnd ℂ) s) = (starRingEnd ℂ) ((n : ℂ) ^ (-s)) := by
  have harg : ((n : ℂ)).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    exact absurd h.1 (by simp)
  have := Complex.cpow_conj ((n : ℂ)) (-s) harg
  simpa [Complex.conj_natCast, map_neg] using this

/-- The paired terms of the eta series commute with conjugation. -/
lemma pairedTerm_conj (j : ℕ) (s : ℂ) :
    pairedTerm j ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pairedTerm j s) := by
  rw [pairedTerm, pairedTerm, map_sub, natCast_cpow_neg_conj, natCast_cpow_neg_conj]

/-- The Dirichlet eta function commutes with conjugation on the right half-plane. -/
lemma dirichletEta_conj {s : ℂ} (hs : 0 < s.re) :
    dirichletEta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dirichletEta s) := by
  have hsum : Summable (fun j : ℕ => pairedTerm j s) := summable_pairedTerm hs
  have hmap : HasSum (fun j : ℕ => (starRingEnd ℂ) (pairedTerm j s))
      ((starRingEnd ℂ) (dirichletEta s)) :=
    hsum.hasSum.map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj
  have heq : dirichletEta ((starRingEnd ℂ) s)
      = ∑' j : ℕ, (starRingEnd ℂ) (pairedTerm j s) := by
    simp only [dirichletEta, pairedTerm_conj]
  rw [heq, hmap.tsum_eq]

/-- Conjugation commutes with `w ↦ 2 ^ w`. -/
lemma two_cpow_conj (w : ℂ) :
    (2 : ℂ) ^ ((starRingEnd ℂ) w) = (starRingEnd ℂ) ((2 : ℂ) ^ w) := by
  have harg : ((2 : ℂ)).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    exact absurd h.1 (by norm_num)
  have := Complex.cpow_conj ((2 : ℂ)) w harg
  simpa [map_ofNat] using this

/-- The Riemann zeta function commutes with conjugation inside the critical strip. -/
lemma riemannZeta_conj_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hcre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  have hcne1 : (starRingEnd ℂ) s ≠ 1 := by
    intro h
    have : ((starRingEnd ℂ) s).re = 1 := by rw [h]; norm_num
    rw [hcre] at this
    linarith
  have h1 := dirichletEta_eq_mul_riemannZeta hs0 hne1
  have h2 := dirichletEta_eq_mul_riemannZeta (by rw [hcre]; exact hs0) hcne1
  have hfac : (1 : ℂ) - 2 ^ (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (1 - 2 ^ (1 - s)) := by
    rw [map_sub, map_one, ← two_cpow_conj]
    congr 2
    rw [map_sub, map_one]
  have hfacne : (1 - 2 ^ (1 - s) : ℂ) ≠ 0 := one_sub_two_cpow_ne_zero hs1
  have hconj_eta : dirichletEta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dirichletEta s) :=
    dirichletEta_conj hs0
  rw [h2, hfac] at hconj_eta
  rw [h1, map_mul] at hconj_eta
  have hfacne' : (starRingEnd ℂ) (1 - 2 ^ (1 - s)) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    exact hfacne
  exact mul_left_cancel₀ hfacne' hconj_eta

/-! ## Reflection in the critical line -/

/-- The zeroes of `ζ` inside the critical strip are symmetric about the critical line: if
`ζ(s) = 0` with `0 < re s < 1`, then `ζ(1 - s) = 0`. -/
lemma riemannZeta_one_sub_eq_zero_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hne : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hre : s.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hs0, hre]
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  rw [riemannZeta_one_sub hne hne1, hz, mul_zero]

/-! ## No real zeroes in the strip -/

/-- For real `x > 0` the value `η(x)` is a positive real number; in particular `η(x) ≠ 0`. -/
lemma dirichletEta_ofReal_ne_zero {x : ℝ} (hx : 0 < x) : dirichletEta (x : ℂ) ≠ 0 := by
  have hxre : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx
  have hsum : Summable (fun j : ℕ => pairedTerm j (x : ℂ)) := summable_pairedTerm hxre
  -- each paired term is a positive real number
  have hterm : ∀ j : ℕ, (pairedTerm j (x : ℂ)).re
      = (2 * j + 1 : ℝ) ^ (-x) - (2 * j + 2 : ℝ) ^ (-x) := by
    intro j
    have h1 : (((2 * j + 1 : ℕ) : ℂ)) ^ (-(x : ℂ))
        = (((2 * j + 1 : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      norm_num
    have h2 : (((2 * j + 2 : ℕ) : ℂ)) ^ (-(x : ℂ))
        = (((2 * j + 2 : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      norm_num
    rw [pairedTerm, h1, h2]
    simp
  have hpos : ∀ j : ℕ, 0 < (pairedTerm j (x : ℂ)).re := by
    intro j
    rw [hterm j]
    have : (2 * j + 2 : ℝ) ^ (-x) < (2 * j + 1 : ℝ) ^ (-x) := by
      apply Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
    linarith
  have hre : HasSum (fun j : ℕ => (pairedTerm j (x : ℂ)).re) (dirichletEta (x : ℂ)).re := by
    simpa [dirichletEta] using Complex.hasSum_re hsum.hasSum
  have hsumre : Summable (fun j : ℕ => (pairedTerm j (x : ℂ)).re) := hre.summable
  have hpos' : 0 < ∑' j : ℕ, (pairedTerm j (x : ℂ)).re :=
    hsumre.tsum_pos (fun i => (hpos i).le) 0 (hpos 0)
  rw [hre.tsum_eq] at hpos'
  intro h
  rw [h] at hpos'
  simp at hpos'

/-- `ζ` has no zero on the real interval `(0, 1)`. -/
lemma riemannZeta_ofReal_ne_zero_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro hz
  have hxre : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx0
  have hne1 : (x : ℂ) ≠ 1 := by
    intro h
    have : (x : ℝ) = 1 := by exact_mod_cast h
    linarith
  have := dirichletEta_eq_mul_riemannZeta hxre hne1
  rw [hz, mul_zero] at this
  exact dirichletEta_ofReal_ne_zero hx0 this

/-! ## Further equivalent formulations -/

/-- The Riemann hypothesis for the zeroes of positive imaginary part.  Since the zeroes are
symmetric about the real axis, and there are no real zeroes in the strip, this is equivalent
to the full strip form. -/
def ZetaUpperStripForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im → riemannZeta s = 0 → s.re = 1 / 2

/-- The Riemann hypothesis as the nonvanishing of `ζ` on the right half of the critical
strip. -/
def ZetaRightStripForm : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- The Riemann hypothesis as the nonvanishing of `ζ` on the half-plane `re s > 1/2`. -/
def ZetaNonvanishingRightForm : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- The Riemann hypothesis as the statement that every zero in the strip is fixed by the
reflection `s ↦ 1 - conj s` in the critical line. -/
def ZetaSelfReflectiveForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s = 1 - (starRingEnd ℂ) s

/-- **The strip form is equivalent to the upper-strip form**: only the zeroes with positive
imaginary part need to be constrained. -/
theorem zeta_strip_iff_upper_strip : ZetaStripForm ↔ ZetaUpperStripForm := by
  constructor
  · intro h s hs0 hs1 _ hz
    exact h s hs0 hs1 hz
  · intro h s hs0 hs1 hz
    rcases lt_trichotomy s.im 0 with him | him | him
    · -- reflect in the real axis
      have hcre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
      have hcim : ((starRingEnd ℂ) s).im = -s.im := Complex.conj_im s
      have hcz : riemannZeta ((starRingEnd ℂ) s) = 0 := by
        rw [riemannZeta_conj_of_mem_strip hs0 hs1, hz, map_zero]
      have := h ((starRingEnd ℂ) s) (by rw [hcre]; exact hs0) (by rw [hcre]; exact hs1)
        (by rw [hcim]; linarith) hcz
      rwa [hcre] at this
    · -- a real zero in the strip is impossible
      exfalso
      have hs_eq : s = ((s.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [hs_eq] at hz
      exact riemannZeta_ofReal_ne_zero_of_lt_one hs0 hs1 hz
    · exact h s hs0 hs1 him hz

/-- **The strip form is equivalent to the nonvanishing of `ζ` on the right half of the
strip**, by the reflection `s ↦ 1 - s`. -/
theorem zeta_strip_iff_right_strip : ZetaStripForm ↔ ZetaRightStripForm := by
  constructor
  · intro h s hs0 hs1 hz
    have := h s (by linarith) hs1 hz
    linarith
  · intro h s hs0 hs1 hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- reflect in the critical line
      have hz' : riemannZeta (1 - s) = 0 :=
        riemannZeta_one_sub_eq_zero_of_mem_strip hs0 hs1 hz
      have hre : (1 - s).re = 1 - s.re := by simp
      exact h (1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith) hz'
    · exact h s hgt hs1 hz

/-- **The strip form is equivalent to the nonvanishing of `ζ` on the half-plane
`re s > 1/2`.** -/
theorem zeta_strip_iff_nonvanishing_right : ZetaStripForm ↔ ZetaNonvanishingRightForm := by
  constructor
  · intro h s hs0 _ hz
    rcases lt_or_ge s.re 1 with hlt | hge
    · exact zeta_strip_iff_right_strip.mp h s hs0 hlt hz
    · exact riemannZeta_ne_zero_of_one_le_re hge hz
  · intro h
    refine zeta_strip_iff_right_strip.mpr (fun s hs0 hs1 hz => ?_)
    refine h s hs0 ?_ hz
    intro hone
    rw [hone] at hs1
    norm_num at hs1

/-- **The strip form is equivalent to the self-reflectivity of the zeroes**: a point `s` has
real part `1/2` exactly when `s = 1 - conj s`. -/
theorem zeta_strip_iff_self_reflective : ZetaStripForm ↔ ZetaSelfReflectiveForm := by
  have key : ∀ s : ℂ, s.re = 1 / 2 ↔ s = 1 - (starRingEnd ℂ) s := by
    intro s
    constructor
    · intro h
      apply Complex.ext <;> simp [h]
      linarith [h]
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  constructor
  · intro h s hs0 hs1 hz
    exact (key s).mp (h s hs0 hs1 hz)
  · intro h s hs0 hs1 hz
    exact (key s).mpr (h s hs0 hs1 hz)

/-- **The Riemann hypothesis is exactly the statement that the numerical verification
succeeds at every height.** -/
theorem zeta_strip_iff_forall_verifiedUpToHeight :
    ZetaStripForm ↔ ∀ H : ℝ, VerifiedUpToHeight H := by
  constructor
  · intro h H s hz him _
    have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
      rintro ⟨n, hn⟩
      have : s.im = 0 := by rw [hn]; norm_num
      linarith
    obtain ⟨hs0, hs1⟩ := zero_of_nontrivial_mem_strip hz htriv
    exact h s hs0 hs1 hz
  · intro h
    refine zeta_strip_iff_upper_strip.mpr (fun s hs0 hs1 him hz => ?_)
    exact h (s.im + 1) s hz him (by linarith)

end RiemannHypothesis

end
