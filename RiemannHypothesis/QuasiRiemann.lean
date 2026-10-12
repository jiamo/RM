/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization

The proof of the main theorem is the native absorption of openai/math, family 003
(github.com/openai/math, revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache 2.0; see
NOTICE and LICENSES/openai-math-LICENSE), ported under `RiemannHypothesis/Family003/`.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Nonvanishing

/-!
# The quasi-Riemann hypothesis for `ζ`: no zeroes with `re s > 7/8`

* `riemannZeta_ne_zero_of_seven_eighths_lt_re` — Mathlib's `riemannZeta` does not vanish on the
  open half-plane `7/8 < re s`.  This is upstream `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`
  (openai/math `fd4aeeb`, module `OAI.NumberTheory.DirichletL.Nonvanishing`), whose proof is
  compiled here, against this repository's Lean and Mathlib pins, as
  `RiemannHypothesis.Family003.riemannZeta_ne_zero_of_seven_eighths_lt_re`.
* `nontrivial_zero_re_mem` — consequently every zero of `ζ` other than the trivial zeroes
  `-2(n+1)` has real part in `[1/8, 7/8]` (by the functional equation).

## The value at `s = 1`

The statement has no pole exception, and none is needed.  Mathlib's `riemannZeta` is a total
function `ℂ → ℂ`; at the pole it is *defined* by a junk value, and Mathlib proves
`riemannZeta_one : riemannZeta 1 = (γ - log (4π)) / 2`, which is non-zero
(`riemannZeta_ne_zero_of_one_le_re` covers `s = 1`).  The upstream theorem is stated about the
same constant `_root_.riemannZeta`, and the proof compiled here is the upstream proof, so the
theorem below *is* the upstream statement, checked on the host convention; there is no
discrepancy to record.  (The completed zeta function `completedRiemannZeta` is not used.)

## What this is not

This is a zero-free half-plane, not the Riemann hypothesis.  Nothing here says that any zero
lies on the critical line `re s = 1/2`; the corollary only confines the nontrivial zeroes to the
strip `1/8 ≤ re s ≤ 7/8`.
-/

namespace RiemannHypothesis.QuasiRiemann

open Complex

/-- **The quasi-Riemann hypothesis for `ζ`.**  The Riemann zeta function has no zeroes in the
half-plane `7/8 < re s`. -/
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) : _root_.riemannZeta s ≠ 0 :=
  RiemannHypothesis.Family003.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- **Location of the nontrivial zeroes.**  Every zero of `ζ` that is not a trivial zero
`-2(n+1)` has real part in `[1/8, 7/8]`.  (The pole `s = 1` needs no exclusion: `ζ 1 ≠ 0` in
Mathlib's convention, and anyway `re 1 > 7/8`.)  The lower bound is the upper bound reflected by
the functional equation `riemannZeta_one_sub`. -/
theorem nontrivial_zero_re_mem {s : ℂ} (hz : _root_.riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) : (1 / 8 : ℝ) ≤ s.re ∧ s.re ≤ 7 / 8 := by
  refine ⟨?_, not_lt.mp fun h => riemannZeta_ne_zero_of_seven_eighths_lt_re h hz⟩
  by_contra hlt
  push Not at hlt
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
  have hre : (7 / 8 : ℝ) < (1 - s).re := by simp; linarith
  have hfe := riemannZeta_one_sub (s := 1 - s) (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    (by intro h; apply hs0; linear_combination -h)
  rw [sub_sub_cancel] at hfe
  rw [hfe] at hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hZ := riemannZeta_ne_zero_of_seven_eighths_lt_re hre
  have hc : cos (Real.pi * (1 - s) / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hs : s = -2 * k := by
      apply mul_left_cancel₀ hpi
      linear_combination -2 * hk
    have hsr : s.re = -2 * k := by rw [hs]; simp
    have hk0 : 0 ≤ k := by
      have : (-1 : ℝ) < k := by linarith
      have : (-1 : ℤ) < k := by exact_mod_cast this
      omega
    have hk1 : k ≠ 0 := by rintro rfl; apply hs0; simpa using hs
    apply htriv
    refine ⟨(k - 1).toNat, ?_⟩
    rw [hs]
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast this
    rw [h2]; ring
  simp [hG, hZ, hc] at hz

end RiemannHypothesis.QuasiRiemann
