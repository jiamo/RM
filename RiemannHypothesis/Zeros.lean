/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Eta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Zeros of `ζ` and `η`

This file proves the two facts about zeroes of the Riemann zeta function that the equivalence
of the formulations of the Riemann hypothesis needs.

## Main results

* `one_sub_two_cpow_ne_zero`: the factor `1 - 2^(1-s)` does not vanish in the critical strip
  `0 < re s < 1`.  Indeed `|2^(1-s)| = 2^(1 - re s)`, and this equals `1` only when
  `re s = 1`.  This is what makes the zeta-form and the eta-form of the Riemann hypothesis
  equivalent: the zeroes of `η` inside the strip are exactly the zeroes of `ζ` inside the
  strip.

* `riemannZeta_eq_zero_of_re_nonpos`: a zero of `ζ` with `re s ≤ 0` must be one of the
  *trivial* zeroes `s = -2(n+1)`, `n ∈ ℕ`.  This is a standard consequence of the
  functional equation: writing `s' = 1 - s` (so `re s' ≥ 1`), the functional equation gives
  `ζ(s) = 2 (2π)^(-s') Γ(s') cos (π s'/2) ζ(s')`, and all factors other than the cosine are
  nonzero, while `ζ(s') ≠ 0` by `riemannZeta_ne_zero_of_one_le_re`; hence
  `cos (π s'/2) = 0`, i.e. `s' = 2k+1` for some `k ∈ ℤ`, which with `re s ≤ 0` forces
  `s = -2(n+1)`.

  This is the fact that the *full* zeta-form of the Riemann hypothesis (as stated in
  `RiemannHypothesis.ZetaForm`, following Mathlib) is equivalent to the strip form
  `RiemannHypothesis.ZetaStripForm`: the trivial zeroes are exactly the zeroes of `ζ`
  outside the strip, together with `s = 1` where `ζ` has its pole.
-/

noncomputable section

open Complex Filter
open scoped Real

namespace RiemannHypothesis

/-- The factor `1 - 2^(1-s)` has no zeroes in the critical strip `0 < re s < 1`. -/
lemma one_sub_two_cpow_ne_zero {s : ℂ} (hs1 : s.re < 1) :
    (1 - 2 ^ (1 - s) : ℂ) ≠ 0 := by
  intro h
  have htwo : (2 : ℂ) ^ (1 - s) = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    change ‖(((2 : ℝ) : ℂ)) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - s)]
    simp
  have h1 : (2 : ℝ) ^ (1 - s.re) = 1 := by
    rw [← hnorm]
    rw [htwo]
    norm_num
  have hre : 1 - s.re = 0 := by
    have hlog : Real.log ((2 : ℝ) ^ (1 - s.re)) = Real.log 1 := by rw [h1]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_one] at hlog
    have h2 : Real.log (2 : ℝ) ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    exact (mul_eq_zero.mp hlog).resolve_right h2
  linarith [hs1, hre]

/-- A zero of `ζ` with `re s ≤ 0` is a trivial zero `s = -2(n+1)`. -/
lemma riemannZeta_eq_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (hz : riemannZeta s = 0) : ∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
  -- `s ≠ 0` (since `ζ(0) = -1/2`)
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    have : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    exact this hz
  -- `s' = 1 - s` has real part at least 1, and `ζ(s') ≠ 0`
  let s' : ℂ := 1 - s
  have hs're : 1 ≤ s'.re := by
    dsimp [s']
    simp
    linarith
  have hζ' : riemannZeta s' ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs're
  -- side conditions for the functional equation at `s'`
  have hfe_side1 : ∀ n : ℕ, s' ≠ -↑n := by
    intro n hn
    have hre : s'.re = -(n : ℝ) := by
      have := congrArg re hn
      norm_num at this
      simpa using this
    have hneg : -(n : ℝ) ≤ 0 := by
      exact neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n)
    have hle : s'.re ≤ 0 := by rw [hre]; exact hneg
    linarith [hs're, hle]
  have hfe_side2 : s' ≠ 1 := by
    intro h
    apply hs0
    dsimp [s'] at h
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by norm_num
  -- the functional equation
  have hfe := riemannZeta_one_sub (s := s') hfe_side1 hfe_side2
  have hfe' : riemannZeta s
      = 2 * (2 * π) ^ (-s') * Gamma s' * cos (π * s' / 2) * riemannZeta s' := by
    simpa [s'] using hfe
  -- all factors other than the cosine are nonzero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h2p : (2 * π : ℂ) ≠ 0 := by
    intro h
    have : (2 * π : ℂ).re = 0 := congrArg re h
    simp at this
  have hpow : (2 * π : ℂ) ^ (-s') ≠ 0 := by
    exact cpow_ne_zero_iff.mpr (Or.inl h2p)
  have hgam : Gamma s' ≠ 0 := Complex.Gamma_ne_zero hfe_side1
  have hcos0 : cos (π * s' / 2) = 0 := by
    by_contra hcne
    have hprod : 2 * (2 * π) ^ (-s') * Gamma s' * cos (π * s' / 2) * riemannZeta s' = 0 := by
      rw [← hfe']
      exact hz
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpow) hgam) hcne) hζ') hprod
  -- `cos(π s'/2) = 0` gives `s' = 2k+1` for some `k : ℤ`
  rcases Complex.cos_eq_zero_iff.mp hcos0 with ⟨k, hk⟩
  -- `s' = 2k+1`, so `s = -2k`
  have hs'k : s' = 2 * (k : ℂ) + 1 := by
    have hlin : π * s' / 2 = (2 * (k : ℂ) + 1) * π / 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    calc
      s' = (2 * (π * s' / 2)) / π := by
        field_simp [hπ]
      _ = (2 * ((2 * (k : ℂ) + 1) * π / 2)) / π := by rw [hlin]
      _ = 2 * (k : ℂ) + 1 := by
        field_simp [hπ]
  have hsk : s = (-2) * (k : ℂ) := by
    dsimp [s'] at hs'k
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - (2 * (k : ℂ) + 1) := by rw [hs'k]
      _ = (-2) * (k : ℂ) := by ring
  -- with `re s ≤ 0`, `k ≥ 1`, and `s = -2(n+1)` with `n = k-1`
  have hkge : 0 ≤ k := by
    have hre : s.re = -2 * (k : ℝ) := by
      have := congrArg re hsk
      norm_num at this
      simpa using this
    have : (-2) * (k : ℝ) ≤ 0 := by rw [← hre]; exact hs
    have : (0 : ℝ) ≤ k := by nlinarith
    exact_mod_cast this
  have hkne : k ≠ 0 := by
    intro hk0
    rw [hk0] at hsk
    norm_num at hsk
    exact hs0 hsk
  have hk1 : 1 ≤ k := by omega
  refine ⟨Int.toNat (k - 1), ?_⟩
  have htoNat : (Int.toNat (k - 1) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega : 0 ≤ k - 1)
  have hcast : ((Int.toNat (k - 1) + 1 : ℕ) : ℂ) = (k : ℂ) := by
    rw [Nat.cast_add, Nat.cast_one]
    rw [← Int.cast_natCast (Int.toNat (k - 1))]
    rw [htoNat]
    norm_num
  -- `s = -2k = -2(n+1)`
  rw [hsk]
  congr 1
  rw [← hcast]

/-- The two ways of writing the trivial zeroes (`-2 * (n+1)` as a natural cast, or
`-2 * ((n : ℂ) + 1)` with the addition inside `ℂ`) coincide. -/
lemma trivial_zero_iff {s : ℂ} :
    (∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ)) ↔ (∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rw [hn]
    norm_num [Nat.cast_add, Nat.cast_one]
  · rw [hn]
    norm_num [Nat.cast_add, Nat.cast_one]

/-- A nontrivial zero of `ζ` lies inside the critical strip.  (The excluded cases are the
trivial zeroes at the negative even integers and the pole at `s = 1`.) -/
lemma zero_of_nontrivial_mem_strip {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ)) : 0 < s.re ∧ s.re < 1 := by
  have hle : ¬s.re ≥ 1 := by
    intro hsge
    exact (riemannZeta_ne_zero_of_one_le_re hsge) hz
  have hle0 : ¬s.re ≤ 0 := by
    intro hsle0
    exact htriv (riemannZeta_eq_zero_of_re_nonpos hsle0 hz)
  constructor
  · linarith
  · linarith

end RiemannHypothesis

end
