/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroCountLower
import RiemannHypothesis.Symmetry

/-!
# Conjugation symmetry of the nontrivial zeroes, and the parity of `N(T)`

`RiemannHypothesis.Symmetry` proves the two classical symmetries of `ζ` inside the critical
strip — conjugation `ζ(conj s) = conj (ζ s)` and reflection `ζ(s) = 0 → ζ(1 - s) = 0` — and the
absence of real zeroes in `(0, 1)`.  This file turns them into statements about the zero *set*
`nontrivialZeroSet = {s | ζ s = 0, 0 < re s < 1}` and about the counting function
`N(T) = #{ρ ∈ nontrivialZeroSet | |im ρ| ≤ T}` of `RiemannHypothesis.ZeroCount`:

* `im_ne_zero_of_mem_nontrivialZeroSet` : every nontrivial zero has nonzero imaginary part, so
  the zero set is the disjoint union of its upper and lower halves;
* `conj_mem_nontrivialZeroSet`, `one_sub_mem_nontrivialZeroSet` : the zero set is stable under
  `s ↦ conj s` and under `s ↦ 1 - s`;
* `conj_image_upperNontrivialZeroSet` : conjugation is a bijection from the upper half of the
  zero set onto the lower half;
* `infinite_upperNontrivialZeroSet`, `infinite_lowerNontrivialZeroSet` : each half is infinite
  (combining the bijection with `infinite_nontrivialZeroSet`);
* `ncard_nontrivialZeros_eq_two_mul` : `N(T) = 2 · #{ρ : ζ ρ = 0, 0 < re ρ < 1, 0 < im ρ ≤ T}`,
  and hence `even_ncard_nontrivialZeros` : `N(T)` is even.

As everywhere in this repository, zeroes are counted *without* multiplicity; with multiplicity
the parity statement would need the equality of the multiplicities at `ρ` and `conj ρ`, which is
not proved here.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- Complex conjugation is injective. -/
lemma conj_injective_complex : Function.Injective (starRingEnd ℂ) :=
  fun a b h => by simpa using congrArg (starRingEnd ℂ) h

/-! ## Stability of the zero set under the two symmetries -/

/-- A nontrivial zero of `ζ` is not real: `ζ` has no zero on the real interval `(0, 1)`. -/
theorem im_ne_zero_of_mem_nontrivialZeroSet {s : ℂ} (hs : s ∈ nontrivialZeroSet) : s.im ≠ 0 := by
  obtain ⟨hz, h0, h1⟩ := hs
  intro him
  have hs_eq : s = ((s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hs_eq] at hz
  exact riemannZeta_ofReal_ne_zero_of_lt_one h0 h1 hz

/-- The zero set is stable under complex conjugation. -/
theorem conj_mem_nontrivialZeroSet {s : ℂ} (hs : s ∈ nontrivialZeroSet) :
    (starRingEnd ℂ) s ∈ nontrivialZeroSet := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  rw [riemannZeta_conj_of_mem_strip h0 h1, hz, map_zero]

/-- The zero set is stable under reflection in the critical line, `s ↦ 1 - s`. -/
theorem one_sub_mem_nontrivialZeroSet {s : ℂ} (hs : s ∈ nontrivialZeroSet) :
    1 - s ∈ nontrivialZeroSet := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine ⟨riemannZeta_one_sub_eq_zero_of_mem_strip h0 h1 hz, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · simp only [Complex.sub_re, Complex.one_re]; linarith

/-! ## The two halves of the zero set -/

/-- The nontrivial zeroes in the upper half-plane. -/
def upperNontrivialZeroSet : Set ℂ := {s | s ∈ nontrivialZeroSet ∧ 0 < s.im}

/-- The nontrivial zeroes in the lower half-plane. -/
def lowerNontrivialZeroSet : Set ℂ := {s | s ∈ nontrivialZeroSet ∧ s.im < 0}

/-- Conjugation maps the upper half of the zero set bijectively onto the lower half. -/
theorem conj_image_upperNontrivialZeroSet :
    (starRingEnd ℂ) '' upperNontrivialZeroSet = lowerNontrivialZeroSet := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hspos⟩, rfl⟩
    exact ⟨conj_mem_nontrivialZeroSet hs, by simpa using hspos⟩
  · rintro ⟨ht, htneg⟩
    refine ⟨(starRingEnd ℂ) t, ⟨conj_mem_nontrivialZeroSet ht, by simpa using htneg⟩, ?_⟩
    simp

/-- The zero set is the union of its two halves. -/
theorem union_upper_lower_nontrivialZeroSet :
    upperNontrivialZeroSet ∪ lowerNontrivialZeroSet = nontrivialZeroSet := by
  ext s
  constructor
  · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
  · intro hs
    rcases lt_or_gt_of_ne (im_ne_zero_of_mem_nontrivialZeroSet hs) with h | h
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨hs, h⟩

/-- **There are infinitely many nontrivial zeroes with positive imaginary part.** -/
theorem infinite_upperNontrivialZeroSet : upperNontrivialZeroSet.Infinite := by
  intro hfin
  have hlow : lowerNontrivialZeroSet.Finite := by
    rw [← conj_image_upperNontrivialZeroSet]
    exact hfin.image _
  have : nontrivialZeroSet.Finite := by
    rw [← union_upper_lower_nontrivialZeroSet]
    exact hfin.union hlow
  exact infinite_nontrivialZeroSet this

/-- **There are infinitely many nontrivial zeroes with negative imaginary part.** -/
theorem infinite_lowerNontrivialZeroSet : lowerNontrivialZeroSet.Infinite := by
  rw [← conj_image_upperNontrivialZeroSet]
  exact infinite_upperNontrivialZeroSet.image (Set.injOn_of_injective conj_injective_complex)

/-! ## The parity of the counting function -/

/-- The nontrivial zeroes of height at most `T` with positive imaginary part. -/
def upperNontrivialZeros (T : ℝ) : Set ℂ := {s | s ∈ nontrivialZeros T ∧ 0 < s.im}

/-- The nontrivial zeroes of height at most `T` with negative imaginary part. -/
def lowerNontrivialZeros (T : ℝ) : Set ℂ := {s | s ∈ nontrivialZeros T ∧ s.im < 0}

theorem conj_image_upperNontrivialZeros (T : ℝ) :
    (starRingEnd ℂ) '' upperNontrivialZeros T = lowerNontrivialZeros T := by
  have key : ∀ s : ℂ, s ∈ nontrivialZeros T → (starRingEnd ℂ) s ∈ nontrivialZeros T := by
    rintro s ⟨hz, h0, h1, hT⟩
    obtain ⟨hz', h0', h1'⟩ := conj_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩
    exact ⟨hz', h0', h1', by simpa [abs_neg] using hT⟩
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hspos⟩, rfl⟩
    exact ⟨key s hs, by simpa using hspos⟩
  · rintro ⟨ht, htneg⟩
    exact ⟨(starRingEnd ℂ) t, ⟨key t ht, by simpa using htneg⟩, by simp⟩

theorem union_upper_lower_nontrivialZeros (T : ℝ) :
    upperNontrivialZeros T ∪ lowerNontrivialZeros T = nontrivialZeros T := by
  ext s
  constructor
  · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
  · intro hs
    obtain ⟨hz, h0, h1, -⟩ := id hs
    rcases lt_or_gt_of_ne (im_ne_zero_of_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩) with h | h
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨hs, h⟩

/-- **The counting function is twice the number of zeroes in the upper half-plane**:
`N(T) = 2 · #{ρ : ζ ρ = 0, 0 < re ρ < 1, 0 < im ρ, |im ρ| ≤ T}`. -/
theorem ncard_nontrivialZeros_eq_two_mul (T : ℝ) :
    (nontrivialZeros T).ncard = 2 * (upperNontrivialZeros T).ncard := by
  have hupfin : (upperNontrivialZeros T).Finite :=
    (finite_nontrivialZeros T).subset fun s hs => hs.1
  have hlowfin : (lowerNontrivialZeros T).Finite :=
    (finite_nontrivialZeros T).subset fun s hs => hs.1
  have hdisj : Disjoint (upperNontrivialZeros T) (lowerNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hpos⟩ ⟨-, hneg⟩
    linarith
  have hcard : (lowerNontrivialZeros T).ncard = (upperNontrivialZeros T).ncard := by
    rw [← conj_image_upperNontrivialZeros T,
      Set.ncard_image_of_injective _ conj_injective_complex]
  rw [← union_upper_lower_nontrivialZeros T, Set.ncard_union_eq hdisj hupfin hlowfin, hcard]
  ring

/-- **The number of nontrivial zeroes of height at most `T` is even** — they come in conjugate
pairs, and none is real. -/
theorem even_ncard_nontrivialZeros (T : ℝ) : Even (nontrivialZeros T).ncard := by
  rw [ncard_nontrivialZeros_eq_two_mul T]
  exact even_two_mul _

end RiemannHypothesis
