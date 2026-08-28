/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroSymmetryCount

/-!
# Off-line zeroes come in quadruples

The two symmetries of `ζ` inside the critical strip — conjugation `s ↦ conj s` and reflection in
the point `1/2`, `s ↦ 1 - s` — generate a Klein four-group acting on the set of nontrivial
zeroes.  The composite `s ↦ 1 - conj s` is the reflection in the *critical line*: it fixes the
imaginary part and sends `re s` to `1 - re s`.  Consequently a nontrivial zero `ρ` that is **not**
on the critical line has four distinct companions

`ρ`, `conj ρ`, `1 - ρ`, `1 - conj ρ`,

all of them nontrivial zeroes of the same height `|im ρ|`.  This file makes that precise and reads
it off the counting function.  Writing

`N_off(T) = #{ρ : ζ ρ = 0, 0 < re ρ < 1, re ρ ≠ 1/2, |im ρ| ≤ T}`

for the number of off-line nontrivial zeroes of height at most `T` (counted, as everywhere in this
repository, *without* multiplicity), the results are:

* `offLineQuadruple_distinct` — for an off-line nontrivial zero the four companions above are
  pairwise distinct nontrivial zeroes of the same height;
* `ncard_offLineNontrivialZeros_eq_four_mul` — `N_off(T) = 4 · #{ρ : off-line zero of height
  at most `T` with `re ρ < 1/2` and `im ρ > 0`}`;
* `four_dvd_ncard_offLineNontrivialZeros` — hence `4 ∣ N_off(T)`;
* `four_le_ncard_offLineNontrivialZeros` — if the Riemann hypothesis fails at some height, it
  fails at least four times there.

Nothing here decides whether `N_off(T)` is zero: the Riemann hypothesis is not proved or disproved
anywhere in this repository.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-! ## The two symmetries on zeroes of bounded height -/

/-- The nontrivial zeroes of height at most `T` are stable under conjugation. -/
theorem conj_mem_nontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T) :
    (starRingEnd ℂ) s ∈ nontrivialZeros T := by
  obtain ⟨hz, h0, h1, hT⟩ := hs
  obtain ⟨hz', h0', h1'⟩ := conj_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩
  exact ⟨hz', h0', h1', by simpa [abs_neg] using hT⟩

/-- The nontrivial zeroes of height at most `T` are stable under `s ↦ 1 - s`. -/
theorem one_sub_mem_nontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T) :
    1 - s ∈ nontrivialZeros T := by
  obtain ⟨hz, h0, h1, hT⟩ := hs
  obtain ⟨hz', h0', h1'⟩ := one_sub_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩
  exact ⟨hz', h0', h1', by simpa [abs_neg] using hT⟩

/-- Reflection in the critical line, `s ↦ 1 - conj s`.  It fixes the imaginary part and sends
`re s` to `1 - re s`. -/
def criticalReflect (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

@[simp] lemma criticalReflect_re (s : ℂ) : (criticalReflect s).re = 1 - s.re := by
  simp [criticalReflect]

@[simp] lemma criticalReflect_im (s : ℂ) : (criticalReflect s).im = s.im := by
  simp [criticalReflect]

@[simp] lemma criticalReflect_criticalReflect (s : ℂ) :
    criticalReflect (criticalReflect s) = s := by
  apply Complex.ext <;> simp

lemma criticalReflect_injective : Function.Injective criticalReflect := fun a b h => by
  simpa using congrArg criticalReflect h

/-- Reflection in the critical line preserves the nontrivial zeroes of height at most `T`. -/
theorem criticalReflect_mem_nontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T) :
    criticalReflect s ∈ nontrivialZeros T :=
  one_sub_mem_nontrivialZeros (conj_mem_nontrivialZeros hs)

/-! ## The quadruple attached to an off-line zero -/

/-- **An off-line nontrivial zero has four distinct companions.**  If `ρ` is a nontrivial zero of
height at most `T` with `re ρ ≠ 1/2`, then `ρ`, `conj ρ`, `1 - ρ` and `1 - conj ρ` are four
pairwise distinct nontrivial zeroes of height at most `T`, none of them on the critical line. -/
theorem offLineQuadruple_distinct {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T)
    (hre : s.re ≠ 1 / 2) :
    ((starRingEnd ℂ) s ∈ nontrivialZeros T ∧ (1 - s) ∈ nontrivialZeros T ∧
      criticalReflect s ∈ nontrivialZeros T) ∧
    (((starRingEnd ℂ) s).re ≠ 1 / 2 ∧ (1 - s).re ≠ 1 / 2 ∧ (criticalReflect s).re ≠ 1 / 2) ∧
    (s ≠ (starRingEnd ℂ) s ∧ s ≠ 1 - s ∧ s ≠ criticalReflect s ∧
      (starRingEnd ℂ) s ≠ 1 - s ∧ (starRingEnd ℂ) s ≠ criticalReflect s ∧
      1 - s ≠ criticalReflect s) := by
  obtain ⟨hz, h0, h1, hT⟩ := hs
  have him : s.im ≠ 0 := im_ne_zero_of_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩
  refine ⟨⟨conj_mem_nontrivialZeros ⟨hz, h0, h1, hT⟩, one_sub_mem_nontrivialZeros ⟨hz, h0, h1, hT⟩,
      criticalReflect_mem_nontrivialZeros ⟨hz, h0, h1, hT⟩⟩, ⟨by simpa using hre, ?_, ?_⟩, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]
    intro h; apply hre; linarith
  · simp only [criticalReflect_re]
    intro h; apply hre; linarith
  · intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    exact him (by linarith)
  · intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at this
    exact him (by linarith)
  · intro h
    have := congrArg Complex.re h
    simp only [criticalReflect_re] at this
    exact hre (by linarith)
  · intro h
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.sub_re, Complex.one_re] at this
    exact hre (by linarith)
  · intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im, criticalReflect_im] at this
    exact him (by linarith)
  · intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, zero_sub, criticalReflect_im] at this
    exact him (by linarith)

/-! ## The four quarters of the off-line zero set -/

/-- The off-line nontrivial zeroes of height at most `T`. -/
def offLineNontrivialZeros (T : ℝ) : Set ℂ := {s | s ∈ nontrivialZeros T ∧ s.re ≠ 1 / 2}

/-- The off-line nontrivial zeroes of height at most `T` in the upper half-plane. -/
def upperOffLineNontrivialZeros (T : ℝ) : Set ℂ :=
  {s | s ∈ nontrivialZeros T ∧ s.re ≠ 1 / 2 ∧ 0 < s.im}

/-- The off-line nontrivial zeroes of height at most `T` in the lower half-plane. -/
def lowerOffLineNontrivialZeros (T : ℝ) : Set ℂ :=
  {s | s ∈ nontrivialZeros T ∧ s.re ≠ 1 / 2 ∧ s.im < 0}

/-- The nontrivial zeroes of height at most `T` in the upper half-plane and to the left of the
critical line. -/
def leftUpperNontrivialZeros (T : ℝ) : Set ℂ :=
  {s | s ∈ nontrivialZeros T ∧ s.re < 1 / 2 ∧ 0 < s.im}

/-- The nontrivial zeroes of height at most `T` in the upper half-plane and to the right of the
critical line. -/
def rightUpperNontrivialZeros (T : ℝ) : Set ℂ :=
  {s | s ∈ nontrivialZeros T ∧ 1 / 2 < s.re ∧ 0 < s.im}

lemma offLineNontrivialZeros_finite (T : ℝ) : (offLineNontrivialZeros T).Finite :=
  (finite_nontrivialZeros T).subset fun _ hs => hs.1

lemma upperOffLineNontrivialZeros_finite (T : ℝ) : (upperOffLineNontrivialZeros T).Finite :=
  (finite_nontrivialZeros T).subset fun _ hs => hs.1

lemma lowerOffLineNontrivialZeros_finite (T : ℝ) : (lowerOffLineNontrivialZeros T).Finite :=
  (finite_nontrivialZeros T).subset fun _ hs => hs.1

lemma leftUpperNontrivialZeros_finite (T : ℝ) : (leftUpperNontrivialZeros T).Finite :=
  (finite_nontrivialZeros T).subset fun _ hs => hs.1

lemma rightUpperNontrivialZeros_finite (T : ℝ) : (rightUpperNontrivialZeros T).Finite :=
  (finite_nontrivialZeros T).subset fun _ hs => hs.1

/-- Conjugation maps the upper off-line zeroes bijectively onto the lower ones. -/
theorem conj_image_upperOffLineNontrivialZeros (T : ℝ) :
    (starRingEnd ℂ) '' upperOffLineNontrivialZeros T = lowerOffLineNontrivialZeros T := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hre, hpos⟩, rfl⟩
    exact ⟨conj_mem_nontrivialZeros hs, by simpa using hre, by simpa using hpos⟩
  · rintro ⟨ht, hre, hneg⟩
    exact ⟨(starRingEnd ℂ) t, ⟨conj_mem_nontrivialZeros ht, by simpa using hre,
      by simpa using hneg⟩, by simp⟩

/-- Reflection in the critical line maps the upper-left nontrivial zeroes bijectively onto the
upper-right ones. -/
theorem criticalReflect_image_leftUpperNontrivialZeros (T : ℝ) :
    criticalReflect '' leftUpperNontrivialZeros T = rightUpperNontrivialZeros T := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hre, hpos⟩, rfl⟩
    refine ⟨criticalReflect_mem_nontrivialZeros hs, ?_, by simpa using hpos⟩
    simp only [criticalReflect_re]; linarith
  · rintro ⟨ht, hre, hpos⟩
    refine ⟨criticalReflect t, ⟨criticalReflect_mem_nontrivialZeros ht, ?_, by simpa using hpos⟩,
      by simp⟩
    simp only [criticalReflect_re]; linarith

/-- The off-line zeroes of height at most `T` split into their upper and lower halves. -/
theorem union_upper_lower_offLineNontrivialZeros (T : ℝ) :
    upperOffLineNontrivialZeros T ∪ lowerOffLineNontrivialZeros T = offLineNontrivialZeros T := by
  ext s
  constructor
  · rintro (⟨hs, hre, -⟩ | ⟨hs, hre, -⟩) <;> exact ⟨hs, hre⟩
  · rintro ⟨hs, hre⟩
    obtain ⟨hz, h0, h1, -⟩ := id hs
    rcases lt_or_gt_of_ne (im_ne_zero_of_mem_nontrivialZeroSet (s := s) ⟨hz, h0, h1⟩) with h | h
    · exact Or.inr ⟨hs, hre, h⟩
    · exact Or.inl ⟨hs, hre, h⟩

/-- The upper off-line zeroes split according to which side of the critical line they lie on. -/
theorem union_left_right_upperOffLineNontrivialZeros (T : ℝ) :
    leftUpperNontrivialZeros T ∪ rightUpperNontrivialZeros T = upperOffLineNontrivialZeros T := by
  ext s
  constructor
  · rintro (⟨hs, hre, hpos⟩ | ⟨hs, hre, hpos⟩)
    · exact ⟨hs, ne_of_lt hre, hpos⟩
    · exact ⟨hs, (ne_of_lt hre).symm, hpos⟩
  · rintro ⟨hs, hre, hpos⟩
    rcases lt_or_gt_of_ne hre with h | h
    · exact Or.inl ⟨hs, h, hpos⟩
    · exact Or.inr ⟨hs, h, hpos⟩

/-! ## The counting consequences -/

/-- The upper off-line zeroes are exactly twice as many as the upper-left ones. -/
theorem ncard_upperOffLineNontrivialZeros_eq_two_mul (T : ℝ) :
    (upperOffLineNontrivialZeros T).ncard = 2 * (leftUpperNontrivialZeros T).ncard := by
  have hdisj : Disjoint (leftUpperNontrivialZeros T) (rightUpperNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hleft, -⟩ ⟨-, hright, -⟩
    linarith
  have hcard : (rightUpperNontrivialZeros T).ncard = (leftUpperNontrivialZeros T).ncard := by
    rw [← criticalReflect_image_leftUpperNontrivialZeros T,
      Set.ncard_image_of_injective _ criticalReflect_injective]
  rw [← union_left_right_upperOffLineNontrivialZeros T,
    Set.ncard_union_eq hdisj (leftUpperNontrivialZeros_finite T)
      (rightUpperNontrivialZeros_finite T), hcard]
  ring

/-- **The off-line nontrivial zeroes of bounded height come in quadruples**:
`N_off(T) = 4 · #{ρ : ζ ρ = 0, 0 < re ρ < 1/2, 0 < im ρ ≤ T}`. -/
theorem ncard_offLineNontrivialZeros_eq_four_mul (T : ℝ) :
    (offLineNontrivialZeros T).ncard = 4 * (leftUpperNontrivialZeros T).ncard := by
  have hdisj : Disjoint (upperOffLineNontrivialZeros T) (lowerOffLineNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, -, hpos⟩ ⟨-, -, hneg⟩
    linarith
  have hcard :
      (lowerOffLineNontrivialZeros T).ncard = (upperOffLineNontrivialZeros T).ncard := by
    rw [← conj_image_upperOffLineNontrivialZeros T,
      Set.ncard_image_of_injective _ conj_injective_complex]
  rw [← union_upper_lower_offLineNontrivialZeros T,
    Set.ncard_union_eq hdisj (upperOffLineNontrivialZeros_finite T)
      (lowerOffLineNontrivialZeros_finite T), hcard,
    ncard_upperOffLineNontrivialZeros_eq_two_mul T]
  ring

/-- **The number of off-line nontrivial zeroes of height at most `T` is divisible by four.** -/
theorem four_dvd_ncard_offLineNontrivialZeros (T : ℝ) :
    4 ∣ (offLineNontrivialZeros T).ncard :=
  ⟨_, ncard_offLineNontrivialZeros_eq_four_mul T⟩

/-- **A counterexample to the Riemann hypothesis never comes alone**: if some nontrivial zero of
height at most `T` lies off the critical line, then at least four do. -/
theorem four_le_ncard_offLineNontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T)
    (hre : s.re ≠ 1 / 2) : 4 ≤ (offLineNontrivialZeros T).ncard := by
  have hne : (offLineNontrivialZeros T).Nonempty := ⟨s, hs, hre⟩
  have hpos : 0 < (offLineNontrivialZeros T).ncard :=
    (Set.ncard_pos (offLineNontrivialZeros_finite T)).2 hne
  obtain ⟨k, hk⟩ := four_dvd_ncard_offLineNontrivialZeros T
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [hk] at hpos
  · omega

end RiemannHypothesis
