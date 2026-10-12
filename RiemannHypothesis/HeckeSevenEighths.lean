/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization

The proofs of the main theorems are the native absorption of openai/math, family 003
(github.com/openai/math, revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache 2.0; see
NOTICE and LICENSES/openai-math-LICENSE), ported under `RiemannHypothesis/Family003/`.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.Nonvanishing

/-!
# Finite-order Hecke `L`-functions over `ℚ(√-3)` have no zeroes with `re s > 7/8`

This module is the public endpoint of the Hecke part of openai/math family 003 (upstream module
`OAI.NumberTheory.DirichletL.Hecke.Nonvanishing`).  The objects are those of the upstream
character model, compiled here under the namespace `RiemannHypothesis.Family003` (the module and
namespace prefix `OAI` is the only renaming):

* `K = CyclotomicField 3 ℚ` (the Eisenstein field `ℚ(√-3)`), `O` its ring of integers,
  `ω` the primitive cube root of unity in `O`, and `coordinateElement x y = x + y ω`;
* a **character** `χ : Character` is a non-zero ideal `χ.modulus` of `O`, a multiplicative
  character `χ.residue` of `O ⧸ χ.modulus` that is trivial on the units of `O`, and a positive
  integer `χ.period` lying in `χ.modulus` — i.e. a finite-order Hecke character of `K` given by
  its values on residues;
* `LFunction χ s = continuedLattice χ s / 6`, where `continuedLattice χ` is the completed theta
  lattice sum `π^s Γ(s)⁻¹ Λ(s)` of the coefficients `χ.residue (x + y ω mod χ.modulus)` over
  `(x, y) ∈ (ℤ/period)²`, built from Mathlib's `WeakFEPair` machinery.  (The division by
  `6 = |O^×|` is the upstream normalisation passing from lattice points to ideals; the
  identification with the Dirichlet series `∑ χ(𝔞) N𝔞^{-s}` is part of the upstream development
  and is not restated in this module.)

The section *Correspondence* below states each of these definitions as an equation and proves
it by `rfl`, so the native objects are, definitionally, the ones of the upstream comparator
statement `ComparatorChallenges/HeckeSevenEighths.lean`.

## Main results

* `LFunction_ne_zero_of_seven_eighths_lt_re` — `LFunction χ s ≠ 0` for `7/8 < re s`, except
  at `s = 1` for a principal character (`χ.residue = 1`).
* `LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re` — the same for the character built from a
  residue character `χ` of `O ⧸ M` that is trivial on units (`Character.ofResidue`).
* `rayCharacter_LFunction_ne_zero_of_seven_eighths_lt_re` — the same for ray-class characters
  modulo a non-zero ideal `M`.

This is a statement about these Hecke `L`-functions over the one field `ℚ(√-3)`; it says nothing
about other number fields, and nothing about the Riemann hypothesis.
-/

namespace RiemannHypothesis.HeckeSevenEighths

open RiemannHypothesis.Family003.SevenEighths

/-! ## Correspondence with the upstream character model -/

section Correspondence

open HeckeFamily

theorem O_eq : HeckeFamily.O = NumberField.RingOfIntegers (CyclotomicField 3 ℚ) := rfl

theorem coordinateElement_eq (x y : ℤ) :
    coordinateElement x y = (x : HeckeFamily.O) + (y : HeckeFamily.O) * omega := rfl

theorem elementCoeff_eq (χ : Character) (z : HeckeFamily.O) :
    elementCoeff χ z = χ.residue (Ideal.Quotient.mk χ.modulus z) := rfl

theorem coefficients_eq (χ : Character) (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = elementCoeff χ (coordinateElement a.1 a.2) := rfl

theorem continuedLattice_eq (χ : Character) :
    continuedLattice χ = HeckeTheta.latticeL (coefficients χ) := rfl

theorem LFunction_eq (χ : Character) (s : ℂ) :
    HeckeFamily.LFunction χ s = continuedLattice χ s / 6 := rfl

theorem latticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) :
    HeckeTheta.latticeL w s =
      (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * HeckeTheta.completed w s := rfl

theorem completed_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    HeckeTheta.completed w = (HeckeTheta.pair w).Λ := rfl

/-- A character is exactly the data of the upstream structure: a non-zero modulus, a residue
character trivial on units, and a positive period in the modulus. -/
example (M : Ideal HeckeFamily.O) (hM : M ≠ ⊥) (r : MulChar (HeckeFamily.O ⧸ M) ℂ)
    (hu : ∀ u : (HeckeFamily.O)ˣ, r (Ideal.Quotient.mk M (u : HeckeFamily.O)) = 1)
    (N : ℕ) (hN : 0 < N) (hNM : (N : HeckeFamily.O) ∈ M) :
    let χ : Character := ⟨M, hM, r, hu, N, hN, hNM⟩
    χ.modulus = M ∧ χ.period = N := ⟨rfl, rfl⟩

/-- The character model is inhabited: the unit ideal with the trivial residue character and
period `1` is a character, so the main theorem is not vacuous. -/
example : Nonempty HeckeFamily.Character :=
  ⟨⟨⊤, top_ne_bot, 1,
    fun u => MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (⊤ : Ideal HeckeFamily.O))),
    1, one_pos, Submodule.mem_top⟩⟩

end Correspondence

/-! ## Main results -/

/-- **Quasi-Riemann hypothesis for finite-order Hecke `L`-functions over `ℚ(√-3)`.** -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re (χ : HeckeFamily.Character) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

/-- The same, for the character attached to a residue character trivial on units. -/
theorem LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re
    (M : Ideal HeckeFamily.O) (hM : M ≠ ⊥) (χ : MulChar (HeckeFamily.O ⧸ M) ℂ)
    (hu : ∀ u : (HeckeFamily.O)ˣ, χ (Ideal.Quotient.mk M (u : HeckeFamily.O)) = 1)
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    HeckeFamily.LFunction (HeckeFamily.Character.ofResidue M hM χ hu) s ≠ 0 :=
  HeckeFamily.LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re M hM χ hu hs hpole

section Ray

variable (M : Ideal HeckeFamily.O) [NeZero M]

local instance : Finite (HeckeFamily.O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The same, for ray-class characters modulo a non-zero ideal `M`. -/
theorem rayCharacter_LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : RiemannHypothesis.Family003.SevenEighths.RayOrthogonality.rayCharacters M) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    HeckeFamily.LFunction (HeckeRayFamily.character M χ) s ≠ 0 :=
  HeckeRayFamily.LFunction_ne_zero_of_seven_eighths_lt_re M χ hs hpole

end Ray

end RiemannHypothesis.HeckeSevenEighths
