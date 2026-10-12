/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/RayQuotient.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.RayQuotient
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.RayFamily
import RiemannHypothesis.Family003.NumberTheory.DirichletL.RayQuotient

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H) : Character :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem principal_iff (χ : RayQuotient.Characters M H) :
    (character M H hH χ).residue = 1 ↔ χ = 1 := by
  rw [character, HeckeRayFamily.principal_iff, RayQuotient.toFullRay_eq_one]

theorem character_entire (χ : RayQuotient.Characters M H) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M H hH χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M H hH χ).mp h))

theorem character_boundary_ne_zero (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M H hH χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M H hH χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M H hH 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ ((principal_iff M H hH 1).mpr rfl)

theorem average_idealCoeff (I : Ideal O) :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

theorem mangoldt_LSeries (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M H hH χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M H hH χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M H hH χ))) s = _ at h
  have heq : idealCoeff (character M H hH χ) = RayQuotient.idealCharacter M H hH χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M H hH χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayQuotient

end

end RiemannHypothesis.Family003
