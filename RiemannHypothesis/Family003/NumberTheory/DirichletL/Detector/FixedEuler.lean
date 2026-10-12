/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/FixedEuler.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.FixedEuler
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - proof tweak: after convert, close residual instance-equality goals with 'with_reducible_and_instances rfl' (host instances are not reducibly defeq)
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighExcludedLocal
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.RayFamily
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.ModulusRefinement

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P) : Character :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

theorem LFunction_hasProd_outside (χ : Character) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert (preTransparency := .instances) h using 1
  all_goals try with_reducible_and_instances rfl
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem fixedSourcePrincipal_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

theorem excludedTarget_hasProd (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
