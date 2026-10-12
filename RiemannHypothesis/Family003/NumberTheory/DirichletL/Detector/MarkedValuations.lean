/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/MarkedValuations.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.MarkedValuations
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighExcludedEuler
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.EulerMarked
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_valuation (P : PrimeIdeal) (I : Id) (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=>h.2⟩

lemma prime_dvd_high_completed (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp only [highIdeals,primeValuations_idealFromValuations,Finsupp.add_apply,
    Finsupp.mapRange_apply,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

lemma primeProduct_dvd (T : Finset PrimeIdeal) (I : Id) :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem _ hP).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ=>primeIdeal_coprime P Q hPQ) h

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm (_P : PrimeIdeal) (b : HighValuation) :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product (T : Finset PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro P hP
    exact ite_eq_left (h P hP)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp only [completedValuationMark,hv,ne_eq,not_true_eq_false,ite_false]

lemma highIdealMask_mark (S : Finset Id) (D I J K L : Id) :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
