/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/LowSlotMarks.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotMarks
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.LowSlotPolynomial
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.CanonicalSlots
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSelectedIdeal_eq_product {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  exact map_prod CanonicalRowCompletion.principalIdealHom _ _

lemma lowSelectedIdeal_dvd_iff {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop

lemma lowSelectedIdeal_mark {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val

lemma lowCanonicalSelectedPrime_mem {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property

lemma lowCanonicalSelectedPrime_span {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalSelectedPrime_injective {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)

lemma lowCanonicalSelected_coprime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

theorem lowCanonicalSelected_mark {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (A : Id) :
    (if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if (lowCanonicalSelectedPrime T hT J b i).val∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b)]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
