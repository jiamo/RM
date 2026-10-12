/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceFiber.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePhysical
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.DetectorDictionarySource

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

def fiberSector (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (θ : selected→RayQuotient.Characters M H) (u : FreeRow) : ℂ :=
  sectorValue M H hH (naturalRow η u.val u.property.1).character η 1
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>fun y=>conj (F.profile s.val y)) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>1-(F.external s.val).re)
    (fun s : selected=>-(F.external s.val).im) 0 (U^F.m) (U^F.m) θ

theorem detectorPositiveRow_sector {Slot : Type*}
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) (hU : 0<U) :
    detectorPositiveRow F η selected j k σ t u=
      averageWeight (ι:=selected) M H*∑θ : selected→RayQuotient.Characters M H,
        fiberSector hH F η selected j k σ t θ u := by
  have he:=natural_physical_product M H hH (naturalRow η u.val u.property.1) η 1 one_ne_zero
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    0 (U^F.m) (U^F.m) (by positivity) (fun _=>Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)] at he
  simpa only [detectorPositiveRow,rowMaskElement_eq_fixed,fiberSector] using he

theorem fiber_plain_sector_energy (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)≤
      ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
        ∑u∈F.rows,‖fiberSector hH F η selected j k σ t θ u‖^2 := by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  calc
    _≤∑u∈F.rows,∑θ : selected→RayQuotient.Characters M H,
        ‖averageWeight (ι:=selected) M H‖*‖fiberSector hH F η selected j k σ t θ u‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [detectorPositiveRow_sector hH F η selected j k σ t u hU]
      exact sector_average_energy M H _
    _= _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end RiemannHypothesis.Family003
