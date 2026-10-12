/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondSectorFrequency.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorFrequency
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondSectorChildren
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorFrequency
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

def sectorFrequency (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) : ℂ :=
  ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
    (if IsCoprime (I:Ideal O) (J:Ideal O) then
      idealCorrelation (C*I) (D*J)
        ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
        ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) j
      else 0)*((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F j I J

theorem sectorFrequency_zero_of_common (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) (hj : idealCorrelation C D hC hD j=0) :
    sectorFrequency η t S β C D hC hD F j=0 := by
  have he := sector_correlation_children η t S β C D hC hD hCD 1 {j} (fun _=>1) F
  simpa only [Finset.sum_singleton,one_mul,hj,zero_mul,mul_zero,Finset.sum_const_zero,
    sectorFrequency] using he

theorem sectorFrequency_common_support (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O)
    (hj : sectorFrequency η t S β C D hC hD F j≠0) : commonFrequencyGenerator C D∣j := by
  by_contra hn
  exact hj (sectorFrequency_zero_of_common η t S β C D hC hD hCD F j
    (idealCorrelation_zero_outside_common C D hC hD hCD j hn))

theorem sectorFrequency_tsum_common (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) :
    (∑' j : O,sectorFrequency η t S β C D hC hD F j)=
      ∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq
    (f := sectorFrequency η t S β C D hC hD F) ?_
  intro j hj
  obtain ⟨w,hw⟩ := sectorFrequency_common_support η t S β C D hC hD hCD F j hj
  exact ⟨w,hw.symm⟩

theorem sectorFrequency_tsum_partition (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ)
    (hs : Summable (fun w : O=>sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))) :
    (∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))=
      ∑ U : Finset (CommonIndex C D),∑' w : O,if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
  have he (w : O) : sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w)=
      ∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
    simp [canonicalPartition,eq_comm]
  calc
    _ = ∑' w : O,∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun U _=>hs.indicator {w | canonicalPartition C D U w})

theorem sectorFrequency_partition_nonunit (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→Ideal O→Ideal O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD F
          ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  let f : O→ℂ := fun w=>if canonicalPartition C D U w then
    sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,ite_eq_right hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end SevenEighths.CenteredMomentSecondSectorFrequency

end

end RiemannHypothesis.Family003
