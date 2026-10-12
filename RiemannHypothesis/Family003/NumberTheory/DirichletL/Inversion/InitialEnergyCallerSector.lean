/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerSector.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSector
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedCanonical
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSector
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem markedModeColumn_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl

theorem markedModeColumn_negative_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,negativeChild,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]

end SevenEighths.InverseInitialEnergyCallerSector

end

end RiemannHypothesis.Family003
