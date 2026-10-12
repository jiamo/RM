/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/MarkedExclusions.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.MarkedProduct
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.FirstBoundary

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => HeckeFamily.O

theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (fun _=>le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>firstPrimeDefectBound_nonneg eps P.val)
      (fun _=>le_rfl) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (T : Finset PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left

end SevenEighths.ProbeHighRowFamily

end

end RiemannHypothesis.Family003
