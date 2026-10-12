/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/CommonLinearNormalization.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.CommonLinearSource
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.CommonRawCost

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

omit [DecidableEq ι] in
theorem commonScalar_sq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P:=
  CenteredMomentDivisorRawEnergy.normalized_norm_sq _
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) _

omit [DecidableEq ι] in
theorem commonScalar_sq_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2≤
      ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ):=by
  rw [commonScalar_sq]
  exact frozen_normalized_cost B.val (alloc_ne s C B) C R hC
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
    s.M_ge_one s.lower s.upper s.lower_pos s.slot_support

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end RiemannHypothesis.Family003
