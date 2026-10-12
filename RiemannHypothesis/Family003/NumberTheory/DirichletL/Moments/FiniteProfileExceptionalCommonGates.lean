/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCommonGates.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonGates
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.CommonExceptionalGates
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.CommonLinearSource
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FixedRowMask

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentCommonExceptionalGates CenteredMomentFiniteProfileExceptional
variable {wlo whi:ℝ}
omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Profiles wlo whi)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    ProfileAdmissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end RiemannHypothesis.Family003
