/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondExceptionalSourceFamily.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondEnergySplit
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondExceptionalKernel

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalSourceFamily
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalKernel
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredExceptionalProfile
local notation "O"=>HeckeFamily.O

lemma exceptional_part_nonzero (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):z≠0:=
  sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1

lemma exceptional_part_inducing (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):
    FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z:=
  (Finset.mem_filter.mp hz).2

lemma actual_family_both_rows (η:Character)(χ₀:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (τ:RayCharacter→Character)(hf:Family η C D hC hD U τ)(R:ℝ):
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)):=by
  have hz0:=exceptional_part_nonzero η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing η χ₀ Q m C D U R
  constructor
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ χ Q hQ m _ hml hm2 _ hex).1 z hz
    exact (hf.inducing_iff χ Q m z hm (hz0 z hz) hml hm2).mp hh
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ (χ⁻¹) Q hQ m _ hml hm2 _ hex).2 z hz
    simp only [inv_inv] at hh
    exact (hf.inducing_iff χ Q m (-z) hm (neg_ne_zero.mpr (hz0 z hz)) hml hm2).mp hh

lemma exceptional_part_live (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    liveRows C D U R (partRows true η χ₀ Q m C D U R)=
      partRows true η χ₀ Q m C D U R:=by
  apply Finset.filter_eq_self.mpr
  intro z hz
  exact liveRows_weight C D U R _ z (Finset.mem_filter.mp hz).1

end SevenEighths.CenteredMomentSecondExceptionalSourceFamily

end

end RiemannHypothesis.Family003
