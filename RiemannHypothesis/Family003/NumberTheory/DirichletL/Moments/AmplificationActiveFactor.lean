/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/AmplificationActiveFactor.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationSourcePool
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def errorMovingExponent (n : ℕ) : ℕ := if n=5 then 0 else 1

theorem residual_six_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*(idealRowHom u (Ideal.span {p})^6)^2 := by ring
    _ = 1 := by rw [hphase,hx];norm_num
    _ = _ := by simp

theorem residual_seven_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*sexticReciprocityPhase p u*
        (idealRowHom u (Ideal.span {p})^6)^2*idealRowHom u (Ideal.span {p})^2 := by ring
    _ = _ := by rw [hphase,hx];ring

theorem error_residual_factor (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

theorem residualColumns_coprime (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (k : ℕ) (I : Ideal O) (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (I : Ideal O) (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end RiemannHypothesis.Family003
