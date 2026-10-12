/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/AmplificationSourcePool.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePool
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
    - imports Compat.MathlibBackports (Mathlib lemmas absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationSourceDomain
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.MathlibBackports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePool
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).2

theorem residualColumns_eq (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) :
    residualColumns S p hp k=
      (supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)).filter
        (fun I => IsCoprime (Ideal.span {p}) I) := by
  ext I
  constructor
  · intro hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    have hsJ := valuationColumns_supported S p k J hJ
    have hh := residualIdeal_reconstruct p hp J hsJ
    rw [(Finset.mem_filter.mp hJ).2] at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,residualIdeal_supported p hp J hsJ⟩,
      residualIdeal_coprime p hp J hsJ⟩
    apply (mem_residualPool _ _ S _).mpr
    rw [hh]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
  · intro hI
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hI
    obtain ⟨hpool,hsI⟩ := Finset.mem_filter.mp hI
    have hIS := (mem_residualPool _ _ S I).mp hpool
    let J := (Ideal.span {p})^k*I
    have hsJ : Supported J := by
      rw [supported_mul_iff]
      constructor
      · simpa only [← Ideal.span_singleton_pow] using supported_power p hs k
      · exact hsI
    have hgen : primaryGenerator J=p^k*primaryGenerator I := by
      rw [show J=(Ideal.span {p})^k*I from rfl,primaryGenerator_mul,primaryGenerator_power,
        primaryGenerator_span p hp.ne_zero hpp]
    have hcop' : IsCoprime p (primaryGenerator I) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [primary_span_supported I hsI]
      exact hcop
    have hv : multiplicity p (primaryGenerator J)=k := by
      rw [hgen,multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_primaryGenerator_ne_zero I hsI))),
        multiplicity_pow_self_of_prime hp,
        multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp hcop'),add_zero]
    have hj : J∈valuationColumns S p k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS,hsJ⟩,hv⟩
    refine Finset.mem_image.mpr ⟨J,hj,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero k hs.1)
    have hh := residualIdeal_reconstruct p hp J hsJ
    simpa only [hv] using hh

end SevenEighths.CenteredMomentAmplificationSourcePool

end

end RiemannHypothesis.Family003
