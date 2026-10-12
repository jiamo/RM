/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongWeight.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongWeight
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.TripleMass

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤Z→V≤L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤Z^V→secondLabelWeight K I≤C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤C*Z^eps:=by gcongr

theorem normalized_second_energy_le_actual_family (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,goodLambda∉Ideal.span {p i})
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (W:ℝ→ℂ)(X Z F V R:ℝ),1≤Z→0<R→V≤L→
      (∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W X Z F≤
        C*Z^(-F+eps)*rowFamilyEnergy labels (fun I k=>
          finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) R := by
  obtain ⟨C,hC,hh⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg pool Ψ m slots lists a labels hlabels W X Z F V R hZ hR hV hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=normalized_energy_le_actual_family p hp hcop hg pool Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (admissible_supported (hlabels I hI)))
    (secondLabelWeight K) (C*Z^eps) (by positivity)
    (fun I hI=>⟨by unfold secondLabelWeight;positivity,
      hh Z V hZ hV I (hlabels I hI).1 (hnorm I hI)⟩) W X Z F R hz hR
  convert (preTransparency := .instances) hb using 1
  rw [Real.rpow_add hz]
  ring

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
