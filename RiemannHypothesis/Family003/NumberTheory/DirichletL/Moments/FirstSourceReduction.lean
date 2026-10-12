/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstSourceReduction.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstRetainedNorm
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SourceInputFirstRemainder
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSourceReduction
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource (activeSource)
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

 theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K‖/volume s.toData≤
      physicalMass s R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
      (volume s.toData) Z ξ‖≤physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith

end SevenEighths.CenteredMomentFirstSourceReduction

end

end RiemannHypothesis.Family003
