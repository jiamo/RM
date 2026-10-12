/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/ZeroGrowthBounds.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounds
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.ZeroGrowthReflection
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.ZeroReferenceError

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1<Z)(hb:0<b)(hx:0<Xlong)(hsupport:1≤b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤defect)
    (hL:Mcap+Bmask+defect+xi≤L)(hL0:0≤L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CompletedGauss.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0<X→X≤Z^L→
      ∀D:Finset (Ideal O),D∈(CompletedGauss.primeSupport s.puncture).powerset→
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end SevenEighths.CenteredMomentEnergyZeroGrowthBounds

end

end RiemannHypothesis.Family003
