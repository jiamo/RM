/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/Reindex.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.Reindex
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.SlotHeight

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i:T=>pool (e i)) (fun i:T=>coeff (e i))
      (fun i:T=>P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i)
      (fun i:T.map e=>P i) X₁ X₂ keep Φ K:=
  energy_reindex (Finset.equivMap e T) η m A W₁ W₂
    (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i)
    t X₁ X₂ keep Φ K

end SevenEighths.CenteredMomentEnergyReindex

end

end RiemannHypothesis.Family003
