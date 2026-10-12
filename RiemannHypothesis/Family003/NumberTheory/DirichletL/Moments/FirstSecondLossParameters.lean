/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/FirstSecondLossParameters.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters
open CenteredMomentFirstSecondCapacityLedger

def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

theorem numerical_choices (Mcap ε:ℝ)(hε:0<ε):
    ∃σ ξ mesh:ℝ,0<σ ∧ σ≤1 ∧ σ≤ε/100 ∧ 0<ξ ∧ 0<mesh ∧ mesh≤ξ ∧
      5*ξ≤σ/2 ∧ Mcap<(depth Mcap σ:ℝ)*σ/2 ∧
      (depth Mcap σ:ℝ)*(7*ξ/2+mesh)≤ε/32 ∧
      3*σ+5*ξ/6+7*ξ/2+mesh≤ε/16 := by
  let σ:ℝ:=min 1 (ε/100)
  have hσ:0<σ:=lt_min (by norm_num) (by positivity)
  have hσ₁:σ≤1:=min_le_left _ _
  have hσε:σ≤ε/100:=min_le_right _ _
  let n:=depth Mcap σ
  let ξ:ℝ:=min (σ/100) (ε/(200*((n:ℝ)+1)))
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have hξ:0<ξ:=lt_min (by positivity) (by positivity)
  have hξσ:ξ≤σ/100:=min_le_left _ _
  have hξε:ξ≤ε/(200*((n:ℝ)+1)):=min_le_right _ _
  have he:ξ*(200*((n:ℝ)+1))≤ε:=(le_div_iff₀ (by positivity)).mp hξε
  have hne:(n:ℝ)*ξ≤ε/200:=by nlinarith
  refine ⟨σ,ξ,ξ,hσ,hσ₁,hσε,hξ,hξ,le_rfl,?_,depth_covers Mcap σ hσ,?_,?_⟩
  · linarith
  · change (n:ℝ)*(7*ξ/2+ξ)≤ε/32
    nlinarith
  · linarith

theorem edge_with_choices (δ₁ δ₂ θ κ mesh ξ:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤ξ):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤9*ξ/2 := by
  have hh:=edge_loss_budget δ₁ δ₂ θ κ mesh ξ ξ hδ₁ hδ₂ hθ hκ hm hmesh
  linarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end RiemannHypothesis.Family003
