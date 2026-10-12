/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/SecondWholeMass.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.SecondWholeMass
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.SecondSupportedEnergy

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem actualSecondChild_outer_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).1 = (actualSecondChild p 1 1 x).1 := rfl

theorem actualSecondChild_label_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).2.1 = (actualSecondChild p 1 1 x).2.1 := rfl

theorem actualSecondTriples_units {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) :
    actualSecondTriples p u v source = actualSecondTriples p 1 1 source := rfl

theorem assigned_second_triples_subset {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂) ⊆
      actualSecondTriples p 1 1 source := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

theorem assigned_second_mass_le_original {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (K : ℕ) :
    (∑ γ∈actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),tripleDivisorWeight K γ) ≤
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (assigned_second_triples_subset p u v source J₁ J₂ L₁ L₂)
    (fun γ _ _ => tripleDivisorWeight_nonneg K γ)

end
end SevenEighths.InverseMoment

end RiemannHypothesis.Family003
