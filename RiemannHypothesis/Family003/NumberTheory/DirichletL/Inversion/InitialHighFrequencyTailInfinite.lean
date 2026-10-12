/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailInfinite.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailInfinite
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O"=>ActualEisensteinCubic.O

theorem weighted_radial_summable (Φ : 𝓢(ℝ,ℂ)) (K Γ : ℝ) (hK : 0<K)
    (P : O→Prop) (a : O→ℂ) (ha : ∀h,P h→‖a h‖≤Γ) :
    Summable (fun h : {h:O // P h}=>a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)) := by
  apply Summable.of_norm_bounded
    (((paperRadialFourier_lattice_summable_norm Φ K hK).subtype P).mul_left Γ)
  intro h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha h.val h.property) (norm_nonneg _)

theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f) (B : ℝ)
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤B) : ‖∑'h,f h‖≤B := by
  exact le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)

theorem weighted_radial_tsum_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (P : O→Prop) (a : O→ℂ),
    (∀h,P h→T≤K*‖eisEmbedding h‖^2) → (∀h,P h→‖a h‖≤Γ) →
    ‖∑'h : {h:O // P h},a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)‖≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := finite_radial_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ P a htail ha
  apply norm_tsum_of_finite_bound _ (weighted_radial_summable Φ K Γ hK P a ha)
  intro F
  have hi : Function.Injective (fun h : {h:O // P h}=>h.val) := Subtype.val_injective
  have he : (∑h∈F,a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2))=
      ∑h∈F.image Subtype.val,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2) := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ hh=>hi hh
  rw [he]
  apply hbound Φ K T Γ hK hT hΓ (F.image Subtype.val) a
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact htail x.val x.property
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact ha x.val x.property

end SevenEighths.InverseInitialHighFrequencyTail

end

end RiemannHypothesis.Family003
