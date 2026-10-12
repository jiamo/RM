/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/SourceSelection.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.SourceSelection
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.OriginalChosen
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.MarkedChosenDual
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section

def sourceDependentExtension {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (C : ∀ x, D (f x)) (fallback : ∀ y, D y) (y : Y) : D y :=
  if h : ∃ x, f x=y then h.choose_spec ▸ C h.choose else fallback y

lemma sourceDependentExtension_at {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (hinj : Function.Injective f) (C : ∀ x, D (f x))
    (fallback : ∀ y, D y) (x : X) :
    sourceDependentExtension f C fallback (f x)=C x := by
  have h : ∃ z, f z=f x := ⟨x,rfl⟩
  unfold sourceDependentExtension
  rw [dite_eq_left h]
  have he : h.choose=x := hinj h.choose_spec
  have hcast : ∀ (z x : X) (hf : f z=f x), z=x → (hf ▸ C z)=C x := by
    intro z x hf hx
    subst x
    rfl
  exact hcast _ _ h.choose_spec he

variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

lemma markedActiveSet_injective (e : α⊕β≃γ) :
    Function.Injective (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2) := by
  intro x y he
  have hh := congrArg (optionalPrimeActive (joinedFiberEquiv e)) he
  dsimp only at hh
  rw [← complete_marked_set,← complete_marked_set,
    optionalPrimeActive_completeActiveSet,optionalPrimeActive_completeActiveSet] at hh
  apply Prod.ext
  · have h := congrArg Finset.toLeft hh
    simpa using h
  · have h := congrArg Finset.toRight hh
    simpa using h

theorem exists_marked_source_selection (e : α⊕β≃γ)
    (D : Finset (γ⊕σ)→Type*) (fallback : ∀ A, D A)
    (C : ∀ B : Finset β, ∀ T : Finset σ, D (markedActiveSet e B T)) :
    ∃ E : ∀ A, D A, ∀ B T, E (markedActiveSet e B T)=C B T := by
  refine ⟨sourceDependentExtension (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2)
    (fun q => C q.1 q.2) fallback,?_⟩
  intro B T
  exact sourceDependentExtension_at _ (markedActiveSet_injective e) _ _ (B,T)
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
