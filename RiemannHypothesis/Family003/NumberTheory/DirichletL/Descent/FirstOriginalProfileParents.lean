/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/FirstOriginalProfileParents.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.FirstOriginalProfileCellEnergy
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.FirstGlobalCaps

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

lemma originalChildEnergy_eq_caps (hp : ∀i,p i≠0)
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) :
    originalChildEnergy p hp hg hinj pool Q k l negative Ψ m mark omega T t Y=
      ∑x∈InverseFirstGlobalCaps.outerCell p pool Q k,
        firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
          (mark (if negative then x.1.rightExponent else x.1.leftExponent))
          (commonSelector p (fun _=>1) l) omega T t Y := by
  rw [originalChildEnergy,originalOuterCell_eq_caps]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end RiemannHypothesis.Family003
