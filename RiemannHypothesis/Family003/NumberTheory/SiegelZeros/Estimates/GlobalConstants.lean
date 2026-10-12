/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Estimates/GlobalConstants.lean
  Original module: OAI.NumberTheory.SiegelZeros.Estimates.GlobalConstants
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

open CategoryTheory AlgebraicGeometry

namespace SiegelZerosAwei.Workers.W15

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

noncomputable def constantSectionMap : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom

theorem constantSectionMap_bijective [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (constantSectionMap f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  change (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom).IsIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

theorem globalSection_existsUnique_constant [IsIntegral X] [UniversallyClosed f]
    (s : Γ(X, ⊤)) : ∃! c : K, constantSectionMap f c = s := by
  obtain ⟨c, hc⟩ := (constantSectionMap_bijective f).2 s
  exact ⟨c, hc, fun d hd => (constantSectionMap_bijective f).1 (hd.trans hc.symm)⟩

local instance integral_top_nonempty [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩

theorem rationalFunction_constant_of_global [IsIntegral X] [UniversallyClosed f]
    (r : X.functionField)
    (h : ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = r) :
    ∃ c : K, X.germToFunctionField ⊤ (constantSectionMap f c) = r := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨c, hc⟩ := (constantSectionMap_bijective f).2 s
  exact ⟨c, by rw [hc, hs]⟩

end SiegelZerosAwei.Workers.W15

end

end SiegelZeros

end RiemannHypothesis.Family003
