/-
Host-compatibility backport (Fredholm operators) for the native absorption of openai/math,
family 003 (source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.  At
the host pin (Mathlib db584cd6d46c92f209a44c0f1c829460d327499d),
`Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean` stops after the definition of
`IsFredholm` and its characterisations; the section `Constructions` of the upstream file
(`IsClosedEmbedding.isFredholm`, `IsFredholm.comp`, `isFredholm_domRestrict_iff`, ...) is not
there.  This file is that upstream section, copied verbatim from Mathlib d13f23b7 (Mathlib is
Apache 2.0; copyright (c) the authors of `Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean`),
compiled against the host's definition of `IsFredholm` (which is identical upstream and here),
with one host-compatibility edit: the nine upstream theorems `Function.Bijective.isFredholm_iff`,
`isInvertible_iff_isFredholm_and_bijective`, `Submodule.isFredholm_projectionOntoL(_iff)`,
`FredholmDecomposition.isFredholm_proj`, `Submodule.isFredholm_projectionL(_iff)` and
`IsIdempotentElem.isFredholm(_iff)` are omitted, because their proofs use upstream lemmas
(`isInvertible_iff_isHomeomorph`, `isQuotientMap_projectionOnto`) that the host lacks and
nothing in the absorbed closure uses them.

Proof status: ADAPTED (upstream Mathlib proofs).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite

noncomputable section

open Topology Submodule LinearMap Function
open Set (MapsTo)
open LinearMap.FiniteRangeSetoid

namespace ContinuousLinearMap
section TVS

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

section Constructions

/-!
## Constructions of Fredholm operators
-/

theorem _root_.Topology.IsClosedEmbedding.isFredholm {f : E →L[𝕜] F}
    (hf : IsClosedEmbedding f) (h_cofg : f.range.CoFG) :
    IsFredholm f where
  isStrictMap := hf.isStrictMap
  isClosed_range := hf.isClosed_range
  finite_ker := by
    rw [LinearMap.ker_eq_bot.2 hf.injective]
    infer_instance
  finite_coker := h_cofg
  closedComplemented_ker := by
    rw [LinearMap.ker_eq_bot.2 hf.injective]
    exact closedComplemented_bot

theorem _root_.Function.Injective.isFredholm_iff (f : E →L[𝕜] F)
    (f_inj : Injective f) :
    IsFredholm f ↔ IsClosedEmbedding f ∧ f.range.CoFG := by
  refine ⟨fun hf ↦ ⟨⟨?_, hf.isClosed_range⟩, hf.finite_coker⟩,
    fun ⟨hf, h_cofg⟩ ↦ hf.isFredholm h_cofg⟩
  simpa [isEmbedding_iff_isStrictMap_injective, f_inj] using hf.isStrictMap

theorem _root_.Submodule.isFredholm_subtypeL_iff {p : Submodule 𝕜 E} :
    IsFredholm p.subtypeL ↔ IsClosed (p : Set E) ∧ p.CoFG := by
  simp [p.subtype_injective.isFredholm_iff p.subtypeL, isClosedEmbedding_iff,
    IsEmbedding.subtypeVal]

theorem _root_.Submodule.isFredholm_subtypeL {p : Submodule 𝕜 E}
    (hp : IsClosed (p : Set E)) [p.CoFG] :
    IsFredholm p.subtypeL :=
  isFredholm_subtypeL_iff.mpr ⟨hp, inferInstance⟩

theorem _root_.ContinuousLinearEquiv.isFredholm (e : E ≃L[𝕜] F) :
    IsFredholm (e : E →L[𝕜] F) :=
  e.isHomeomorph.isClosedEmbedding.isFredholm (by simp)

protected theorem IsFredholm.id : IsFredholm (.id 𝕜 E) :=
  ContinuousLinearEquiv.refl 𝕜 E |>.isFredholm

theorem IsInvertible.isFredholm {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    IsFredholm f := by
  rcases hf with ⟨e, rfl⟩
  exact e.isFredholm

theorem _root_.Topology.IsQuotientMap.isFredholm {f : E →L[𝕜] F} (hq : IsQuotientMap f)
    (hcompl : f.ker.ClosedComplemented) (hfg : FiniteDimensional 𝕜 f.ker) :
    IsFredholm f where
  isStrictMap := hq.isStrictMap
  isClosed_range := by
    rw [LinearMap.range_eq_top.2 hq.surjective]
    exact isClosed_univ
  finite_ker := hfg
  finite_coker := by
    rw [LinearMap.range_eq_top.2 hq.surjective]
    exact Submodule.CoFG.top
  closedComplemented_ker := hcompl

theorem _root_.Function.Surjective.isFredholm_iff (f : E →L[𝕜] F) (f_surj : Surjective f) :
    IsFredholm f ↔ IsQuotientMap f ∧ f.ker.ClosedComplemented ∧ FiniteDimensional 𝕜 f.ker := by
  refine ⟨fun hf ↦ ⟨?_, hf.closedComplemented_ker, hf.finite_ker⟩,
    fun ⟨h_quot, h_comp, h_fin⟩ ↦ h_quot.isFredholm h_comp h_fin⟩
  simpa [isQuotientMap_iff_isStrictMap_surjective, f_surj] using hf.isStrictMap

theorem _root_.Submodule.isFredholm_mkQL_iff {p : Submodule 𝕜 E} :
    IsFredholm p.mkQL ↔ p.ClosedComplemented ∧ FiniteDimensional 𝕜 p := by
  -- Technical note: we go through `Submodule.FG` because otherwise we have to rewrite types,
  -- which is just painful.
  rw [p.mkQ_surjective.isFredholm_iff p.mkQL, ← fg_iff_finiteDimensional,
    ← fg_iff_finiteDimensional]
  simp [isQuotientMap_mkQ]

theorem _root_.Submodule.isFredholm_mkQL {p : Submodule 𝕜 E} (hcompl : p.ClosedComplemented)
    [FiniteDimensional 𝕜 p] :
    IsFredholm p.mkQL :=
  isFredholm_mkQL_iff.mpr ⟨hcompl, inferInstance⟩

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 G]
  [T2Space E] [T2Space F] [T2Space G]

theorem isFredholm_congr {u u' : E →L[𝕜] F} (h : u.toLinearMap ≈ u'.toLinearMap) :
    IsFredholm u ↔ IsFredholm u' := by
  simp_rw [isFredholm_iff_exists_isQuasiInverse]
  exact exists_congr fun _ ↦ isQuasiInverse_congr (Setoid.refl _) (Setoid.symm h)

theorem IsFredholm.congr {u u' : E →L[𝕜] F} (hu : IsFredholm u)
    (h : u.toLinearMap ≈ u'.toLinearMap) :
    IsFredholm u' := (isFredholm_congr h).mp hu

theorem IsFredholm.add_hasFiniteRange {u v : E →L[𝕜] F} (hu : IsFredholm u)
    (hv : HasFiniteRange v.toLinearMap) :
    IsFredholm (u + v) :=
  hu.congr (by simpa [equiv_iff_hasFiniteRange] using hv.neg)

theorem IsFredholm.hasFiniteRange_add {u v : E →L[𝕜] F} (hu : IsFredholm u)
    (hv : HasFiniteRange v.toLinearMap) :
    IsFredholm (v + u) :=
  add_comm u v ▸ hu.add_hasFiniteRange hv

theorem IsFredholm.comp {f' : F →L[𝕜] G} {f : E →L[𝕜] F} (hf' : IsFredholm f')
    (hf : IsFredholm f) : IsFredholm (f' ∘L f) := by
  obtain ⟨g, hg⟩ := hf.exists_isQuasiInverse
  obtain ⟨g', hg'⟩ := hf'.exists_isQuasiInverse
  exact .of_isQuasiInverse (mod_cast hg.comp hg')

theorem IsFredholm.comp_iff_left {f : E →L[𝕜] F} {f' : F →L[𝕜] G} (hf : IsFredholm f) :
    IsFredholm (f' ∘L f) ↔ IsFredholm f' := by
  refine ⟨fun hcomp ↦ ?_, fun hf' ↦ hf'.comp hf⟩
  obtain ⟨g, hg⟩ := hf.exists_isQuasiInverse
  obtain ⟨w, hw⟩ := hcomp.exists_isQuasiInverse
  exact .of_isQuasiInverse (mod_cast hg.of_comp_left hw)

theorem IsFredholm.comp_iff_right {f : E →L[𝕜] F} {f' : F →L[𝕜] G} (hf' : IsFredholm f') :
    IsFredholm (f' ∘L f) ↔ IsFredholm f := by
  refine ⟨fun hcomp ↦ ?_, fun hf ↦ hf'.comp hf⟩
  obtain ⟨g', hg'⟩ := hf'.exists_isQuasiInverse
  obtain ⟨w, hw⟩ := hcomp.exists_isQuasiInverse
  exact .of_isQuasiInverse (mod_cast hg'.of_comp_right hw)

@[simp]
theorem isFredholm_comp_equiv {f : E ≃L[𝕜] F} {f' : F →L[𝕜] G} :
    IsFredholm (f' ∘L (f : E →L[𝕜] F)) ↔ IsFredholm f' :=
  f.isFredholm.comp_iff_left

@[simp]
theorem isFredholm_equiv_comp {f : E →L[𝕜] F} {f' : F ≃L[𝕜] G} :
    IsFredholm ((f' : F →L[𝕜] G) ∘L f) ↔ IsFredholm f :=
  f'.isFredholm.comp_iff_right

theorem isFredholm_restrict_iff {f : E →L[𝕜] F} {A : Submodule 𝕜 E} {B : Submodule 𝕜 F}
    (hA : IsClosed (A : Set E)) [A.CoFG] (hB : IsClosed (B : Set F)) [B.CoFG] (hf : MapsTo f A B) :
    IsFredholm (f.restrict hf) ↔ IsFredholm f := by
  rw [← (isFredholm_subtypeL hA).comp_iff_left, ← (isFredholm_subtypeL hB).comp_iff_right,
    subtypeL_comp_restrict hf, domRestrict]

alias ⟨IsFredholm.of_restrict, IsFredholm.restrict⟩ := isFredholm_restrict_iff

theorem isFredholm_domRestrict_iff {f : E →L[𝕜] F} {A : Submodule 𝕜 E}
    (hA : IsClosed (A : Set E)) [A.CoFG] :
    IsFredholm (f.domRestrict A) ↔ IsFredholm f := by
  rw [← (isFredholm_subtypeL hA).comp_iff_left, domRestrict]

alias ⟨IsFredholm.of_domRestrict, IsFredholm.domRestrict⟩ := isFredholm_domRestrict_iff

theorem isFredholm_codRestrict_iff {f : E →L[𝕜] F} {B : Submodule 𝕜 F}
    (hB : IsClosed (B : Set F)) [B.CoFG] (hf : ∀ x, f x ∈ B) :
    IsFredholm (f.codRestrict B hf) ↔ IsFredholm f := by
  rw [← (isFredholm_subtypeL hB).comp_iff_right, subtypeL_comp_codRestrict]

alias ⟨IsFredholm.of_codRestrict, IsFredholm.codRestrict⟩ := isFredholm_codRestrict_iff

end Constructions

end TVS
end ContinuousLinearMap

end
