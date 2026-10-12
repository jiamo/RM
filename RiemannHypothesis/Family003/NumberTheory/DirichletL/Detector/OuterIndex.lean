/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/OuterIndex.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.OuterIndex
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RawIndexGrouping

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

lemma sourceOuter_tsum (S : Finset (Ideal O)) (f : {I : Ideal O // Supported I}→ℂ) :
    (∑'K : {I : Ideal O // Supported I},if ∀P∈S,¬P∣K.val then f K else 0)=
      ∑'K : SourceOuter S,f ⟨K.val,K.property.1⟩ := by
  have hs := tsum_subtype {K : {I : Ideal O // Supported I} | ∀P∈S,¬P∣K.val} f
  have he := (sourceOuterEquiv S).tsum_eq (fun K=>f K.val)
  calc
    _ = ∑' K : {I : Ideal O // Supported I},
        Set.indicator {K | ∀ P ∈ S, ¬P ∣ K.val} f K := by
      apply tsum_congr
      intro K
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> rfl
    _ = _ := hs.symm.trans he.symm

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
