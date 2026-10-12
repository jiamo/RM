/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramTruncation.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramTruncation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramSourceDivisors

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceTruncation (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑k∈E,originalCommonBlock S hS σ C k W hW Y Q hY U v

def sourceCanonicalSum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : SupportedIdeal→Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
    ∑k∈E C,canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))

theorem sourceTruncation_eq_canonical (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (E : Finset GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceTruncation S hS σ F E W hW Y Q hY U v=sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v := by
  unfold sourceTruncation sourceCanonicalSum
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  simp_rw [originalCommonBlock_eq_rectangle S hS hbad σ F C hC _ W hW Y Q hY hQ U v]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun D hD=>(Finset.mul_sum ..).symm)

def exceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (ExceptionalFrequency S hS C)
def nonexceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (fun k=>¬ExceptionalFrequency S hS C k)

lemma sourceCanonicalSum_split (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v=
      sourceCanonicalSum S hS σ F (exceptionalFrequencies S hS E) W hW Y Q hY U v+
      sourceCanonicalSum S hS σ F (nonexceptionalFrequencies S hS E) W hW Y Q hY U v := by
  unfold sourceCanonicalSum exceptionalFrequencies nonexceptionalFrequencies
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [←mul_add,Finset.sum_filter_add_sum_filter_not]

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
