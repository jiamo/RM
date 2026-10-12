/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramMobiusPool.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramMobiusPool
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramIdealDilation
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.MobiusRegroup

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

lemma poolDivisor_val (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    (poolDivisor G D).val=D := by simp [poolDivisor,hD]

lemma finite_pair_eq_tsum (F G : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ)
    (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,f I J)=∑'I : SupportedIdeal,∑'J : SupportedIdeal,f I J := by
  have hinner (I : SupportedIdeal) : (∑J∈G,f I J)=∑'J : SupportedIdeal,f I J :=
    (tsum_eq_sum (fun J hJ=>hf I J (Or.inr hJ))).symm
  simp_rw [hinner]
  symm
  apply tsum_eq_sum
  intro I hI
  simp only [hf I _ (Or.inl hI),tsum_zero]

theorem finite_pair_mobius_dilation (F G : Finset SupportedIdeal)
    (f : SupportedIdeal→SupportedIdeal→ℂ) (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,if IsCoprime I.val J.val then f I J else 0)=
      ∑D∈divisorPool G Subtype.val,(moebius D:ℂ)*
        ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
          f (supportedIdealProduct (poolDivisor G D) I) (supportedIdealProduct (poolDivisor G D) J) := by
  rw [finite_pair_mobius F G Subtype.val Subtype.val (fun J _=>J.property.1) f]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hd := poolDivisor_val G D hD
  rw [finite_pair_eq_tsum F G (fun I J=>if D∣I.val ∧ D∣J.val then f I J else 0) (by
    intro I J h
    simp only [hf I J h,ite_self])]
  convert (preTransparency := .instances) supported_divisor_pair_tsum (poolDivisor G D) f using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
