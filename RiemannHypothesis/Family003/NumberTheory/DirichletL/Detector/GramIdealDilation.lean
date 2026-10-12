/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramIdealDilation.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramGcd

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}

def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩

def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨idealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (idealQuotient_mul (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_mul I.property

lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryGenerator (supportedIdealProduct D J).val=primaryGenerator D.val*primaryGenerator J.val :=
  primaryGenerator_mul _ _

lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _

theorem supported_divisor_tsum (D : SupportedIdeal) (f : SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,if D.val∣I.val then f I else 0)=
      ∑'J : SupportedIdeal,f (supportedIdealProduct D J) := by
  change (∑'I : SupportedIdeal,({I : SupportedIdeal | D.val∣I.val}.indicator f) I)=_
  rw [←tsum_subtype (s:={I : SupportedIdeal | D.val∣I.val}) (f:=f)]
  exact (supportedDilationEquiv D).tsum_eq (fun I : DivisibleSupported D=>f I.val) |>.symm

theorem supported_divisor_pair_tsum (D : SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
        f (supportedIdealProduct D I) (supportedIdealProduct D J) := by
  have hinner (I : SupportedIdeal) : (∑'J : SupportedIdeal,if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      if D.val∣I.val then ∑'J : SupportedIdeal,f I (supportedIdealProduct D J) else 0 := by
    by_cases hI : D.val∣I.val
    · simp only [hI,true_and,ite_true]
      exact supported_divisor_tsum D (f I)
    · simp [hI]
  simp_rw [hinner]
  exact supported_divisor_tsum D (fun I=>∑'J : SupportedIdeal,f I (supportedIdealProduct D J))

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
