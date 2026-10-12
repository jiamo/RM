/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramPrefactor.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramPrefactor
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramWeightedFrequency
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramIdealSummation

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_prefactor (c d F P Y Q : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*c*(Y/(c*d))^2*(P/c)*min 1 ((F*c*(P/c)/(Y/(c*d)))^A)=
      (Q/Y)*P*(c^(-2:ℝ)*d^(-2:ℝ)*min 1 ((c*d/(Y/(F*P)))^A)) := by
  have he : F*c*(P/c)/(Y/(c*d))=c*d/(Y/(F*P)) := by field_simp
  rw [he,Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two,Real.rpow_two]
  field_simp

lemma exceptional_prefactor (c d F P Y Q ε : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*c*(Y/(c*d))^2*(F*c)^ε*(P/c)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(c^(-7/6+ε:ℝ)*d^(-2:ℝ)) := by
  rw [Real.mul_rpow hF.le hc.le,Real.div_rpow hP.le hc.le,
    show (-7/6+ε:ℝ)=ε+(-1)+(-(1/6)) by ring,
    Real.rpow_add hc,Real.rpow_add hc,Real.rpow_neg_one,
    Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two]
  field_simp

lemma supported_nonexceptional_prefactor (C D : SupportedIdeal) (F P Y Q : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((F*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)=
      (Q/Y)*P*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(F*P)))^A)) :=
  nonexceptional_prefactor _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY A

lemma supported_exceptional_prefactor (C D : SupportedIdeal) (F P Y Q ε : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*
      (F*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
  exceptional_prefactor _ _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
