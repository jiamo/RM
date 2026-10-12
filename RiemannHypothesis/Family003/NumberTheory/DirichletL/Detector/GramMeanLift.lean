/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramMeanLift.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramMeanLift
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramMean

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O

theorem joint_mean_of_local_factor (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : O→O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : O⧸Q*P^c) (y : O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=>F x.out y.out) d
  convert (preTransparency := .instances) hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
