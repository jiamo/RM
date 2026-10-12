/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighRowsCentralStrict.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrict
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma squarefree_base_boundary_norm (j : ℕ) (hj : j≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j (by omega)
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  rw [he,ite_eq_right (by omega)]
  split_ifs
  · rw [norm_mul,norm_mul,norm_inv,
      Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
      inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
    norm_num
  · simp only [mul_zero,norm_zero]
    positivity

include hc in
lemma squarefree_base_strict_norm (j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j hj
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le
      ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (show 1≤Ideal.absNorm (Ideal.span {p}) by omega)
  have hfac : ‖if 1<j then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else if j=1 ∧ True then -(1:ℂ) else 0‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    split_ifs
    · rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    · simpa using hQ1
    · simp
  rw [he,norm_mul,norm_mul,norm_inv,
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
    inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
  calc
    _≤Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ)*(Ideal.absNorm (Ideal.span {p}):ℝ) :=
      mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
    _=(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
      rw [mul_comm]
      convert (preTransparency := .instances) ProbeEuler.pow_mul_sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) hQ 1 using 1 <;> norm_num
end SevenEighths.ProbePrimePower
end

end RiemannHypothesis.Family003
