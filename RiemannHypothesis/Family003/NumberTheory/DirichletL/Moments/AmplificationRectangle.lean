/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/AmplificationRectangle.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationRectangle
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationShortening

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationRectangle
open CenteredMomentRectangle CenteredMomentExtraction CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem centralRoot_extract (p : O) (hp : p ≠ 0) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T : ℂ)⁻¹ = (primeRoot p k)⁻¹ *
      (Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ := by
  have hN : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hroot : Real.sqrt T = Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) *
      Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) := by
    rw [← Real.sqrt_mul (pow_nonneg hN.le k)]
    congr 1
    field_simp
  rw [hroot,Complex.ofReal_mul,mul_inv,primeRoot]

theorem centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T : ℂ)⁻¹ *
      (idealWeight c χ R t (Q * ((Ideal.span {p})^j*I) * ((Ideal.span {p})^(k-j)*J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) =
      (idealWeight c χ R t ((Ideal.span {p})^k) / primeRoot p k) *
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J) *
            idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) I J)) := by
  rw [extracted_rectangle_coefficient,centralRoot_extract p hp k T hT]
  have hprod : Q*(Ideal.span {p})^j*(Ideal.span {p})^(k-j) = Q*(Ideal.span {p})^k := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hj]
  rw [hprod]
  simp only [idealWeight_mul,map_pow,Nat.cast_pow]
  ring

theorem centered_product_prime_extract (p : O) (k j : ℕ) (hj : j ≤ k)
    (X₁ X₂ Y₁ Y₂ T : ℝ) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k ∧
    (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k := by
  simp only [div_mul_div_comm,← pow_add,Nat.add_sub_of_le hj,hX,hY,and_self]

end SevenEighths.CenteredMomentAmplificationRectangle

end

end RiemannHypothesis.Family003
