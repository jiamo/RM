/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/AmplificationMask.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationMask
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports Compat.MathlibBackports (Mathlib lemmas absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationRectangle
import RiemannHypothesis.Family003.Compat.MathlibBackports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationMask
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem whole_product_divisibility (p : O) (s Q I J : Ideal O)
    (hcop : IsCoprime s (Ideal.span {p})) (k j : ℕ) (hj : j ≤ k) :
    s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) ↔ s∣Q*I*J := by
  have he : Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) =
      (Ideal.span {p})^k*(Q*I*J) := by
    calc
      _ = ((Ideal.span {p})^j*(Ideal.span {p})^(k-j))*(Q*I*J) := by ring
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  exact (hcop.pow_right (n := k)).dvd_mul_left_iff

theorem masked_centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (s : Ideal O) (hcop : IsCoprime s (Ideal.span {p}))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T:ℂ)⁻¹ *
      (idealWeight c χ R t (Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J))*
        CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) *
      (if s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) then (1:ℂ) else 0) =
      (idealWeight c χ R t ((Ideal.span {p})^k)/primeRoot p k)*
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k):ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J)*
            CenteredMomentRectangle.idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j)) I J)*
          (if s∣Q*I*J then (1:ℂ) else 0)) := by
  simp only [whole_product_divisibility p s Q I J hcop k j hj]
  rw [centered_coefficient_prime_extract p hp c χ R t W₁ W₂ X₁ X₂ Y₁ Y₂ T hT Q I J k j hj]
  ring

end SevenEighths.CenteredMomentAmplificationMask

end

end RiemannHypothesis.Family003
