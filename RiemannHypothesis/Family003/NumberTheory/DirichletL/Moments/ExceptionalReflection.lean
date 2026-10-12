/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/ExceptionalReflection.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.ExceptionalPair
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [ite_eq_left hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) *
        elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end SevenEighths.CenteredMomentExceptionalReflection

end

end RiemannHypothesis.Family003
