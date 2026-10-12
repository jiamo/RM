/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/DeletionReciprocal.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.DeletionReciprocal
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.DeletionBounds
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDeletionReciprocal
open HeckeFamily HeckeFiniteDeletion HeckeReciprocal HeckeDeletionBounds

theorem reciprocal_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    reciprocal χ s = reciprocal ψ s * (factors χ.modulus ψ s)⁻¹ := by
  by_cases hχ : χ.residue = 1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [reciprocal, ite_eq_left hχ, ite_eq_left hψ]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    simp only [reciprocal, ite_eq_right hχ, ite_eq_right hψ]
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_inv]

theorem exists_primitive_reciprocal_reduction (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character,
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
        (∀ I : Ideal O, idealCoeff χ I =
          if IsCoprime I χ.modulus then idealCoeff ψ I else 0) ∧
        ∀ s : ℂ, σ ≤ s.re →
          ‖reciprocal χ s‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε * ‖reciprocal ψ s‖ := by
  obtain ⟨C, hC, hb⟩ := factors_radical_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro χ
  obtain ⟨ψ, _, hp, hn, hm⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, hn, hm, ?_⟩
  intro s hs
  rw [reciprocal_eq_of_mask χ ψ hm (hσ.trans_le hs), norm_mul]
  have hf := hb χ.modulus ψ s hs
  have hfb : ‖(factors χ.modulus ψ s)⁻¹‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ s)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfb (norm_nonneg (reciprocal ψ s))

end SevenEighths.HeckeDeletionReciprocal

end

end RiemannHypothesis.Family003
