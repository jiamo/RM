/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/DetectorRowSpecialization.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowSpecialization
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.RowClosure
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.Dyadic

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end SevenEighths.HeckeDetectorRowSpecialization

end

end RiemannHypothesis.Family003
