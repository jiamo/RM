/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/DetectorCoefficientTransfer.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ) : ℝ := if reverse then -freq else freq

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end RiemannHypothesis.Family003
