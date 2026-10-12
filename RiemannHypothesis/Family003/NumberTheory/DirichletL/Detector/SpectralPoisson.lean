/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/SpectralPoisson.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.SpectralPoisson
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.PhysicalPoisson
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.PhysicalReopen
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dite_eq_left hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (supportedElement_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dite_eq_right hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
