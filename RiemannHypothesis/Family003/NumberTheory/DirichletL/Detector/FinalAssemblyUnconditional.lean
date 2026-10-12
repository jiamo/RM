/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.CertifiedExistence
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import RiemannHypothesis.Family003.Compat.NormNumIntToNat
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssemblyUnconditional
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

theorem detector_certified_bands:DetectorCertifiedBands:=by
  intro hβ D _hfine F bΦ hbΦ
  have hp:=fixed_parameters D
  apply terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

theorem dirichlet_nonzero (q:ℕ)(hq:q≠0)(χ:DirichletCharacter ℂ q)(s:ℂ)
    (hs:(7/8:ℝ)<s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_certified detector_certified_bands q hq χ s hs hexc

theorem zeta_nonzero (s:ℂ)(hs:(7/8:ℝ)<s.re):riemannZeta s≠0:=
  zeta_of_certified detector_certified_bands s hs

end SevenEighths.ProbeFinalAssemblyUnconditional

end

end RiemannHypothesis.Family003
