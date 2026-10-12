/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/NonfloorDictionary.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.CentralClassPartition

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O)
variable (H : Subgroup (O ⧸ M)ˣ)

lemma source_physical_amplitude {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) (j : Fin N) :
    physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z := by
  unfold physical
  rw [physical_slot_scale ell Z d hZ hd j]

lemma source_rowMean_eq {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) mesh (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) u=
      weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z)) := by
  unfold rowMean
  simp_rw [physical_slot_scale ell Z d hZ hd,source_physical_amplitude M H ell W Z d b z hZ hd]
  rw [show (2*a-1)/2=a-1/2 by ring]

lemma source_amplitude_class_mean {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (hm : 0<mesh)
    (rows : Finset FreeRow) (bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh)
    (u : FreeRow)
    (hu : u∈amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) bin) :
    weightedMean Finset.univ (fun j=>ell j/d)
      (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z))=
      classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin := by
  rw [←source_rowMean_eq M H ell W Z d b a mesh z hZ hd u]
  exact rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d) _ bin u hu

end SevenEighths.ProbeHighRowFamily

end

end RiemannHypothesis.Family003
