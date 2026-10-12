/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/MapIInfPrimesOver.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.MapIInfPrimesOver
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib
import RiemannHypothesis.Family003.External.PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Determinants.SqrtPairFrobeniusDirections

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section
namespace WeightedTorusJets

theorem map_eq_iInf_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsMaximal]
    (hunr : Algebra.IsUnramifiedIn S P) :
    P.map (algebraMap R S) = ⨅ Q : Ideal.primesOver P S, Q.1 := by
  apply le_antisymm
  · refine le_iInf fun Q ↦ ?_
    exact Ideal.map_le_iff_le_comap.mpr Q.2.2.over.le
  · intro x hx
    apply mem_map_of_forall_mem_primesOver P hunr
    intro Q hQ hover
    have hle : (⨅ Q : Ideal.primesOver P S, Q.1) ≤ Q :=
      iInf_le (fun Q : Ideal.primesOver P S ↦ Q.1) ⟨Q, hQ, hover⟩
    exact hle hx

end WeightedTorusJets

end

end SiegelZeros

end RiemannHypothesis.Family003
