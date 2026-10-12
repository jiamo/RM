/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/DvrFractions.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.DvrFractions
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W14

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]

theorem fraction_mem_range_of_addVal_le {x y : R} (hy : y ≠ 0)
    (hv : IsDiscreteValuationRing.addVal R y ≤ IsDiscreteValuationRing.addVal R x) :
    algebraMap R K x / algebraMap R K y ∈ (algebraMap R K).range := by
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hv
  refine ⟨r, ?_⟩
  have hy0 : algebraMap R K y ≠ 0 := by
    intro h
    exact hy ((IsFractionRing.injective R K) (by simpa using h))
  rw [hr, map_mul, mul_div_cancel_left₀ _ hy0]

theorem fraction_and_inverse_mem_range_of_addVal_eq {x y : R}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : IsDiscreteValuationRing.addVal R x = IsDiscreteValuationRing.addVal R y) :
    algebraMap R K x / algebraMap R K y ∈ (algebraMap R K).range ∧
    (algebraMap R K x / algebraMap R K y)⁻¹ ∈ (algebraMap R K).range := by
  constructor
  · exact fraction_mem_range_of_addVal_le hy hv.ge
  · rw [inv_div]
    exact fraction_mem_range_of_addVal_le hx hv.le

end SiegelZerosAwei.Workers.W14

end

end SiegelZeros

end RiemannHypothesis.Family003
