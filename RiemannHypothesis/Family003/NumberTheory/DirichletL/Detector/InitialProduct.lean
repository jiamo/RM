/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/InitialProduct.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.InitialProduct
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.InitialSubseries
import Mathlib.MeasureTheory.Integral.Prod
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem initialHigh_counting_product_integrable {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ι×HeightSpace=>initialHighOnLines S D η mask σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ι).prod heightMeasure) := by
  have hb : Integrable (fun i : ι=>initialHighMajorant σ υ ξ (e i)) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (initialHighMajorant_nonneg _ _ _ _)] using
      (initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro i
    exact ((initialHighOnLines_continuous S D η mask σ υ ξ (e i)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e p.1) p.2) (norm_nonneg _)

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
