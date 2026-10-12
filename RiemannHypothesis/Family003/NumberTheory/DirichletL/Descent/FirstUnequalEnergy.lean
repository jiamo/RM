/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/FirstUnequalEnergy.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.FirstUnequalEnergy
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.FirstFamilyEnergy
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_family_integral_of_two_energies (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    (Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      (Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply hh.trans_eq
    rw [Real.sqrt_mul hB₁,Real.sqrt_mul hB₂]
    calc
      _=(Real.sqrt B₁*Real.sqrt B₂)*(Real.sqrt (tripleHeight J z.1*coordinateHeight J z.2))^2:=by ring
      _= _:=by rw [Real.sq_sqrt];unfold tripleHeight coordinateHeight;positivity
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),(Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _
end
end SevenEighths.InverseMoment

end RiemannHypothesis.Family003
