/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/ContourShear.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.ContourShear
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.InitialFubini

namespace RiemannHypothesis.Family003

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceHeightShear_integral (F : HeightSpace→ℂ) :
    (∫p,F (sourceHeightShear p) ∂heightMeasure)=∫p,F p ∂heightMeasure :=
  sourceHeightShear_preserving.integral_comp' F

theorem source_contour_shear (F : ℂ→ℂ→ℂ→ℂ) (σ ξ υ : ℝ) :
    (∫p : HeightSpace,F (((σ:ℂ)+p.1.1*Complex.I)+((ξ:ℂ)+p.1.2*Complex.I)-1)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
    ∫p : HeightSpace,F (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  have hh := sourceHeightShear_integral (fun p : HeightSpace=>F
    (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I))
  convert (preTransparency := .instances) hh using 1
  congr 1
  funext p
  dsimp only [sourceHeightShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2 ; push_cast ; ring

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
