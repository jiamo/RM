/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialOverlapHeight.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapHeight
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.CommonMeasure
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.DescentHeight
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapHeight
open InverseInitialOverlapFourier InverseMoment JointLogSeparation

theorem twisted_polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(θ:ℝ),∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density (frequencyTwist g θ) xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ k t‖^2)≤C*E*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨C,hC,hboundMoment⟩ := frequencyTwist_fourier_moment J g
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro θ κ inst xj φ E hE hφ hbound
  have hint:=AnalyticBridge.schwartz_fourier_one_plus_integrable (frequencyTwist g θ) J
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density (frequencyTwist g θ) xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density (frequencyTwist g θ) xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density (frequencyTwist g θ) xj t‖ := by
    rw [show b t=density (frequencyTwist g θ) xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h,density_norm]
      using hint
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C*(1+‖θ‖)^(J+(volume:Measure ℝ).integrablePower) := by
    simpa only [hbnorm,h,density_norm]
      using hboundMoment θ
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_pow,←pow_mul,Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapHeight

end

end RiemannHypothesis.Family003
