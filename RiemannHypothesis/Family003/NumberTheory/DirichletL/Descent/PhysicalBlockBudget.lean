/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/PhysicalBlockBudget.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.PhysicalBlockBudget
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.PhysicalExponents

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.InverseMoment

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0<Y) (hE : 0<E) (hV : 0<V) (hX : 0<X) (a : ℂ) :
    ‖(Y:ℂ)*a*((E*V*X:ℝ):ℂ)⁻¹‖ = ‖a‖*(Y/(E*V*X)) := by
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,abs_of_pos (by positivity : 0<E*V*X)]
  ring

theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
        (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z))) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hZpos : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9/2:ℝ)*(η*Real.log Z))=Z^((9/2:ℝ)*η) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V δ A B R j t g θ v η τ π ε
    (max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v) hclip
  nlinarith

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0≤C)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    C * Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Real.exp (6*(η*Real.log Z)) *
        ‖((Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ):ℝ):ℂ)*ray*
          ((Z^θ*Z^v*Z^(secondFormalColumn r A B t g v):ℝ):ℂ)⁻¹‖) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    C*‖ray‖*Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V δ A B R j t g θ v η τ π ε εmass hclip hεmass)
    (mul_nonneg hC (norm_nonneg ray))
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
