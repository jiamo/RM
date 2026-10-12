/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerWeights.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPhysicalMeasure
namespace SevenEighths.InverseInitialEnergyCallerWeights
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (j C d h : Eis) (V : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V‖ ≤ ‖Ψ (∏ i∈V,p i)‖ := by
  rw [initialColumn_eq_secondPre]
  exact secondPreColumn_norm_le p hp hcop hg hc Ψ (j*C) 1 1 d h V

omit hp hcop hg in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem initialBeta_norm_le_one (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (G : Finset ι) : ‖initialBeta p Ψ j G‖≤1 := by
  have hm : ‖rowCoprimeMask (fun i=>Ideal.span {p i}) G j‖≤1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have h := (mul_le_of_le_one_left (norm_nonneg _) (hΨ (∏ i∈G,p i))).trans hm
  simp only [initialBeta,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _),norm_mul]
  nlinarith [mul_nonneg (norm_nonneg (Ψ (∏ i∈G,p i)))
    (norm_nonneg (rowCoprimeMask (fun i=>Ideal.span {p i}) G j))]

theorem outerCoefficient_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (x : Point ι) (ρ : SecondRayIndex) :
    ‖outerCoefficient p hp hcop hg Ψ j x ρ‖ ≤ ‖secondRayCoefficient ρ‖ := by
  have hβ := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hV : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  have hL := (initialColumn_norm_le p hp hcop hg hc (secondRayMinus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) x.frequency x.overlap).trans
      ((secondRayMinus_norm_le Ψ ρ _).trans (hΨ _))
  have hR := (initialColumn_norm_le p hp hcop hg hc (secondRayPlus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) (-x.frequency) x.overlap).trans
      ((secondRayPlus_norm_le Ψ ρ _).trans (hΨ _))
  simp only [outerCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*1*1 := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialEnergyCallerWeights

end

end RiemannHypothesis.Family003
