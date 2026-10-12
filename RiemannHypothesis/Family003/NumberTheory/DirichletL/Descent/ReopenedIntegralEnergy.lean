/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/ReopenedIntegralEnergy.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedIntegralEnergy
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - proof tweak: after convert, close residual instance-equality goals with 'with_reducible_and_instances rfl' (host instances are not reducibly defeq)
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.ReopenedCommonMeasure
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert (preTransparency := .instances) hi using 1
  all_goals try with_reducible_and_instances rfl
  funext ξ
  rw [varyingReopenedRow_integrand p hp hcop hg]
  simp only [A,Finset.mul_sum,columnLog]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem varying_separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) :=
    varying_separated_canonical_integrable p hp hcop hg pool Q (β I) n mark Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end
end SevenEighths.InverseMoment

end RiemannHypothesis.Family003
