/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/EntireLogarithm.lean
  Original module: OAI.NumberTheory.SiegelZeros.EntireFunctions.EntireLogarithm
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

theorem exists_entire_logarithm (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hlog : Differentiable ℂ (logDeriv f) := by
    intro z
    exact ((hf.analyticAt z).deriv.differentiableAt).div (hf z) (hne z)
  obtain ⟨g, hg⟩ := hlog.isExactOn_univ
  have hg' : ∀ z, HasDerivAt g (logDeriv f z) z := fun z => hg z (Set.mem_univ z)
  have hgd : Differentiable ℂ g := fun z => (hg' z).differentiableAt
  have he : Differentiable ℂ (fun z => Complex.exp (g z)) := hgd.cexp
  have heq : Set.EqOn (logDeriv f) (logDeriv (fun z => Complex.exp (g z))) Set.univ := by
    intro z _
    have hd := (hg' z).cexp
    rw [logDeriv_apply (fun z => Complex.exp (g z)), hd.deriv]
    simp [Complex.exp_ne_zero]
  obtain ⟨c, hc, hfc⟩ :=
    (logDeriv_eqOn_iff hf.differentiableOn he.differentiableOn
      isOpen_univ isPreconnected_univ (fun z _ => Complex.exp_ne_zero (g z))
      (fun z _ => hne z)).mp heq
  refine ⟨fun z => Complex.log c + g z, hgd.const_add _, ?_⟩
  intro z
  rw [Complex.exp_add, Complex.exp_log hc]
  simpa only [Pi.smul_apply, smul_eq_mul] using hfc (Set.mem_univ z)

end SiegelZerosAwei.W03

end

end SiegelZeros

end RiemannHypothesis.Family003
