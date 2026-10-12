/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/ParametersProbeWindows.lean
  Original module: OAI.NumberTheory.DirichletL.ParametersProbeWindows
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Foundation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannHypothesis.Family003.Compat.NormNumIntToNat
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped ContDiff
namespace SevenEighths.Parameters

theorem exists_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w ⊆ Set.Ioo 1 2 ∧ (∀ x,0≤w x ∧ w x≤1) ∧
    w (3/2)=1 ∧ w≠0 ∧ (∀ x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W ⊆ Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,hs,hc,hw,hr,hval⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (E:=ℝ) (s:=Set.Ioo 1 2) (x:=3/2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
  let f : ℝ→ℂ := fun x=>(w x:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfc : HasCompactSupport f := hc.comp_left (show (fun x:ℝ=>(x:ℂ)) 0=0 by simp)
  let W : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hf
  have hne : w≠0 := by intro hz;have := congrFun hz (3/2);simp [hval] at this
  refine ⟨w,W,hw,hc,(subset_tsupport w).trans hs,fun x=>hr ⟨x,rfl⟩,hval,hne,
    fun _=>rfl,?_,?_,fun _=>rfl,?_⟩
  · intro hz
    apply hne
    funext x
    have h := congrArg (fun F : SchwartzMap ℝ ℂ => (F x).re) hz
    change w x=0 at h
    exact h
  · intro x hx
    have hwx : w x≠0 := by intro h;apply hx;change (w x:ℂ)=0;rw [h];rfl
    exact Set.Ioo_subset_Icc_self (hs (subset_tsupport w hwx))
  · intro x
    exact (hr ⟨x,rfl⟩).1
end SevenEighths.Parameters

end

end RiemannHypothesis.Family003
