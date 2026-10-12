/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialProfileBounds.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds
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

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

theorem clipped_norm (W:ℝ→ℂ)(c θ x:ℝ):‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,logPhase_norm,one_mul]

theorem clipped_bound (W:ℝ→ℂ)(B:ℝ)(hW:∀x,‖W x‖≤B)(c θ x:ℝ):
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

theorem clipped_support (W:ℝ→ℂ)(a b c cmax θ:ℝ)(ha:0<a)(hc:1≤c)(hcm:c≤cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

theorem clipped_support_upper (W:ℝ→ℂ)(a b c θ:ℝ)(ha:0<a)(hc:1≤c)
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

theorem childLogTest_eq_clipped (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=clippedSource W 1 θ:=by
  funext x
  simp only [childLogTest,clippedSource,mul_comm,mul_one]

theorem childLogTest_norm (W:ℝ→ℂ)(θ x:ℝ):‖childLogTest W θ x‖=‖W x‖:=by
  rw [childLogTest_eq_clipped,clipped_norm,one_mul]

end SevenEighths.InverseInitialProfileBounds

end

end RiemannHypothesis.Family003
