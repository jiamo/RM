/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SourceDyadicShell.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SourceDyadicShell
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SourceLowerSupport
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondActiveDyadic

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization CenteredMomentSourceLowerSupport
local notation "O" => ActualEisensteinCubic.O

lemma residual_window_bounds (C I:Ideal O) (hC:C≠0) (L U:ℝ) (n:ℤ)
    (hL:L≤(Ideal.absNorm (C*I):ℝ)) (hU:(Ideal.absNorm (C*I):ℝ)≤U)
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    L/(Ideal.absNorm C:ℝ)≤dyadicScale n ∧
      dyadicScale n≤4*U/(Ideal.absNorm C:ℝ) := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=dyadicWeight_support n hw
  simp only [map_mul,Nat.cast_mul] at hL hU
  constructor
  · apply (div_le_iff₀ hc).mpr
    exact hL.trans (by nlinarith [hs.2])
  · apply (le_div_iff₀ hc).mpr
    nlinarith [hs.1]

lemma raw_window_lower (C I:Ideal O) (hC:C≠0) (a H:ℝ) (ha:0<a) (n:ℤ)
    (hL:a*H≤(Ideal.absNorm (C*I):ℝ))
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale n/a := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=(dyadicWeight_support n hw).2.le
  simp only [map_mul,Nat.cast_mul] at hL
  apply (div_le_div_iff₀ hc ha).mpr
  nlinarith

end SevenEighths.CenteredMomentSourceDyadicShell

end

end RiemannHypothesis.Family003
