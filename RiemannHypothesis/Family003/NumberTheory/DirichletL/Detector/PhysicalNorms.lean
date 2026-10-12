/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/PhysicalNorms.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.MellinScaling
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SpectralWeights

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : ActualEisensteinCubic.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : ActualEisensteinCubic.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  have hb : (Real.sqrt B:ℂ)^2=(B:ℂ) := by exact_mod_cast Real.sq_sqrt hB.le
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
