/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailGeometry.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailGeometry
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem live_column_norm_bound (W : ℝ→ℂ) (b C v n X : ℝ)
    (hs : Function.support W⊆Set.Iic b) (hX : 0<X)
    (hw : W (C*v*n/X)≠0) : C*v*n≤b*X := by
  exact (div_le_iff₀ hX).mp (hs hw)

theorem actual_radial_center_lower
    (Z D m B θ H η C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hd : 0<d) (hv : 0<v) (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hL : 0<L) (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Z^(radialCenter m H θ D B-3*η) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hc : 0<C := (Real.rpow_pos_of_pos hz B).trans_le hC
  have hh : 0≤hnorm := (Real.rpow_pos_of_pos hz H).le.trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ L
    (by positivity) hc hd hv hn₁ hn₂ hL h₁ h₂
  calc
    _ = Z^m*(Z^B)^2*Z^H/(Z^(θ+η)*(Z^(D+η))^2) := by
      simp only [pow_two]
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      unfold radialCenter
      ring
    _ ≤ Z^m*C^2*hnorm/(d*L^2) := by
      gcongr
    _ = (Z^m*C^2/(d*L^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem high_radial_block_tail_gate
    (Z D m B θ H η τ C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L)
    (hhigh : 4*η+τ≤radialCenter m H θ D B) :
    Z^τ ≤ (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
    (actual_radial_center_lower Z D m B θ H η C d v n₁ n₂ L hnorm
      hZ hd hv hn₁ hn₂ hL hC hdiv hcol hfreq h₁ h₂)

end SevenEighths.InverseInitialHighFrequencyTail

end

end RiemannHypothesis.Family003
