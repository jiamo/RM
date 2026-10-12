/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/SecondCutoffScale.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.PhysicalExponents

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z delta theta g s Hc eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(s+4*eta)) :
    correlatedSecondRadius p d G E L (Z^(Hc+12*eta+tau)) (Z^tau) ≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G ≤ Z^(theta-g+2*eta) := by
    calc
      _ ≤ Z^(theta+eta)/Z^(g-eta) := div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ ≤ Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*
        Z^tau/Z^(Hc+12*eta+tau) := by
      unfold correlatedSecondRadius
      gcongr
    _ = _ := by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem second_correlated_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z M r ell V delta A B j t g theta eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    correlatedSecondRadius p d G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau) ≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb := second_correlated_radius_bound p hp d G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hd hE hG hL
  convert (preTransparency := .instances) hb using 1; congr 1
  unfold childM decrease firstPhysicalHeight
  ring

end
end SevenEighths.InverseMoment

end RiemannHypothesis.Family003
