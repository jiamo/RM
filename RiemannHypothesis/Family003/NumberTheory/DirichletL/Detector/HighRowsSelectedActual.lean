/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedActual.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsRegion
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    have hu : IsUnit (Ideal.Quotient.mk eta.modulus p) := eta.residue.apply_ne_zero_iff.mp h
    obtain ⟨u,hu⟩ := hu
    change ‖eta.residue (Ideal.Quotient.mk eta.modulus p)‖=1
    rw [←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

def actualUnramifiedSelected (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end RiemannHypothesis.Family003
