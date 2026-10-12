/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/CentralSlots.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.SelectedBounds
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RayPoolGood
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have he : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

theorem actual_central_unramified_error (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (4:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))+
      idealUnramifiedCorrection η u P x w z*star (idealRowHom u.val P.val)‖≤
        720*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact (rpow_le_half _ _ hQ (by rw [hz];norm_num)).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
    (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
      ((rpow_le_half _ _ hQ (by rw [hx,hz];linarith)).trans_lt (by norm_num))
  rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
  exact unramifiedSelected_central_error _ a e _ _ _ x w z hQ ha ha1 he he1
    (actualAPhase_norm_le_one η _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη)
    (row_phase_norm_one_of_not_dvd u P hs hn) hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end RiemannHypothesis.Family003
