/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/PrincipalNormalizer.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.PrincipalResidue
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrincipalSignalComparison
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.RadialMellin
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrincipalNormalizer
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
local notation "O" => HeckeFamily.O

theorem sourceResidueConstant_positive (M : Ideal O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0) :
    ∃c : ℝ,0<c ∧ sourceResidueConstant W0 W1 M=(c:ℂ) := by
  obtain ⟨hp0,hi0⟩ := ProbeRadialMellin.radial_mellin_one_sixth_pos W0 a0 b0 ha0 hW0 hreal0 hpos0 hne0
  obtain ⟨hp1,hi1⟩ := ProbeRadialMellin.positive_source_mellin W1 a1 b1 ha1 hW1 hreal1 hpos1 hne1 1
  obtain ⟨R,hR,hres⟩ := HeckePrincipalResidue.fixed_principal_residue_positive M
  have hr : fixedPrincipalResidue M=(R:ℂ) := by
    rw [fixedPrincipalResidue,←HeckeOrigin.poleRemoved_one]
    exact hres
  have he0 : mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)=
      ((mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi0)
  have he1 : mellin W1 1=((mellin W1 1).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi1)
  refine ⟨(mellin W1 1).re*(mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)).re*R^2/6,?_,?_⟩
  · norm_num only [Complex.ofReal_one] at hp1
    positivity
  · unfold sourceResidueConstant
    rw [he0,he1,hr]
    push_cast
    rfl

theorem sourceResidueConstant_ne_zero (M : Ideal O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0) :
    sourceResidueConstant W0 W1 M≠0 := by
  obtain ⟨c,hc,he⟩ := sourceResidueConstant_positive M W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hreal0 hreal1 hpos0 hpos1 hne0 hne1
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hc.ne'

theorem signed_source_normalizer_ne_zero {κ ι : Type*} [DecidableEq κ]
    (M : Ideal O) [NeZero M] (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0)
    (S : Finset κ) (T : κ→Finset ι) (w : κ→ι→ℝ) (Z ℓ : ℝ) (hZ : 0<Z)
    (hm : ∀j∈S,0<slotMass T w j) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ℓ (slotMass T w):ℂ)≠0 :=
  mul_ne_zero (sourceResidueConstant_ne_zero M W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hreal0 hreal1 hpos0 hpos1 hne0 hne1) (source_normalizer_ne_zero S T w hZ hm)

end SevenEighths.ProbePrincipalNormalizer
end

end RiemannHypothesis.Family003
