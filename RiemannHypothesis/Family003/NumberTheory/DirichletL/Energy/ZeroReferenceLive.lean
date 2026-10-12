/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Energy/ZeroReferenceLive.lean
  Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLive
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.ZeroReferencePower
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Energy.LiveClippingDefect
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLive
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePower CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLive

end

end RiemannHypothesis.Family003
