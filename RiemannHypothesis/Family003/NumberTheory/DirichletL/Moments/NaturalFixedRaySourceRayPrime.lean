/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceRayPrime.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end RiemannHypothesis.Family003
