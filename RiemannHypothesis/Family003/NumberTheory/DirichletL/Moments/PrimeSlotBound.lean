/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/PrimeSlotBound.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlotBound
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.PrimeSlot
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.PrimeHeight
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentPrimeSlotBound
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentRayNonprincipal
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

include hH
theorem actual_slot_all_height_squared (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hWs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧ ∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H b P) (slotProfile W P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  have hχreal:(χ.modulus.absNorm:ℝ)≤Z^Lmod:=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  rw [normalizedSlot_norm_sq M H η χ m A z hrow W b P σ t (zero_lt_one.trans_le hP)]
  exact hbound Z P hZ hP hPcap χ hχreal
    (all_ray_twists_nonprincipal M H hH η χ Q m A z hrow hQ hex) σ t hσ hσhi

end SevenEighths.CenteredMomentPrimeSlotBound

end

end RiemannHypothesis.Family003
