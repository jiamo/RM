/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/AmplificationEligibility.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationEligibility
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationEnergy
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationMask
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.InverseAmplificationMask

namespace RiemannHypothesis.Family003

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationEligibility
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def exclusionIdeal (R s : Ideal O) (h : O) : Ideal O := R*s*Ideal.span {h}

def eligible (R s : Ideal O) (h p : O) : Prop := ¬Ideal.span {p}∣exclusionIdeal R s h

theorem exclusionIdeal_ne_zero (R s : Ideal O) (h : O)
    (hR : R ≠ 0) (hs : s ≠ 0) (hh : h ≠ 0) : exclusionIdeal R s h ≠ 0 :=
  mul_ne_zero (mul_ne_zero hR hs) (Ideal.span_singleton_eq_bot.not.mpr hh)

theorem exclusionIdeal_norm (R s : Ideal O) (h : O) (Z B b M : ℝ) (hZ : 0 < Z)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (Ideal.absNorm (exclusionIdeal R s h):ℝ) ≤ Z^(B+b+M) := by
  simp only [exclusionIdeal,map_mul,Nat.cast_mul]
  calc
    _ ≤ (Z^B*Z^b)*Z^M := mul_le_mul
      (mul_le_mul hR hs (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ,← Real.rpow_add hZ]

theorem eligible_not_dvd_row (R s : Ideal O) (h p : O) (he : eligible R s h p) : ¬p∣h := by
  intro hd
  apply he
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)).trans
    (dvd_mul_left (Ideal.span {h}) (R*s))

theorem eligible_coprime_divisor (R s : Ideal O) (h p : O)
    (hp : Prime (Ideal.span {p})) (he : eligible R s h p) : IsCoprime s (Ideal.span {p}) := by
  apply (HeckeInverseAmplification.prime_coprime_iff ⟨Ideal.span {p},hp⟩ s).mpr
  intro hd
  exact he (hd.trans ((dvd_mul_left s R).mul_right (Ideal.span {h})))

theorem uniform_eligible_pool (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (h : O) (hh0 : h ≠ 0) (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (P.card:ℝ)/2 ≤ ((elementPool P).filter (eligible R s h)).card := by
  unfold eligible
  convert (preTransparency := .instances) eligible_element_card_half P hp hbad (exclusionIdeal R s h)
    (exclusionIdeal_ne_zero R s h hR0 hs0 hh0) Z ell (B+b+M) hZ hell hlower
    (exclusionIdeal_norm R s h Z B b M (zero_lt_one.trans hZ) hR hs hh) hsize

theorem actual_eligible_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows : Finset O) (hrows : ∀ h ∈ rows,h ≠ 0)
    (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hupper : ∀ Q ∈ P,(Ideal.absNorm Q:ℝ) ≤ Z^L)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (hrowNorm : ∀ h ∈ rows,(Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2) ≤
      (8/(P.card:ℝ))*
        (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows (elementPool P) (eligible R s)).image outputRow,
          ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c y‖^2)+
          ∑ x ∈ eligiblePairs rows (elementPool P) (eligible R s),errorEnergy S a ha c x.1 x.2) := by
  have hpos : (0:ℝ)<P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hb := gauss_energy_amplification S a ha c rows (elementPool P) (eligible R s) hrows
    (fun p hpP => (elementPool_data P hp hbad p hpP).1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.2)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.1)
    (fun h hh p hpP he => eligible_not_dvd_row R s h p he)
    ((P.card:ℝ)/2) (by positivity)
    (fun h hh => uniform_eligible_pool P hp hbad R s hR0 hs0 Z ell B b M hZ hell hlower hR hs hsize h (hrows h hh) (hrowNorm h hh))
    Z ell M L hZ hell
    (fun p hpP => hlower (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    (fun p hpP => hupper (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    hrowNorm
  convert (preTransparency := .instances) hb using 1 ; ring

end SevenEighths.CenteredMomentAmplificationEligibility

end

end RiemannHypothesis.Family003
