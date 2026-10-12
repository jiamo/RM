/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/SlotSums.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.SlotSums
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.SelectedBounds
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤B) → ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=>continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (hT P.val P.property).1
      (hT P.val P.property).2 x w z hx hw (by rw [hz];exact hr)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by have := (hT P.val P.property).2;change 1≤(P.val.val.absNorm:ℝ);linarith)
        (max_le (by linarith) (by norm_num))
    · simp only [show P.val.val=f P from rfl,ite_eq_right hp,le_refl]
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

end SevenEighths.ProbeHighRowFamily
end

end RiemannHypothesis.Family003
