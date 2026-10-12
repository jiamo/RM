/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/PairPhase.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.PairPhase
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.PhasePowers
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

theorem sexticPair_cube (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) :
    sexticPair p q ^ 3 = reciprocitySign p q := by
  have hr : idealRowHom q (Ideal.span {p}) =
      reciprocitySign p q * idealRowHom p (Ideal.span {q}) :=
    idealRowHom_prime_reciprocity p q hp hq hprimaryP hprimaryQ hsP hsQ
  have h6 := idealRowHom_sixth_mask p (Ideal.span {q}) hsQ
  rw [idealRowHom_argument_pow _ _ _ hsQ, ite_eq_left hcop.symm] at h6
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  calc
    sexticPair p q ^ 3 = reciprocitySign p q ^ 3 * idealRowHom p (Ideal.span {q}) ^ 6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = reciprocitySign p q := by rw [h6, mul_one, pow_succ, h2, one_mul]

theorem completed_pair_phase (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) (e f l k : ℕ) :
    sexticPair p q ^ ((e + 3 * l) * (f + 3 * k)) / sexticPair p q ^ (e * f) =
      reciprocitySign p q ^ (e * k + f * l + l * k) := by
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  have hr : reciprocitySign p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h2; norm_num at h2
  have hz : sexticPair p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h3; exact hr h3.symm
  have hexp : (e + 3 * l) * (f + 3 * k) = e * f + 3 * (e * k + f * l + 3 * l * k) := by ring
  rw [hexp, pow_add, pow_mul (sexticPair p q) 3 (e * k + f * l + 3 * l * k),
    h3, mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]
  have htail : e * k + f * l + 3 * l * k = (e * k + f * l + l * k) + 2 * (l * k) := by ring
  rw [htail, pow_add, pow_mul (reciprocitySign p q) 2 (l * k), h2, one_pow, mul_one]

end SevenEighths.ProbePhase
end

end RiemannHypothesis.Family003
