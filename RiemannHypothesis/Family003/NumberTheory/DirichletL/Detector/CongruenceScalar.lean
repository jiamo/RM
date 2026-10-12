/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/CongruenceScalar.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.CongruenceScalar
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.Sextic
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dite_eq_right]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dite_eq_left hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end SevenEighths.ProbePrimePower
end

end RiemannHypothesis.Family003
