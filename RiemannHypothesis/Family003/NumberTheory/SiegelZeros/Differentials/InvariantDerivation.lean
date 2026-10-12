/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Differentials/InvariantDerivation.lean
  Original module: OAI.NumberTheory.SiegelZeros.Differentials.InvariantDerivation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - proof repair: simp uses MvPolynomial.coeff_add (the host's MvPolynomial.coeff is not unfolded to AddMonoidAlgebra.coeff)
-/
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace RiemannHypothesis.Family003

namespace SiegelZeros


noncomputable section

open MvPolynomial
open scoped BigOperators

namespace WeightedTorusJets.W18

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

def invariantDerivation (v : σ → R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  ∑ i, (C (v i) * X i) • pderiv i

def eigenvalue (v : σ → R) (n : σ →₀ ℕ) : R :=
  ∑ i, v i * (n i : R)

theorem invariantDerivation_apply (v : σ → R) (p : MvPolynomial σ R) :
    invariantDerivation v p = ∑ i, C (v i) * (X i * pderiv i p) := by
  classical
  unfold invariantDerivation
  have h (s : Finset σ) :
      (∑ i ∈ s, (C (v i) * X i) • pderiv i) p =
        ∑ i ∈ s, C (v i) * (X i * pderiv i p) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Derivation.smul_apply, smul_eq_mul, mul_assoc, ih]
  simpa using h Finset.univ

theorem invariantDerivation_monomial (v : σ → R) (n : σ →₀ ℕ) (r : R) :
    invariantDerivation v (monomial n r) = monomial n (eigenvalue v n * r) := by
  classical
  rw [invariantDerivation_apply]
  simp only [X_mul_pderiv_monomial, C_mul']
  simp only [smul_monomial, nsmul_eq_mul, smul_eq_mul]
  rw [← map_sum]
  congr 1
  simp [eigenvalue, Finset.sum_mul, mul_assoc]

theorem invariantDerivation_monomial_smul (v : σ → R) (n : σ →₀ ℕ) (r : R) :
    invariantDerivation v (monomial n r) = eigenvalue v n • monomial n r := by
  rw [invariantDerivation_monomial, smul_monomial, smul_eq_mul]

theorem coeff_invariantDerivation (v : σ → R) (p : MvPolynomial σ R)
    (n : σ →₀ ℕ) :
    (invariantDerivation v p).coeff n = eigenvalue v n * p.coeff n := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [invariantDerivation_monomial]
    by_cases h : m = n
    · subst m; simp
    · simp [coeff_monomial, h]
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

theorem support_invariantDerivation_subset (v : σ → R) (p : MvPolynomial σ R) :
    (invariantDerivation v p).support ⊆ p.support := by
  intro n hn
  rw [mem_support_iff] at hn ⊢
  rw [coeff_invariantDerivation] at hn
  intro hz
  exact hn (by rw [hz, mul_zero])

def InBox (N : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ n ∈ p.support, ∀ i, n i < N

theorem inBox_invariantDerivation (v : σ → R) {N : ℕ} {p : MvPolynomial σ R}
    (hp : InBox N p) : InBox N (invariantDerivation v p) := by
  intro n hn i
  exact hp n (support_invariantDerivation_subset v p hn) i

end WeightedTorusJets.W18

end


end SiegelZeros

end RiemannHypothesis.Family003
