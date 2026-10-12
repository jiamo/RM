/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/PolynomialBridge.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialBridge
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemma absent at the host pin)
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Trunc
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Structure.RectangleGenerators
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SiegelZeros

noncomputable section
namespace Result.Workers.W57
variable (K : Type*) [CommRing K]

def polynomialJetMap (n : ℕ) : Polynomial K →+* Jet K n :=
  (jetProjection K n).comp Polynomial.coeToPowerSeries.ringHom

theorem polynomialJetMap_surjective (n : ℕ) :
    Function.Surjective (polynomialJetMap K n) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨PowerSeries.trunc n f, ?_⟩
  change Ideal.Quotient.mk (truncationIdeal K n)
    ((PowerSeries.trunc n f : Polynomial K) : PowerSeries K) =
      Ideal.Quotient.mk (truncationIdeal K n) f
  rw [Ideal.Quotient.eq, truncationIdeal, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hi, sub_self]

theorem polynomialJetMap_ker (n : ℕ) :
    RingHom.ker (polynomialJetMap K n) =
      Ideal.span {(Polynomial.X : Polynomial K)^n} := by
  ext p
  change polynomialJetMap K n p = 0 ↔ _
  change Ideal.Quotient.mk (truncationIdeal K n) (p : PowerSeries K) = 0 ↔ _
  rw [truncation_eq_zero_iff, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

def polynomialJetEquiv (n : ℕ) :
    (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K)^n}) ≃+* Jet K n :=
  (Ideal.quotEquivOfEq (polynomialJetMap_ker K n).symm).trans
    ((polynomialJetMap K n).quotientKerEquivOfSurjective (polynomialJetMap_surjective K n))

end Result.Workers.W57

end

end SiegelZeros

end RiemannHypothesis.Family003
