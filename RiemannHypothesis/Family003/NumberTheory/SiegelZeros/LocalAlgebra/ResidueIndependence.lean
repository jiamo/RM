/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/ResidueIndependence.lean
  Original module: OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueIndependence
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.SimpleRing.Basic

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W14

open scoped BigOperators

theorem integer_relation_eq_zero {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] {c : ι → V}
    (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    (h : ∑ i, (n i : ℚ) • c i = 0) : ∀ i, n i = 0 := by
  have hn := Fintype.linearIndependent_iff.mp hc (fun i => (n i : ℚ)) h
  intro i
  exact Int.cast_eq_zero.mp (hn i)

theorem complex_integer_relation_eq_zero {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    (h : ∑ i, c i * (n i : ℂ) = 0) : ∀ i, n i = 0 := by
  apply integer_relation_eq_zero hc n
  simpa [Rat.smul_def, mul_comm] using h

theorem residue_field_integer_relation_eq_zero {ι K : Type*} [Fintype ι]
    [Field K] {c : ι → ℂ} (hc : LinearIndependent ℚ c)
    (constants : ℂ →+* K) (n : ι → ℤ)
    (h : ∑ i, constants (c i) * (n i : K) = 0) : ∀ i, n i = 0 := by
  apply complex_integer_relation_eq_zero hc n
  apply constants.injective
  simpa using h

theorem orders_eq_zero_of_residue_equations {ι E : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (ord : E → ι → ℤ)
    (hres : ∀ e, ∑ i, c i * (ord e i : ℂ) = 0) :
    ∀ e i, ord e i = 0 := by
  intro e
  exact complex_integer_relation_eq_zero hc (ord e) (hres e)

theorem residue_ne_zero_of_order_ne_zero {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    {i : ι} (hi : n i ≠ 0) : ∑ j, c j * (n j : ℂ) ≠ 0 := by
  intro hz
  exact hi (complex_integer_relation_eq_zero hc n hz i)

theorem four_orders_eq_zero {E : Type*} {c : Fin 4 → ℂ}
    (hc : LinearIndependent ℚ c) (ord : E → Fin 4 → ℤ)
    (hres : ∀ e, ∑ i, c i * (ord e i : ℂ) = 0) :
    ∀ e i, ord e i = 0 :=
  orders_eq_zero_of_residue_equations hc ord hres

end SiegelZerosAwei.Workers.W14

end

end SiegelZeros

end RiemannHypothesis.Family003
