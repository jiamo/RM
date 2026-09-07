/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Vaughan's identity

Vaughan's identity is the elementary decomposition of the von Mangoldt function that turns a
sum `∑_{n ≤ N} Λ(n) f(n)` into a *linear* (type I) sum and two *bilinear* (type II) sums, whose
variables are constrained to ranges one controls.  It is the combinatorial input of the
Bombieri–Vinogradov theorem and of Vinogradov's estimates for exponential sums over primes; the
analytic inputs (the large sieve, Siegel–Walfisz) are separate.

Everything here happens in the Dirichlet convolution ring `ArithmeticFunction ℝ`.  Writing
`f_{≤U}` for the truncation of `f` to `n ≤ U` and `f_{>U}` for its complement, the identity is

`Λ = Λ_{≤U} + log ∗ μ_{≤V} − Λ_{≤U} ∗ ζ ∗ μ_{≤V} + Λ_{>U} ∗ ζ ∗ μ_{>V}`,

an identity of arithmetic functions, proved from `Λ ∗ ζ = log` and `ζ ∗ μ = 1` alone.  At an
argument `n > U` the first term vanishes, which is the form in which the identity is used:

`Λ(n) = ∑_{d ∣ n, d ≤ V} μ(d) log(n/d)`
`     − ∑_{b c m = n, b ≤ U, c ≤ V} Λ(b) μ(c)`
`     + ∑_{b c m = n, b > U, c > V} Λ(b) μ(c)`.

## Main results

* `RiemannHypothesis.Vaughan.truncLE`, `truncGT` — the two truncations, and
  `truncLE_add_truncGT` — they add up to the original function.
* `RiemannHypothesis.Vaughan.vaughan_identity` — **Vaughan's identity**, as an identity of
  arithmetic functions.
* `RiemannHypothesis.Vaughan.vonMangoldt_eq_of_lt` — the identity evaluated at `n > U`.
* `RiemannHypothesis.Vaughan.typeI_apply` — the first term as the divisor sum
  `∑_{d ∣ n, d ≤ V} μ(d) log(n/d)`.
* `RiemannHypothesis.Vaughan.typeII_apply`, `typeIII_apply` — the two bilinear terms as sums over
  the triples `b c m = n` with the stated constraints, which is what makes them bilinear.

## Scope

This is the exact identity only.  No estimate is proved for either bilinear sum, so nothing about
primes in progressions or about `ζ` follows from this file by itself.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RiemannHypothesis

namespace Vaughan

/-- The truncation of an arithmetic function to the arguments `n ≤ U`. -/
def truncLE (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The truncation of an arithmetic function to the arguments `n > U`. -/
def truncGT (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] theorem truncLE_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncLE f U n = if n ≤ U then f n else 0 := rfl

@[simp] theorem truncGT_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncGT f U n = if U < n then f n else 0 := rfl

/-- The two truncations add up to the original function. -/
theorem truncLE_add_truncGT (f : ArithmeticFunction ℝ) (U : ℕ) :
    truncLE f U + truncGT f U = f := by
  ext n
  simp only [ArithmeticFunction.add_apply, truncLE_apply, truncGT_apply]
  by_cases h : n ≤ U
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- The truncation vanishes above its threshold. -/
theorem truncLE_apply_of_lt {f : ArithmeticFunction ℝ} {U n : ℕ} (h : U < n) :
    truncLE f U n = 0 := by simp [not_le.mpr h]

/-! ## The identity -/

/-- **Vaughan's identity.**  For all thresholds `U, V`,
`Λ = Λ_{≤U} + log ∗ μ_{≤V} − Λ_{≤U} ∗ ζ ∗ μ_{≤V} + Λ_{>U} ∗ ζ ∗ μ_{>V}`. -/
theorem vaughan_identity (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ)
      = truncLE Λ U
        + ArithmeticFunction.log * truncLE (μ : ArithmeticFunction ℝ) V
        - truncLE Λ U * (ζ : ArithmeticFunction ℝ) * truncLE (μ : ArithmeticFunction ℝ) V
        + truncGT Λ U * (ζ : ArithmeticFunction ℝ) * truncGT (μ : ArithmeticFunction ℝ) V := by
  have hzm : ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) = 1 :=
    coe_zeta_mul_coe_moebius
  have hsplitmu : (μ : ArithmeticFunction ℝ)
      = truncLE (μ : ArithmeticFunction ℝ) V + truncGT (μ : ArithmeticFunction ℝ) V :=
    (truncLE_add_truncGT _ _).symm
  have hsplitL : (Λ : ArithmeticFunction ℝ) = truncLE Λ U + truncGT Λ U :=
    (truncLE_add_truncGT _ _).symm
  have hlog : truncLE Λ U * (ζ : ArithmeticFunction ℝ)
      + truncGT Λ U * (ζ : ArithmeticFunction ℝ) = ArithmeticFunction.log := by
    rw [← add_mul, ← hsplitL, vonMangoldt_mul_zeta]
  have key : truncGT Λ U
      = (truncGT Λ U * (ζ : ArithmeticFunction ℝ)) * truncLE (μ : ArithmeticFunction ℝ) V
        + (truncGT Λ U * (ζ : ArithmeticFunction ℝ)) * truncGT (μ : ArithmeticFunction ℝ) V := by
    rw [← mul_add, ← hsplitmu, mul_assoc, hzm, mul_one]
  have hGT : truncGT Λ U * (ζ : ArithmeticFunction ℝ)
      = ArithmeticFunction.log - truncLE Λ U * (ζ : ArithmeticFunction ℝ) := by
    rw [← hlog]; ring
  calc (Λ : ArithmeticFunction ℝ) = truncLE Λ U + truncGT Λ U := hsplitL
    _ = truncLE Λ U
        + ((truncGT Λ U * (ζ : ArithmeticFunction ℝ)) * truncLE (μ : ArithmeticFunction ℝ) V
          + (truncGT Λ U * (ζ : ArithmeticFunction ℝ)) *
            truncGT (μ : ArithmeticFunction ℝ) V) := by rw [← key]
    _ = _ := by rw [hGT]; ring

/-- **Vaughan's identity at an argument above the first threshold.**  For `n > U` the linear
term `Λ_{≤U}` drops out. -/
theorem vonMangoldt_eq_of_lt {U V n : ℕ} (hn : U < n) :
    (Λ : ArithmeticFunction ℝ) n
      = (ArithmeticFunction.log * truncLE (μ : ArithmeticFunction ℝ) V) n
        - (truncLE Λ U * (ζ : ArithmeticFunction ℝ) * truncLE (μ : ArithmeticFunction ℝ) V) n
        + (truncGT Λ U * (ζ : ArithmeticFunction ℝ) * truncGT (μ : ArithmeticFunction ℝ) V) n := by
  have hsub : ∀ f g : ArithmeticFunction ℝ, (f - g) n = f n - g n := fun _ _ => rfl
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_identity U V)
  simp only [ArithmeticFunction.add_apply, hsub] at h
  rw [h, truncLE_apply_of_lt hn]
  ring

/-! ## The three terms as explicit sums -/

/-- The **type I** term is the divisor sum `∑_{d ∣ n, d ≤ V} μ(d) log(n/d)`. -/
theorem typeI_apply (V n : ℕ) :
    (ArithmeticFunction.log * truncLE (μ : ArithmeticFunction ℝ) V) n
      = ∑ x ∈ n.divisorsAntidiagonal, Real.log x.1 * (if x.2 ≤ V then (μ x.2 : ℝ) else 0) := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [ArithmeticFunction.log_apply, truncLE_apply]

/-- The **type II** term: a sum over the triples `b c m = n` with `b ≤ U` and `c ≤ V`, of
`Λ(b) μ(c)`. -/
theorem typeII_apply (U V n : ℕ) :
    (truncLE Λ U * (ζ : ArithmeticFunction ℝ) * truncLE (μ : ArithmeticFunction ℝ) V) n
      = ∑ x ∈ n.divisorsAntidiagonal,
          (∑ y ∈ x.1.divisorsAntidiagonal,
            (if y.1 ≤ U then Λ y.1 else 0) * (if y.2 = 0 then 0 else 1)) *
              (if x.2 ≤ V then (μ x.2 : ℝ) else 0) := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y.2 = 0
  · simp [hy]
  · simp [hy, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]

/-- The **type III** term: a sum over the triples `b c m = n` with `b > U` and `c > V`, of
`Λ(b) μ(c)`.  Both variables are restricted to long ranges, which is exactly what makes the
term amenable to a bilinear (Cauchy–Schwarz) estimate. -/
theorem typeIII_apply (U V n : ℕ) :
    (truncGT Λ U * (ζ : ArithmeticFunction ℝ) * truncGT (μ : ArithmeticFunction ℝ) V) n
      = ∑ x ∈ n.divisorsAntidiagonal,
          (∑ y ∈ x.1.divisorsAntidiagonal,
            (if U < y.1 then Λ y.1 else 0) * (if y.2 = 0 then 0 else 1)) *
              (if V < x.2 then (μ x.2 : ℝ) else 0) := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y.2 = 0
  · simp [hy]
  · simp [hy, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]

/-! ## The identity summed against a weight -/

/-- Vaughan's identity summed against an arbitrary weight `f` over `U < n ≤ N`: the sum of
`Λ(n) f(n)` splits into one linear and two bilinear sums.  This is the form in which the
identity enters the Bombieri–Vinogradov theorem and Vinogradov's estimates for exponential sums
over the primes. -/
theorem sum_vonMangoldt_eq (f : ℕ → ℝ) (U V N : ℕ) :
    ∑ n ∈ Finset.Ioc U N, (Λ : ArithmeticFunction ℝ) n * f n
      = (∑ n ∈ Finset.Ioc U N,
            (ArithmeticFunction.log * truncLE (μ : ArithmeticFunction ℝ) V) n * f n)
        - (∑ n ∈ Finset.Ioc U N,
            (truncLE Λ U * (ζ : ArithmeticFunction ℝ) *
              truncLE (μ : ArithmeticFunction ℝ) V) n * f n)
        + ∑ n ∈ Finset.Ioc U N,
            (truncGT Λ U * (ζ : ArithmeticFunction ℝ) *
              truncGT (μ : ArithmeticFunction ℝ) V) n * f n := by
  have hterm : ∀ n ∈ Finset.Ioc U N, (Λ : ArithmeticFunction ℝ) n * f n
      = (ArithmeticFunction.log * truncLE (μ : ArithmeticFunction ℝ) V) n * f n
        - (truncLE Λ U * (ζ : ArithmeticFunction ℝ) *
            truncLE (μ : ArithmeticFunction ℝ) V) n * f n
        + (truncGT Λ U * (ζ : ArithmeticFunction ℝ) *
            truncGT (μ : ArithmeticFunction ℝ) V) n * f n := by
    intro n hn
    rw [vonMangoldt_eq_of_lt (V := V) (Finset.mem_Ioc.mp hn).1]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end Vaughan

end RiemannHypothesis
