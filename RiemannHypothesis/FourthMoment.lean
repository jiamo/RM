/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MeanSquare

/-!
# The fourth moment of `ζ` on a line of absolute convergence

The identity `ζ(s)² = ∑ d(n) n^(-s)`, where `d(n)` is the number of divisors of `n`, exhibits
`ζ²` as an absolutely convergent Dirichlet series on every line `re s = σ > 1`.  Feeding this
into the mean value theorem of `RiemannHypothesis.MeanSquare` gives the fourth moment

`(1/T) ∫₀ᵀ |ζ(σ + i t)|⁴ dt → ∑ d(n)² n^(-2σ)`  as  `T → ∞`.

## Main results

* `lseries_divisorCount` : `∑ d(n) n^(-s) = ζ(s)²` for `re s > 1`.
* `fourthMomentAvg_tendsto_tsum_divisorCount` : the fourth moment of `ζ` for `σ > 1`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology ArithmeticFunction

namespace RiemannHypothesis

/-- The number of divisors of `n` (so `divisorCount 0 = 0`). -/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

@[simp] lemma divisorCount_zero : divisorCount 0 = 0 := by simp [divisorCount]

/-- The Dirichlet convolution of the constant-one arithmetic function with itself is the
divisor counting function. -/
lemma convolution_zeta_zeta_eq_divisorCount (n : ℕ) :
    LSeries.convolution (fun m => (ArithmeticFunction.zeta m : ℂ))
      (fun m => (ArithmeticFunction.zeta m : ℂ)) n = (divisorCount n : ℂ) := by
  rw [LSeries.convolution_def]
  simp only [divisorCount]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.zeta a : ℂ) * (ArithmeticFunction.zeta b : ℂ))]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) ?_]
  · simp
  · intro i hi
    rw [Nat.mem_divisors] at hi
    have h1 : i ≠ 0 := by rintro rfl; simp at hi
    have h2 : n / i ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨h1, Nat.le_of_dvd (Nat.pos_of_ne_zero hi.2) hi.1⟩
    simp [ArithmeticFunction.zeta_apply, h1, h2]

/-- The Dirichlet series of the divisor counting function converges absolutely for
`re s > 1`. -/
lemma lseriesSummable_divisorCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorCount n : ℂ)) s :=
  (LSeriesSummable_congr s fun {n} _ => convolution_zeta_zeta_eq_divisorCount n).mp
    ((ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs).convolution
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs))

/-- `∑ d(n) n^(-s) = ζ(s)²` for `re s > 1`. -/
theorem lseries_divisorCount {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (divisorCount n : ℂ)) s = riemannZeta s ^ 2 := by
  have hz := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have h := LSeries_convolution' hz hz
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← sq] at h
  rw [← h]
  exact LSeries_congr (fun {n} _ => (convolution_zeta_zeta_eq_divisorCount n).symm) s

/-- Absolute convergence, in shifted form, of a Dirichlet series with nonnegative real
coefficients that is `LSeriesSummable` at a real point. -/
lemma summable_shift_rpow_of_lseriesSummable {a : ℕ → ℝ} {σ : ℝ}
    (h : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ)) :
    Summable fun n : ℕ => a (n + 1) * ((n : ℝ) + 1) ^ (-σ) := by
  have hshift : Summable fun n : ℕ => LSeries.term (fun n => (a n : ℂ)) (σ : ℂ) (n + 1) :=
    (summable_nat_add_iff 1).mpr h
  refine Complex.summable_ofReal.mp (hshift.congr fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n + 1 : ℕ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [LSeries.term_def, if_neg (Nat.succ_ne_zero n), hcast, ← Complex.ofReal_cpow hn.le,
    ← Complex.ofReal_div, Real.rpow_neg hn.le, div_eq_mul_inv]

lemma summable_dirichletWeight_divisorCount {σ : ℝ} (hσ : 1 < σ) :
    Summable (dirichletWeight (fun n => ((divisorCount (n + 1) : ℕ) : ℂ)) σ) := by
  have hre : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have h := summable_shift_rpow_of_lseriesSummable (a := fun n => (divisorCount n : ℝ))
    ((lseriesSummable_divisorCount hre).congr fun n => by push_cast; ring)
  refine h.congr fun n => ?_
  rw [dirichletWeight, Complex.norm_natCast]

/-- On the line of real part `σ > 1`, the Dirichlet series of the divisor counting function
is `ζ²`. -/
lemma dirichletLineSum_divisorCount {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    dirichletLineSum (fun n => ((divisorCount (n + 1) : ℕ) : ℂ)) σ t
      = riemannZeta (linePoint σ t) ^ 2 := by
  have hre : 1 < (linePoint σ t).re := by simpa using hσ
  have h := lseries_eq_dirichletLineSum (fun n => (divisorCount n : ℂ)) σ t
    (lseriesSummable_divisorCount hre)
  rw [lseries_divisorCount hre] at h
  exact h.symm

/-- **The fourth moment of `ζ` on a line of absolute convergence.**  For `σ > 1`,
`(1/T) ∫₀ᵀ |ζ(σ + i t)|⁴ dt → ∑_{n ≥ 1} d(n)² n^(-2σ)`. -/
theorem fourthMomentAvg_tendsto_tsum_divisorCount {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 4) / T) atTop
      (𝓝 (∑' n : ℕ, ((divisorCount (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  have h := meanSquareAvg_tendsto_tsum_of_summable (summable_dirichletWeight_divisorCount hσ)
  simp_rw [dirichletLineSum_divisorCount hσ, norm_pow] at h
  have hpow : ∀ t : ℝ, (‖riemannZeta (linePoint σ t)‖ ^ 2) ^ 2
      = ‖riemannZeta (linePoint σ t)‖ ^ 4 := fun t => by ring
  have hcoeff : ∀ n : ℕ,
      dirichletWeight (fun n => ((divisorCount (n + 1) : ℕ) : ℂ)) σ n ^ 2
        = ((divisorCount (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [dirichletWeight_sq, Complex.norm_natCast]
  simp_rw [hpow, hcoeff] at h
  exact h

end RiemannHypothesis
