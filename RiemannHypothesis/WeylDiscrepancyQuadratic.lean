/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDiscrepancy
import RiemannHypothesis.WeylBadlyApproximable

/-!
# A rate of convergence for the equidistribution of `α n²`

`RiemannHypothesis.WeylDiscrepancy` proves an Erdős–Turán type discrepancy inequality,
bounding `|#{n < N : Int.fract (x n) ∈ [a, b)}/N − (b − a)|` by `4/K` plus twice the average of
the exponential sums at the frequencies below `K⁴`, and applies it to the linear sequence `α n`.
This module carries out the corresponding application to the *quadratic* sequence `α n²`, using
the unconditional square-root cancellation
`RiemannHypothesis.WeylBadlyApproximable.norm_quadSum_le_of_badlyApproximable`.

## Main results

* `badlyApproximable_natMul` — if `x` is badly approximable with constant `c` then `m x` is badly
  approximable with constant `c/m`.
* `expSum_quadratic_eq` — the exponential sum of `α n²` at frequency `m` is the quadratic Weyl sum
  `quadSum (m α) N`.
* `norm_expSum_quadratic_le` — hence, for `2α` badly approximable with constant `c`,

      ‖∑_{n<N} e(m α n²)‖ ≤ √((16 m/c + 26) N (1 + log N)) .

* `abs_countIn_div_sub_le_quadratic` — **the rate**: for `K ≥ 2` and `N ≥ 1`,

      |#{n < N : Int.fract (α n²) ∈ [a, b)}/N − (b − a)|
          ≤ 4/K + 2 K⁴ √((16 K⁴/c + 26) N (1 + log N)) / N .

* `abs_countIn_div_sub_le_sqrt_two` — the concrete instance `α = √2/2`, where `c = 1/4`.

Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount

/-! ### Multiples of a badly approximable number -/

/-- If `x` is badly approximable with constant `c`, then `m x` is badly approximable with
constant `c/m`. -/
theorem badlyApproximable_natMul {x c : ℝ}
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |x - (a : ℝ) / q|)
    {m : ℕ} (hm : 1 ≤ m) :
    ∀ (a : ℤ) (q : ℕ), 0 < q → (c / m) / (q : ℝ) ^ 2 ≤ |(m : ℝ) * x - (a : ℝ) / q| := by
  intro a q hq
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h := hbad a (m * q) (Nat.mul_pos (by omega) hq)
  have hcast : ((m * q : ℕ) : ℝ) = (m : ℝ) * q := by push_cast; ring
  rw [hcast] at h
  have hprod : (m : ℝ) * (x - (a : ℝ) / ((m : ℝ) * q)) = (m : ℝ) * x - (a : ℝ) / q := by
    field_simp
  calc (c / m) / (q : ℝ) ^ 2 = (m : ℝ) * (c / ((m : ℝ) * q) ^ 2) := by field_simp
    _ ≤ (m : ℝ) * |x - (a : ℝ) / ((m : ℝ) * q)| := by
        exact mul_le_mul_of_nonneg_left h hm0.le
    _ = |(m : ℝ) * x - (a : ℝ) / q| := by rw [← abs_of_pos hm0, ← abs_mul, abs_of_pos hm0, hprod]

/-! ### The exponential sums of the quadratic sequence -/

/-- The exponential sum of `α n²` at frequency `m` is the quadratic Weyl sum of `m α`. -/
theorem expSum_quadratic_eq (α : ℝ) (m : ℤ) (N : ℕ) :
    expSum (fun n : ℕ => α * (n : ℝ) ^ 2) m N
      = WeylEquidistribution.quadSum ((m : ℝ) * α) N := by
  unfold expSum WeylEquidistribution.quadSum
  rw [sum_Ico_int_eq_sum_range]
  simp only [Int.toNat_natCast]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

/-- **Square-root cancellation at every frequency.**  If `2α` is badly approximable with
constant `c`, the exponential sums of `α n²` satisfy
`‖∑_{n<N} e(m α n²)‖ ≤ √((16 m/c + 26) N (1 + log N))`. -/
theorem norm_expSum_quadratic_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {m N : ℕ} (hm : 1 ≤ m) (hN : 0 < N) :
    ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖
      ≤ Real.sqrt ((16 * m / c + 26) * N * (1 + Real.log N)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hbad' := badlyApproximable_natMul hbad hm
  have hbad'' : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (c / m) / (q : ℝ) ^ 2 ≤ |2 * ((m : ℝ) * α) - (a : ℝ) / q| := by
    intro a q hq
    have h := hbad' a q hq
    rwa [show (m : ℝ) * (2 * α) = 2 * ((m : ℝ) * α) by ring] at h
  have h := WeylQuadratic.norm_quadSum_le_of_badlyApproximable (α := (m : ℝ) * α) (c := c / m)
    (by positivity) hbad'' hN
  rw [expSum_quadratic_eq]
  refine h.trans (le_of_eq ?_)
  congr 2
  field_simp

/-! ### The discrepancy bound -/

/-- **An explicit rate for the quadratic sequence.**  If `2α` is badly approximable with constant
`c`, the discrepancy of `α n²` on an interval is at most
`4/K + 2 K⁴ √((16 K⁴/c + 26) N (1 + log N))/N`. -/
theorem abs_countIn_div_sub_le_quadratic {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K) (hN : 0 < N) (ha : 1 / (K : ℝ) < a)
    (hb : b + 1 / (K : ℝ) < 1) (hab : a + 2 / (K : ℝ) ≤ b) :
    |(countIn (fun n : ℕ => α * (n : ℝ) ^ 2) a b N : ℝ) / N - (b - a)|
      ≤ 4 / K
        + 2 * (K : ℝ) ^ 4 * Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) / N := by
  have hK0 : 0 < K := by omega
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  set S : ℝ := Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hmain := abs_countIn_div_sub_le_pow (fun n : ℕ => α * (n : ℝ) ^ 2) hK hN ha hb hab
  have hterm : ∀ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
      ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N ≤ S / N := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmK : (m : ℝ) ≤ (K : ℝ) ^ 4 := by
      have : m ≤ K ^ 4 := le_trans hm.2 (Nat.sub_le _ _)
      exact_mod_cast this
    have h1 := norm_expSum_quadratic_le hc hbad hm.1 hN
    have h2 : Real.sqrt ((16 * (m : ℝ) / c + 26) * N * (1 + Real.log N)) ≤ S := by
      rw [hS]
      apply Real.sqrt_le_sqrt
      have h1log : (0 : ℝ) ≤ 1 + Real.log N := by linarith
      gcongr
    have := h1.trans h2
    gcongr
  have hcard : (Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card ≤ K ^ 4 := by
    rw [Nat.card_Icc]; omega
  have hsum : ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
      ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N ≤ (K : ℝ) ^ 4 * (S / N) := by
    calc ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
          ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N
        ≤ ∑ _m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), S / N := Finset.sum_le_sum hterm
      _ = ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) * (S / N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) ^ 4 * (S / N) := by
          have hc4 : ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) ≤ (K : ℝ) ^ 4 := by
            have h := (Nat.cast_le (α := ℝ)).2 hcard
            simpa using h
          have hpos : (0 : ℝ) ≤ S / N := by positivity
          exact mul_le_mul_of_nonneg_right hc4 hpos
  have hfin : 4 / (K : ℝ) + 2 * ((K : ℝ) ^ 4 * (S / N))
      = 4 / K + 2 * (K : ℝ) ^ 4 * S / N := by ring
  linarith [hmain, hsum, hfin]

/-- The concrete instance `α = √2/2`, for which `2α = √2` is badly approximable with `c = 1/4`. -/
theorem abs_countIn_div_sub_le_sqrt_two {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K) (hN : 0 < N)
    (ha : 1 / (K : ℝ) < a) (hb : b + 1 / (K : ℝ) < 1) (hab : a + 2 / (K : ℝ) ≤ b) :
    |(countIn (fun n : ℕ => Real.sqrt 2 / 2 * (n : ℝ) ^ 2) a b N : ℝ) / N - (b - a)|
      ≤ 4 / K
        + 2 * (K : ℝ) ^ 4 * Real.sqrt ((64 * (K : ℝ) ^ 4 + 26) * N * (1 + Real.log N)) / N := by
  have hbad : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ |2 * (Real.sqrt 2 / 2) - (a : ℝ) / q| := by
    intro a q hq
    have h := WeylQuadratic.badlyApproximable_sqrt_two a q hq
    rwa [show 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 by ring]
  have h := abs_countIn_div_sub_le_quadratic (α := Real.sqrt 2 / 2) (c := 1 / 4)
    (by norm_num) hbad hK hN ha hb hab
  have hcoef : 16 * (K : ℝ) ^ 4 / (1 / 4) + 26 = 64 * (K : ℝ) ^ 4 + 26 := by ring
  rwa [hcoef] at h

end WeylDiscrepancy

end RiemannHypothesis
