/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Discrepancy
import RiemannHypothesis.DiscrepancyCriterion
import RiemannHypothesis.WeylPortmanteau

/-!
# Koksma's inequality

`RiemannHypothesis.Discrepancy` defines the discrepancy

    D_N(x) = sup { |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| : 0 ≤ a ≤ b ≤ 1 }

and bounds it for concrete sequences.  This module proves what makes the discrepancy the right
measure of equidistribution: **Koksma's inequality**, the statement that the error committed by
replacing an integral over `[0, 1]` by the average of the integrand along the first `N` terms of
the sequence is at most the total variation of the integrand times the discrepancy,

    |(1/N) ∑_{n < N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ (f 1 − f 0) · D_N(x)   (`koksma_monotone`)

for a nondecreasing `f` — no continuity assumed, jumps allowed — and, for an `L`-Lipschitz `f`,

    |(1/N) ∑_{n < N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ 3 L · D_N(x)   (`koksma_lipschitz`).

The inequality is quantitative — no limit is taken — and it converts every discrepancy bound of
the repository into an error bound for numerical integration along the sequence.

## Main results

* `koksma_monotone` — Koksma's inequality for a nondecreasing integrand.
* `koksma_sub_monotone` — the same for a difference of two nondecreasing functions, with the sum
  of the two rises in place of `f 1 - f 0`.
* `koksma_lipschitz` — Koksma's inequality for a Lipschitz integrand, with constant `3 L`.
* `tendsto_average_of_tendsto_discrepancy` — a sequence whose discrepancy tends to `0` integrates
  every monotone function correctly in the limit.
* `tendsto_average_quadratic` — the concrete instance `xₙ = α n²`, `α` irrational.

## Proof

Cut `[0, 1)` into `K` cells `[j/K, (j+1)/K)` and let `c_j` be the number of `n < N` whose
fractional part falls in the `j`-th cell.  Monotonicity brackets the average between the two
*step averages* built from the values of `f` at the left and the right endpoints of the cells
(`sum_stepLeft_le_sum_fract`, `sum_fract_le_sum_stepRight`), and it brackets `∫₀¹ f` between the
corresponding left and right Riemann sums (`riemannSum_le_integral_le`), which themselves differ
by `(f 1 − f 0)/K` (`riemannSum_right_sub_left`).

What remains is the *cell deviation sum* `∑_j w_j (c_j/N − 1/K)`, with the weight `w_j` the value
of `f` at either endpoint of the `j`-th cell.  Summation by parts (`sum_mul_sub_succ`,
`sum_mul_sub_succ'`) rewrites it as a sum of consecutive differences of `f` against the
deviations `S_j` of the *tail* intervals `[j/K, 1)`, each of which is at most `D_N` in absolute
value; the differences are nonnegative and telescope to at most `f 1 − f 0`
(`abs_sum_cellDev_le`, `abs_sum_cellDev_right_le`).  The boundary terms of the summation by parts
vanish because `S_0 = S_K = 0`: every fractional part lies in `[0, 1)`, and `[1, 1)` is empty.

Combining, the error is at most `(f 1 − f 0) D_N + (f 1 − f 0)/K` for every `K ≥ 1`, hence at
most `(f 1 − f 0) D_N`.
-/
noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount WeylPortmanteau

/-! ### Summation by parts -/

/-- **Summation by parts.**  The boundary terms are `a 0 * S 0` and `a K * S K`. -/
theorem sum_mul_sub_succ (a S : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, a j * (S j - S (j + 1))
      = a 0 * S 0 - a K * S K + ∑ j ∈ Finset.range K, (a (j + 1) - a j) * S (j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih,
        Finset.sum_range_succ (f := fun j => (a (j + 1) - a j) * S (j + 1))]
      ring

/-- **Summation by parts**, with the weight taken at the right endpoint.  The boundary terms are
the same, and every index used is at most `K`. -/
theorem sum_mul_sub_succ' (a S : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, a (j + 1) * (S j - S (j + 1))
      = a 0 * S 0 - a K * S K + ∑ j ∈ Finset.range K, (a (j + 1) - a j) * S j := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih,
        Finset.sum_range_succ (f := fun j => (a (j + 1) - a j) * S j)]
      ring

/-! ### The three error terms -/

/-- The deviation of the tail interval `[j/K, 1)` is bounded by the discrepancy. -/
theorem abs_tailDev_le_discrepancy (x : ℕ → ℝ) {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) (N : ℕ) :
    |(countIn x ((j : ℝ) / K) 1 N : ℝ) / N - (1 - (j : ℝ) / K)| ≤ discrepancy x N := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have h1 : (0 : ℝ) ≤ (j : ℝ) / K := by positivity
  have h2 : (j : ℝ) / K ≤ 1 := by
    rw [div_le_one hK0]
    exact_mod_cast hj
  exact le_discrepancy x h1 h2 le_rfl N

/-- **The lower step sum.**  Replacing each `f(⟨xₙ⟩)` by the value of `f` at the left endpoint of
its cell decreases the sum, because `f` is nondecreasing. -/
theorem sum_stepLeft_le_sum_fract {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) {K : ℕ}
    (hK : 0 < K) (x : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range K, (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)
      ≤ ∑ n ∈ Finset.range N, f (Int.fract (x n)) := by
  classical
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hmaps : ∀ n ∈ Finset.range N, cell K (x n) ∈ Finset.range K :=
    fun n _ => Finset.mem_range.2 (cell_lt hK _)
  have h1 : (∑ n ∈ Finset.range N, f (Int.fract (x n)))
      = ∑ j ∈ Finset.range K,
          ∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f (Int.fract (x n)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [h1]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j < K := Finset.mem_range.1 hj
  have hjmem : ((j : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hK0]
    exact_mod_cast hjK.le
  rw [countIn_cell_eq_card hK, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hlo, _⟩ := (cell_eq_iff hK).1 (Finset.mem_filter.1 hn).2
  exact hmono hjmem ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ hlo

/-- **The upper step sum.**  Replacing each `f(⟨xₙ⟩)` by the value of `f` at the right endpoint of
its cell increases the sum. -/
theorem sum_fract_le_sum_stepRight {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) {K : ℕ}
    (hK : 0 < K) (x : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (Int.fract (x n))
      ≤ ∑ j ∈ Finset.range K,
          (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f (((j : ℝ) + 1) / K) := by
  classical
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hmaps : ∀ n ∈ Finset.range N, cell K (x n) ∈ Finset.range K :=
    fun n _ => Finset.mem_range.2 (cell_lt hK _)
  have h1 : (∑ n ∈ Finset.range N, f (Int.fract (x n)))
      = ∑ j ∈ Finset.range K,
          ∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f (Int.fract (x n)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [h1]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j < K := Finset.mem_range.1 hj
  have hjmem : (((j : ℝ) + 1) / K) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hK0]
    exact_mod_cast hjK
  rw [countIn_cell_eq_card hK, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨_, hhi⟩ := (cell_eq_iff hK).1 (Finset.mem_filter.1 hn).2
  exact hmono ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ hjmem hhi.le

/-- **The cell deviation sum is controlled by the discrepancy.**  This is the summation by parts
step: the weights `f((j+1)/K) − f(j/K)` are nonnegative and telescope to `f 1 − f 0`. -/
theorem abs_sum_cellDev_le {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) (x : ℕ → ℝ)
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |∑ j ∈ Finset.range K,
        f ((j : ℝ) / K) * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)|
      ≤ (f 1 - f 0) * discrepancy x N := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set a : ℕ → ℝ := fun j => f ((j : ℝ) / K) with ha
  set S : ℕ → ℝ := fun j => (countIn x ((j : ℝ) / K) 1 N : ℝ) / N - (1 - (j : ℝ) / K) with hS
  -- grid points lie in `[0, 1]`
  have hgrid : ∀ j : ℕ, j ≤ K → ((j : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hK0]
    exact_mod_cast hj
  -- the deviations telescope
  have hdiff : ∀ j ∈ Finset.range K,
      ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K) = S j - S (j + 1) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hle : (j : ℝ) / K ≤ ((j : ℝ) + 1) / K := by
      gcongr
      linarith
    have hle1 : ((j : ℝ) + 1) / K ≤ 1 := by
      rw [div_le_one hK0]
      exact_mod_cast hjK
    have hadd := countIn_add_countIn x hle hle1 N
    have hcast : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
    have hadd' : (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ)
        = (countIn x ((j : ℝ) / K) 1 N : ℝ) - (countIn x (((j : ℝ) + 1) / K) 1 N : ℝ) := by
      rw [← hadd]
      push_cast
      ring
    simp only [hS, hcast]
    rw [hadd']
    field_simp
    ring
  have hS0 : S 0 = 0 := by
    simp only [hS, Nat.cast_zero, zero_div, countIn_zero_one]
    field_simp
    norm_num
  have hSK : S K = 0 := by
    have hKK : (K : ℝ) / K = 1 := div_self (ne_of_gt hK0)
    simp only [hS, hKK, countIn_self]
    norm_num
  have hmonoStep : ∀ j ∈ Finset.range K, 0 ≤ a (j + 1) - a j := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have h1 : ((j : ℝ) / K) ≤ ((j + 1 : ℕ) : ℝ) / K := by
      have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
      gcongr
    have := hmono (hgrid j hjK.le) (hgrid (j + 1) hjK) h1
    simpa [ha] using sub_nonneg.2 this
  have hstep : ∀ j ∈ Finset.range K,
      |(a (j + 1) - a j) * S (j + 1)| ≤ (a (j + 1) - a j) * discrepancy x N := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    rw [abs_mul, abs_of_nonneg (hmonoStep j hj)]
    exact mul_le_mul_of_nonneg_left (abs_tailDev_le_discrepancy x hK hjK N)
      (hmonoStep j hj)
  have hrewrite : ∑ j ∈ Finset.range K,
      f ((j : ℝ) / K) * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)
      = ∑ j ∈ Finset.range K, a j * (S j - S (j + 1)) :=
    Finset.sum_congr rfl fun j hj => by rw [hdiff j hj]
  rw [hrewrite, sum_mul_sub_succ a S K, hS0, hSK]
  simp only [mul_zero, sub_zero, zero_add]
  calc |∑ j ∈ Finset.range K, (a (j + 1) - a j) * S (j + 1)|
      ≤ ∑ j ∈ Finset.range K, |(a (j + 1) - a j) * S (j + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, (a (j + 1) - a j) * discrepancy x N :=
        Finset.sum_le_sum hstep
    _ = (a K - a 0) * discrepancy x N := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ = (f 1 - f 0) * discrepancy x N := by
        have hKK : (K : ℝ) / K = 1 := div_self (ne_of_gt hK0)
        simp [ha, hKK]

/-- **The cell deviation sum with the weights at the right endpoints** is controlled by the
discrepancy in the same way. -/
theorem abs_sum_cellDev_right_le {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) (x : ℕ → ℝ)
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |∑ j ∈ Finset.range K,
        f (((j : ℝ) + 1) / K)
          * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)|
      ≤ (f 1 - f 0) * discrepancy x N := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set a : ℕ → ℝ := fun j => f ((j : ℝ) / K) with ha
  set S : ℕ → ℝ := fun j => (countIn x ((j : ℝ) / K) 1 N : ℝ) / N - (1 - (j : ℝ) / K) with hS
  have hgrid : ∀ j : ℕ, j ≤ K → ((j : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hK0]
    exact_mod_cast hj
  have hdiff : ∀ j ∈ Finset.range K,
      ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K) = S j - S (j + 1) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hle : (j : ℝ) / K ≤ ((j : ℝ) + 1) / K := by
      gcongr
      linarith
    have hle1 : ((j : ℝ) + 1) / K ≤ 1 := by
      rw [div_le_one hK0]
      exact_mod_cast hjK
    have hadd := countIn_add_countIn x hle hle1 N
    have hcast : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
    have hadd' : (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ)
        = (countIn x ((j : ℝ) / K) 1 N : ℝ) - (countIn x (((j : ℝ) + 1) / K) 1 N : ℝ) := by
      rw [← hadd]
      push_cast
      ring
    simp only [hS, hcast]
    rw [hadd']
    field_simp
    ring
  have hS0 : S 0 = 0 := by
    simp only [hS, Nat.cast_zero, zero_div, countIn_zero_one]
    field_simp
    norm_num
  have hSK : S K = 0 := by
    have hKK : (K : ℝ) / K = 1 := div_self (ne_of_gt hK0)
    simp only [hS, hKK, countIn_self]
    norm_num
  have hmonoStep : ∀ j ∈ Finset.range K, 0 ≤ a (j + 1) - a j := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have h1 : ((j : ℝ) / K) ≤ ((j + 1 : ℕ) : ℝ) / K := by
      have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
      gcongr
    have := hmono (hgrid j hjK.le) (hgrid (j + 1) hjK) h1
    simpa [ha] using sub_nonneg.2 this
  have hstep : ∀ j ∈ Finset.range K,
      |(a (j + 1) - a j) * S j| ≤ (a (j + 1) - a j) * discrepancy x N := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    rw [abs_mul, abs_of_nonneg (hmonoStep j hj)]
    exact mul_le_mul_of_nonneg_left (abs_tailDev_le_discrepancy x hK hjK.le N) (hmonoStep j hj)
  have hrewrite : ∑ j ∈ Finset.range K,
      f (((j : ℝ) + 1) / K)
        * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)
      = ∑ j ∈ Finset.range K, a (j + 1) * (S j - S (j + 1)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hcast : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
    rw [hdiff j hj]
    simp only [ha, hcast]
  rw [hrewrite, sum_mul_sub_succ' a S K, hS0, hSK]
  simp only [mul_zero, sub_zero, zero_add]
  calc |∑ j ∈ Finset.range K, (a (j + 1) - a j) * S j|
      ≤ ∑ j ∈ Finset.range K, |(a (j + 1) - a j) * S j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, (a (j + 1) - a j) * discrepancy x N := Finset.sum_le_sum hstep
    _ = (a K - a 0) * discrepancy x N := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ = (f 1 - f 0) * discrepancy x N := by
        have hKK : (K : ℝ) / K = 1 := div_self (ne_of_gt hK0)
        simp [ha, hKK]

/-- **The Riemann sums bracket the integral.**  For a monotone `f` the left Riemann sum on the
grid of step `1/K` is at most `∫₀¹ f`, which is at most the right Riemann sum. -/
theorem riemannSum_le_integral_le {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) {K : ℕ}
    (hK : 0 < K) :
    (∑ j ∈ Finset.range K, f ((j : ℝ) / K) / K) ≤ (∫ t in (0 : ℝ)..1, f t) ∧
      (∫ t in (0 : ℝ)..1, f t) ≤ ∑ j ∈ Finset.range K, f (((j : ℝ) + 1) / K) / K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set g : ℕ → ℝ := fun j => (j : ℝ) / K with hg
  have hgrid : ∀ j : ℕ, j ≤ K → g j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [hg, div_le_one hK0]
    exact_mod_cast hj
  have hsteple : ∀ j : ℕ, g j ≤ g (j + 1) := by
    intro j
    have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    simp only [hg]
    gcongr
  have hwidth : ∀ j : ℕ, g (j + 1) - g j = 1 / K := by
    intro j
    simp only [hg]
    push_cast
    field_simp
    ring
  have hsub : ∀ j : ℕ, j < K → Set.uIcc (g j) (g (j + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    rw [Set.uIcc_of_le (hsteple j)]
    exact Set.Icc_subset_Icc (hgrid j hj.le).1 (hgrid (j + 1) hj).2
  have hint : ∀ j < K, IntervalIntegrable f MeasureTheory.volume (g j) (g (j + 1)) :=
    fun j hj => MonotoneOn.intervalIntegrable (hmono.mono (hsub j hj))
  have hsum : ∑ j ∈ Finset.range K, ∫ t in (g j)..(g (j + 1)), f t = ∫ t in (g 0)..(g K), f t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have hg0 : g 0 = 0 := by simp [hg]
  have hgK : g K = 1 := by
    simp only [hg]
    exact div_self (ne_of_gt hK0)
  have hmem : ∀ j : ℕ, j < K → ∀ t ∈ Set.Icc (g j) (g (j + 1)), t ∈ Set.Icc (0 : ℝ) 1 :=
    fun j hj t ht => ⟨le_trans (hgrid j hj.le).1 ht.1, le_trans ht.2 (hgrid (j + 1) hj).2⟩
  have hlow : ∀ j ∈ Finset.range K, f (g j) / K ≤ ∫ t in (g j)..(g (j + 1)), f t := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hle : (∫ _t in (g j)..(g (j + 1)), f (g j)) ≤ ∫ t in (g j)..(g (j + 1)), f t :=
      intervalIntegral.integral_mono_on (hsteple j) intervalIntegrable_const (hint j hjK)
        fun t ht => hmono (hgrid j hjK.le) (hmem j hjK t ht) ht.1
    rw [intervalIntegral.integral_const, hwidth j, smul_eq_mul] at hle
    calc f (g j) / K = 1 / (K : ℝ) * f (g j) := by ring
      _ ≤ _ := hle
  have hhigh : ∀ j ∈ Finset.range K,
      (∫ t in (g j)..(g (j + 1)), f t) ≤ f (g (j + 1)) / K := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hle : (∫ t in (g j)..(g (j + 1)), f t) ≤ ∫ _t in (g j)..(g (j + 1)), f (g (j + 1)) :=
      intervalIntegral.integral_mono_on (hsteple j) (hint j hjK) intervalIntegrable_const
        fun t ht => hmono (hmem j hjK t ht) (hgrid (j + 1) hjK) ht.2
    rw [intervalIntegral.integral_const, hwidth j, smul_eq_mul] at hle
    calc (∫ t in (g j)..(g (j + 1)), f t) ≤ 1 / (K : ℝ) * f (g (j + 1)) := hle
      _ = f (g (j + 1)) / K := by ring
  have hcast : ∀ j : ℕ, g (j + 1) = ((j : ℝ) + 1) / K := by
    intro j
    simp only [hg]
    push_cast
    ring
  constructor
  · have h := Finset.sum_le_sum hlow
    rwa [hsum, hg0, hgK] at h
  · have h := Finset.sum_le_sum hhigh
    rw [hsum, hg0, hgK] at h
    simpa only [hcast] using h

/-- The two Riemann sums differ by `(f 1 − f 0)/K`. -/
theorem riemannSum_right_sub_left (f : ℝ → ℝ) {K : ℕ} (hK : 0 < K) :
    (∑ j ∈ Finset.range K, f (((j : ℝ) + 1) / K) / K)
        - ∑ j ∈ Finset.range K, f ((j : ℝ) / K) / K = (f 1 - f 0) / K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hcast : ∀ j : ℕ, ((j : ℝ) + 1) / K = ((j + 1 : ℕ) : ℝ) / K := by
    intro j
    push_cast
    ring
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range K, f (((j : ℝ) + 1) / K) / K - f ((j : ℝ) / K) / K
      = (fun j : ℕ => f ((j : ℝ) / K) / K) (j + 1) - (fun j : ℕ => f ((j : ℝ) / K) / K) j := by
    intro j _
    simp only [hcast j]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / K) / K) K]
  have hKK : ((K : ℕ) : ℝ) / K = 1 := div_self (ne_of_gt hK0)
  simp only [Nat.cast_zero, zero_div, hKK]
  ring

/-! ### Koksma's inequality -/

/-- **Koksma's inequality** for a nondecreasing integrand: the error of the average along the
first `N` terms of `x` is at most the total variation `f 1 − f 0` times the discrepancy.  No
continuity is needed: the integrand may have jumps. -/
theorem koksma_monotone {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) (x : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (f 1 - f 0) * discrepancy x N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a fine enough grid
  obtain ⟨K, hKgt⟩ := exists_nat_gt (max ((f 1 - f 0) / ε) 1)
  have hK1 : (1 : ℝ) < K := lt_of_le_of_lt (le_max_right _ _) hKgt
  have hK : 0 < K := by exact_mod_cast lt_trans zero_lt_one hK1
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hKε : (f 1 - f 0) / K < ε := by
    have h1 : (f 1 - f 0) / ε < (K : ℝ) := lt_of_le_of_lt (le_max_left _ _) hKgt
    rw [div_lt_iff₀ hε] at h1
    rw [div_lt_iff₀ hK0]
    linarith
  -- the two step sums bracket the sum of the values
  have hlowsum := sum_stepLeft_le_sum_fract hmono hK x N
  have hupsum := sum_fract_le_sum_stepRight hmono hK x N
  have hcellL := abs_le.1 (abs_sum_cellDev_le hmono x hK hN)
  have hcellR := abs_le.1 (abs_sum_cellDev_right_le hmono x hK hN)
  obtain ⟨hriemannL, hriemannR⟩ := riemannSum_le_integral_le hmono hK
  have hdiffRL := riemannSum_right_sub_left f hK
  -- each cell deviation sum is the difference of a step average and a Riemann sum
  have hsplitL : ∑ j ∈ Finset.range K,
        f ((j : ℝ) / K) * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)
      = (∑ j ∈ Finset.range K,
          (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)) / N
        - ∑ j ∈ Finset.range K, f ((j : ℝ) / K) / K := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hsplitR : ∑ j ∈ Finset.range K,
        f (((j : ℝ) + 1) / K)
          * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)
      = (∑ j ∈ Finset.range K,
          (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f (((j : ℝ) + 1) / K)) / N
        - ∑ j ∈ Finset.range K, f (((j : ℝ) + 1) / K) / K := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hsplitL] at hcellL
  rw [hsplitR] at hcellR
  -- the sandwich, divided by `N`
  have havgL : (∑ j ∈ Finset.range K,
      (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)) / N
      ≤ (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N := by
    gcongr
  have havgR : (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N
      ≤ (∑ j ∈ Finset.range K,
          (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f (((j : ℝ) + 1) / K)) / N := by
    gcongr
  rw [abs_le]
  constructor <;> linarith [hcellL.1, hcellL.2, hcellR.1, hcellR.2]

/-- **Koksma's inequality** for an integrand of bounded variation, presented as a difference
`f = g - h` of two nondecreasing functions: the error is at most the sum of the two rises times
the discrepancy. -/
theorem koksma_sub_monotone {f g h : ℝ → ℝ}
    (hfgh : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = g t - h t)
    (hgmono : MonotoneOn g (Set.Icc 0 1)) (hhmono : MonotoneOn h (Set.Icc 0 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ ((g 1 - g 0) + (h 1 - h 0)) * discrepancy x N := by
  have hfract : ∀ n : ℕ, Int.fract (x n) ∈ Set.Icc (0 : ℝ) 1 :=
    fun n => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hsum : ∑ n ∈ Finset.range N, f (Int.fract (x n))
      = (∑ n ∈ Finset.range N, g (Int.fract (x n)))
        - ∑ n ∈ Finset.range N, h (Int.fract (x n)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => hfgh _ (hfract n)
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
  have hhint : IntervalIntegrable h MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
  have hint : (∫ t in (0 : ℝ)..1, f t)
      = (∫ t in (0 : ℝ)..1, g t) - ∫ t in (0 : ℝ)..1, h t := by
    rw [← intervalIntegral.integral_sub hgint hhint]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hfgh t ht
  have hg := abs_le.1 (koksma_monotone hgmono x hN)
  have hh := abs_le.1 (koksma_monotone hhmono x hN)
  rw [hsum, hint, sub_div, abs_le]
  constructor <;> nlinarith [hg.1, hg.2, hh.1, hh.2]

/-- **Koksma's inequality** for a Lipschitz integrand. -/
theorem koksma_lipschitz {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 3 * L * discrepancy x N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hD := discrepancy_nonneg x N
  -- the two monotone pieces `f + L t` and `L t`
  have hmono_h : MonotoneOn (fun t : ℝ => L * t) (Set.Icc (0 : ℝ) 1) :=
    fun _ _ _ _ hst => mul_le_mul_of_nonneg_left hst hL
  have hmono_g : MonotoneOn (fun t : ℝ => f t + L * t) (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have hb := (abs_le.1 (hlip s t hs ht)).1
    rw [abs_of_nonneg (sub_nonneg.2 hst)] at hb
    simp only
    linarith
  have hg := koksma_monotone hmono_g x hN
  have hh := koksma_monotone hmono_h x hN
  -- split the sum and the integral
  have hinth : IntervalIntegrable (fun t : ℝ => L * t) MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hintg : IntervalIntegrable (fun t : ℝ => f t + L * t) MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
  have hintf : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    have := hintg.sub hinth
    simpa using this
  have hsum : ∑ n ∈ Finset.range N, (f (Int.fract (x n)) + L * Int.fract (x n))
      = (∑ n ∈ Finset.range N, f (Int.fract (x n)))
        + ∑ n ∈ Finset.range N, L * Int.fract (x n) := Finset.sum_add_distrib
  have hint : (∫ t in (0 : ℝ)..1, (f t + L * t))
      = (∫ t in (0 : ℝ)..1, f t) + ∫ t in (0 : ℝ)..1, L * t :=
    intervalIntegral.integral_add hintf hinth
  rw [hsum, hint, add_div] at hg
  -- the Lipschitz bound on the total variation of `f`
  have hfL : f 1 - f 0 ≤ L := by
    have := hlip 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    have h1 : |f 1 - f 0| ≤ L := by simpa using this
    exact le_trans (le_abs_self _) h1
  have h1 := abs_le.1 hg
  have h2 := abs_le.1 hh
  have hgval : f 1 + L * 1 - (f 0 + L * 0) = (f 1 - f 0) + L := by ring
  have hhval : L * 1 - L * 0 = L := by ring
  rw [hgval] at h1
  rw [hhval] at h2
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- A sequence whose discrepancy tends to `0` integrates every monotone function correctly in
the limit. -/
theorem tendsto_average_of_tendsto_discrepancy {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1))
    {x : ℕ → ℝ}
    (hx : Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => (f 1 - f 0) * discrepancy x N) atTop (𝓝 0) := by
    simpa using hx.const_mul (f 1 - f 0)
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [Real.dist_eq]
  exact koksma_monotone hmono x hN

/-- The concrete instance: for irrational `α` the sequence `α n²` integrates every monotone
function correctly. -/
theorem tendsto_average_quadratic {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1))
    {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (α * n ^ 2))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
  tendsto_average_of_tendsto_discrepancy hmono (tendsto_discrepancy_quadratic hα)

end WeylDiscrepancy

end RiemannHypothesis
