/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.KoksmaVariation

/-!
# Koksma's inequality for a Lipschitz integrand, with the sharp constant

`RiemannHypothesis.Koksma` proves Koksma's inequality for a Lipschitz integrand with the constant
`3 L`, and `RiemannHypothesis.KoksmaVariation` improves it to `2 L`.  Both go through the
monotone case, and the factor in front of `L` is the price of that detour.  This module proves
the classical, sharp form

    |(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ L · D_N(x)   (`koksma_lipschitz_sharp`)

for every `L`-Lipschitz `f` on `[0,1]`, every sequence `x` and every `N ≥ 1`.

## Main results

* `abs_sum_weight_cellDev_le` — the cell deviation sum for an *arbitrary* weight sequence `a`:

      |∑_{j<K} a_j (c_j/N − 1/K)| ≤ (∑_{j<K} |a_{j+1} − a_j|) · D_N(x),

  where `c_j` counts the `n < N` whose fractional part lies in the `j`-th cell.  This is the
  summation-by-parts step of `RiemannHypothesis.Koksma` with monotonicity removed; the total
  variation of the weights along the grid replaces the rise.
* `abs_avg_sub_stepAvg_le`, `abs_integral_sub_riemannSum_le` — for an `L`-Lipschitz integrand,
  replacing each value by the value at the left endpoint of its cell costs at most `L/K`, both in
  the average and in the integral.
* `koksma_lipschitz_sharp` — the sharp inequality.
* `tendsto_average_of_tendsto_discrepancy_lipschitz` — its limiting form.

## Proof

Cut `[0,1)` into the `K` cells `[j/K, (j+1)/K)`, write `t_j = j/K` and let `c_j` be the number of
`n < N` in the `j`-th cell.  Then

    (1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f
      = [(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∑_j (c_j/N) f(t_j)]
        + ∑_j f(t_j) (c_j/N − 1/K)
        + [∑_j (1/K) f(t_j) − ∫₀¹ f] .

The first and the third bracket are at most `L/K` each, because `f` moves by at most `L/K` inside
a cell.  The middle sum is handled by summation by parts against the deviations of the tail
intervals `[t_j, 1)`, each at most `D_N(x)`, and the weights contribute
`∑_j |f(t_{j+1}) − f(t_j)| ≤ K · (L/K) = L`.  So the error is at most `L D_N(x) + 2L/K` for every
`K ≥ 1`, and letting `K` grow gives `L D_N(x)`.

Nothing is lost in the limit: `K` does not appear in the final statement, which is quantitative
and holds for every fixed `N ≥ 1`.
-/

noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace WeylDiscrepancy

open WeylCount WeylPortmanteau

/-- **The cell deviation sum for an arbitrary weight sequence.**  Summation by parts against the
deviations of the tail intervals `[j/K, 1)`; the total variation of the weights along the grid
replaces the rise of the monotone case. -/
theorem abs_sum_weight_cellDev_le (x : ℕ → ℝ) (a : ℕ → ℝ) {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |∑ j ∈ Finset.range K,
        a j * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)|
      ≤ (∑ j ∈ Finset.range K, |a (j + 1) - a j|) * discrepancy x N := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set S : ℕ → ℝ := fun j => (countIn x ((j : ℝ) / K) 1 N : ℝ) / N - (1 - (j : ℝ) / K) with hS
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
  have hstep : ∀ j ∈ Finset.range K,
      |(a (j + 1) - a j) * S (j + 1)| ≤ |a (j + 1) - a j| * discrepancy x N := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_tailDev_le_discrepancy x hK hjK N) (abs_nonneg _)
  have hrewrite : ∑ j ∈ Finset.range K,
      a j * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)
      = ∑ j ∈ Finset.range K, a j * (S j - S (j + 1)) :=
    Finset.sum_congr rfl fun j hj => by rw [hdiff j hj]
  rw [hrewrite, sum_mul_sub_succ a S K, hS0, hSK]
  simp only [mul_zero, sub_zero, zero_add]
  calc |∑ j ∈ Finset.range K, (a (j + 1) - a j) * S (j + 1)|
      ≤ ∑ j ∈ Finset.range K, |(a (j + 1) - a j) * S (j + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, |a (j + 1) - a j| * discrepancy x N :=
        Finset.sum_le_sum hstep
    _ = (∑ j ∈ Finset.range K, |a (j + 1) - a j|) * discrepancy x N := by
        rw [Finset.sum_mul]

section Lipschitz

variable {f : ℝ → ℝ} {L : ℝ}

/-- The grid points lie in `[0,1]`. -/
private theorem grid_mem {K : ℕ} (hK : 0 < K) {j : ℕ} (hj : j ≤ K) :
    ((j : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hK0]
  exact_mod_cast hj

/-- **Replacing each value by the value at the left endpoint of its cell** costs at most `L/K`
in the average. -/
theorem abs_avg_sub_stepAvg_le (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    {K : ℕ} (hK : 0 < K) (x : ℕ → ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n)))
        - ∑ j ∈ Finset.range K,
            (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)|
      ≤ (N : ℝ) * (L / K) := by
  classical
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hmaps : ∀ n ∈ Finset.range N, cell K (x n) ∈ Finset.range K :=
    fun n _ => Finset.mem_range.2 (cell_lt hK _)
  have h1 : (∑ n ∈ Finset.range N, f (Int.fract (x n)))
      = ∑ j ∈ Finset.range K,
          ∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f (Int.fract (x n)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h2 : ∀ j ∈ Finset.range K,
      (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)
        = ∑ _n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f ((j : ℝ) / K) := by
    intro j _
    rw [countIn_cell_eq_card hK, Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.sum_congr rfl h2, ← Finset.sum_sub_distrib]
  have hbound : ∀ j ∈ Finset.range K,
      |(∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f (Int.fract (x n)))
        - ∑ _n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), f ((j : ℝ) / K)|
      ≤ (((Finset.range N).filter (fun n => cell K (x n) = j)).card : ℝ) * (L / K) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hlo, hhi⟩ := (cell_eq_iff hK).1 (Finset.mem_filter.1 hn).2
    have hfr : Int.fract (x n) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hclose : |Int.fract (x n) - (j : ℝ) / K| ≤ 1 / K := by
      rw [abs_of_nonneg (by linarith)]
      have hgap : ((j : ℝ) + 1) / K - (j : ℝ) / K = 1 / K := by
        ring
      linarith
    have := hlip ((j : ℝ) / K) (Int.fract (x n)) (grid_mem hK hjK.le) hfr
    calc |f (Int.fract (x n)) - f ((j : ℝ) / K)| ≤ L * |Int.fract (x n) - (j : ℝ) / K| := this
      _ ≤ L * (1 / K) := by gcongr
      _ = L / K := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [← Finset.sum_mul]
  have hcard : ∑ j ∈ Finset.range K,
      (((Finset.range N).filter (fun n => cell K (x n) = j)).card : ℝ) = (N : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise hmaps
    have hcast : ((Finset.range N).card : ℝ)
        = ∑ j ∈ Finset.range K,
            (((Finset.range N).filter (fun n => cell K (x n) = j)).card : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
    simpa using hcast.symm
  rw [hcard]

/-- **The Riemann sum of an `L`-Lipschitz integrand** differs from the integral by at most
`L/K`. -/
theorem abs_integral_sub_riemannSum_le (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    {K : ℕ} (hK : 0 < K) :
    |(∫ t in (0 : ℝ)..1, f t) - ∑ j ∈ Finset.range K, (1 / K : ℝ) * f ((j : ℝ) / K)|
      ≤ L / K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    have hlipOn : LipschitzOnWith L.toNNReal f (Set.Icc (0 : ℝ) 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hlip b a hb ha
    exact hlipOn.continuousOn
  set t : ℕ → ℝ := fun j => (j : ℝ) / K with ht
  have htmem : ∀ j ≤ K, t j ∈ Set.Icc (0 : ℝ) 1 := fun j hj => grid_mem hK hj
  have hsub : ∀ j < K, Set.uIcc (t j) (t (j + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    have h1 : t j ≤ t (j + 1) := by
      simp only [ht]
      gcongr
      exact Nat.le_succ j
    rw [Set.uIcc_of_le h1]
    exact Set.Icc_subset_Icc (htmem j hj.le).1 (htmem (j + 1) hj).2
  have hint : ∀ j < K, IntervalIntegrable f MeasureTheory.volume (t j) (t (j + 1)) :=
    fun j hj => (hcont.mono (hsub j hj)).intervalIntegrable
  have hsplit : ∑ j ∈ Finset.range K, ∫ s in (t j)..(t (j + 1)), f s = ∫ s in (t 0)..(t K), f s :=
    intervalIntegral.sum_integral_adjacent_intervals fun j hj => hint j hj
  have ht0 : t 0 = 0 := by simp [ht]
  have htK : t K = 1 := by
    simp only [ht]
    exact div_self (ne_of_gt hK0)
  rw [ht0, htK] at hsplit
  rw [← hsplit, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcell : ∀ j ∈ Finset.range K,
      |(∫ s in (t j)..(t (j + 1)), f s) - (1 / K : ℝ) * f ((j : ℝ) / K)| ≤ L / K ^ 2 := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hle : t j ≤ t (j + 1) := by
      simp only [ht]
      gcongr
      exact Nat.le_succ j
    have hlen : t (j + 1) - t j = 1 / K := by
      simp only [ht]
      push_cast
      ring
    have hconstint : (∫ _s in (t j)..(t (j + 1)), f ((j : ℝ) / K))
        = (1 / K : ℝ) * f ((j : ℝ) / K) := by
      rw [intervalIntegral.integral_const, hlen]
      simp [smul_eq_mul]
    have hsubint : (∫ s in (t j)..(t (j + 1)), f s) - (1 / K : ℝ) * f ((j : ℝ) / K)
        = ∫ s in (t j)..(t (j + 1)), (f s - f ((j : ℝ) / K)) := by
      rw [← hconstint, intervalIntegral.integral_sub (hint j hjK) intervalIntegrable_const]
    rw [hsubint]
    have hnorm : ∀ s ∈ Set.uIoc (t j) (t (j + 1)), ‖f s - f ((j : ℝ) / K)‖ ≤ L / K := by
      intro s hs
      rw [Set.uIoc_of_le hle] at hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) 1 :=
        Set.Icc_subset_Icc (htmem j hjK.le).1 (htmem (j + 1) hjK).2 ⟨hs.1.le, hs.2⟩
      have hclose : |s - (j : ℝ) / K| ≤ 1 / K := by
        rw [abs_of_nonneg (by simpa [ht] using sub_nonneg.2 hs.1.le)]
        have : s ≤ t (j + 1) := hs.2
        simp only [ht] at this ⊢
        have hlen' : ((j : ℝ) + 1) / K - (j : ℝ) / K = 1 / K := by ring
        push_cast at this
        linarith
      have := hlip ((j : ℝ) / K) s (grid_mem hK hjK.le) hsmem
      calc ‖f s - f ((j : ℝ) / K)‖ = |f s - f ((j : ℝ) / K)| := rfl
        _ ≤ L * |s - (j : ℝ) / K| := this
        _ ≤ L * (1 / K) := by gcongr
        _ = L / K := by ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
    have hlen' : |t (j + 1) - t j| = 1 / K := by
      rw [hlen, abs_of_nonneg (by positivity)]
    calc |∫ s in (t j)..(t (j + 1)), (f s - f ((j : ℝ) / K))| ≤ L / K * |t (j + 1) - t j| := hb
      _ = L / K ^ 2 := by rw [hlen']; ring
  refine le_trans (Finset.sum_le_sum hcell) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq : (K : ℝ) * (L / (K : ℝ) ^ 2) = L / K := by
    field_simp
  exact le_of_eq heq

/-- The values of an `L`-Lipschitz function along the grid have total variation at most `L`. -/
theorem sum_abs_grid_diff_le
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    {K : ℕ} (hK : 0 < K) :
    ∑ j ∈ Finset.range K, |f (((j : ℕ) + 1 : ℕ) / (K : ℝ)) - f ((j : ℝ) / K)| ≤ L := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hterm : ∀ j ∈ Finset.range K,
      |f (((j : ℕ) + 1 : ℕ) / (K : ℝ)) - f ((j : ℝ) / K)| ≤ L / K := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have hcast : (((j : ℕ) + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have h1 : ((j : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := grid_mem hK hjK.le
    have h2 : ((((j : ℕ) + 1 : ℕ) : ℝ) / K) ∈ Set.Icc (0 : ℝ) 1 := grid_mem hK hjK
    have hdist : |((((j : ℕ) + 1 : ℕ) : ℝ) / K) - (j : ℝ) / K| = 1 / K := by
      rw [hcast]
      have hgap : ((j : ℝ) + 1) / K - (j : ℝ) / K = 1 / K := by ring
      rw [hgap, abs_of_nonneg (by positivity)]
    have := hlip ((j : ℝ) / K) ((((j : ℕ) + 1 : ℕ) : ℝ) / K) h1 h2
    rw [hdist] at this
    calc |f (((j : ℕ) + 1 : ℕ) / (K : ℝ)) - f ((j : ℝ) / K)| ≤ L * (1 / K) := this
      _ = L / K := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq : (K : ℝ) * (L / K) = L := by
    field_simp
  exact le_of_eq heq

/-- The quantitative step: for every `K ≥ 1` the error is at most `L D_N(x) + 2L/K`. -/
theorem abs_avg_sub_integral_le_add (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ L * discrepancy x N + 2 * (L / K) := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set a : ℕ → ℝ := fun j => f ((j : ℝ) / K) with ha
  -- the middle term
  have hmid := abs_sum_weight_cellDev_le x a hK hN
  have hvar : ∑ j ∈ Finset.range K, |a (j + 1) - a j| ≤ L := by
    simpa [ha] using sum_abs_grid_diff_le (f := f) hlip hK
  have hD := discrepancy_nonneg x N
  have hmid' : |∑ j ∈ Finset.range K,
      a j * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K)|
      ≤ L * discrepancy x N := by
    refine hmid.trans ?_
    exact mul_le_mul_of_nonneg_right hvar hD
  -- the averaging term
  have havg := abs_avg_sub_stepAvg_le (f := f) hL hlip hK x N
  have havg' : |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N
      - ∑ j ∈ Finset.range K,
          ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N) * f ((j : ℝ) / K)|
      ≤ L / K := by
    have hsums : ∑ j ∈ Finset.range K,
        ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N) * f ((j : ℝ) / K)
        = (∑ j ∈ Finset.range K,
            (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hrw : (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N
        - ∑ j ∈ Finset.range K,
            ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N) * f ((j : ℝ) / K)
        = ((∑ n ∈ Finset.range N, f (Int.fract (x n)))
            - ∑ j ∈ Finset.range K,
                (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)) / N := by
      rw [hsums, sub_div]
    rw [hrw, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc |(∑ n ∈ Finset.range N, f (Int.fract (x n)))
            - ∑ j ∈ Finset.range K,
                (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) * f ((j : ℝ) / K)|
        ≤ (N : ℝ) * (L / K) := havg
      _ = L / K * N := by ring
  -- the Riemann sum term
  have hriem := abs_integral_sub_riemannSum_le (f := f) hL hlip hK
  -- assemble
  set A : ℝ := ∑ j ∈ Finset.range K,
      ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N) * f ((j : ℝ) / K) with hA
  set B : ℝ := ∑ j ∈ Finset.range K, (1 / K : ℝ) * f ((j : ℝ) / K) with hB
  have hmidAB : ∑ j ∈ Finset.range K,
      a j * ((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N - 1 / K) = A - B := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [ha]; ring
  rw [hmidAB] at hmid'
  have h1 := abs_le.1 havg'
  have h2 := abs_le.1 hmid'
  have h3 := abs_le.1 hriem
  rw [abs_le]
  constructor <;> linarith

/-- **Koksma's inequality for a Lipschitz integrand, with the sharp constant.**  For every
`L`-Lipschitz `f` on `[0,1]`, every sequence `x` and every `N ≥ 1`,

    |(1/N) ∑_{n<N} f(⟨xₙ⟩) − ∫₀¹ f| ≤ L · D_N(x). -/
theorem koksma_lipschitz_sharp (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ L * discrepancy x N := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * L / ε)
  have hK0 : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
  have hKpos : 0 < K := by exact_mod_cast hK0
  have hsmall : 2 * (L / K) < ε := by
    rw [div_lt_iff₀ hε] at hK
    have : 2 * (L / K) = 2 * L / K := by ring
    rw [this, div_lt_iff₀ hK0]
    linarith
  exact le_trans (abs_avg_sub_integral_le_add hL hlip x hKpos hN) (by linarith)

/-- The limiting form: a sequence whose discrepancy tends to `0` integrates every Lipschitz
function correctly, with the sharp constant along the way. -/
theorem tendsto_average_of_tendsto_discrepancy_lipschitz (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    {x : ℕ → ℝ} (hx : Tendsto (fun N : ℕ => discrepancy x N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => L * discrepancy x N) atTop (𝓝 0) := by
    simpa using hx.const_mul L
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [Real.dist_eq]
  exact koksma_lipschitz_sharp hL hlip x hN

end Lipschitz

end WeylDiscrepancy

end RiemannHypothesis
