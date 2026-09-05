/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCountGeneral

/-!
# Weyl's criterion in its counting form

`RiemannHypothesis.WeylCriterion` proves Weyl's criterion in the analytic form: a sequence is
equidistributed modulo one — meaning that the averages of every *continuous* function on the
circle converge to its mean — if and only if all of its exponential sums are `o(N)`.
`RiemannHypothesis.WeylCount` and `RiemannHypothesis.WeylCountGeneral` deduce from
equidistribution the classical *counting* statement: the proportion of `n < N` whose fractional
part lies in a subinterval `[a, b)` of `[0, 1]` tends to `b − a`.

This module proves the converse of that deduction, and so closes the loop: the counting
statement, taken for every subinterval, is itself equivalent to equidistribution and to the
vanishing of the exponential sums.  In particular the criterion becomes available in the form in
which it is usually stated and used, with no continuous test function anywhere.

## Main results

* `CountsEquidistribute` — the counting form: for every `0 ≤ a < b ≤ 1`,
  `#{n < N : Int.fract (x n) ∈ [a, b)} / N → b − a`.
* `weylSumsVanish_of_countsEquidistribute` — the counting form implies the vanishing of every
  exponential sum.
* `equidistributedMod1_iff_countsEquidistribute`,
  `weylSumsVanish_iff_countsEquidistribute` — **Weyl's criterion, counting form**: the three
  statements are equivalent.
* `countsEquidistribute_quadratic` — for irrational `α` the fractional parts of `α n²` fill every
  subinterval of `[0, 1]` with the right frequency.

## Proof

The direction that is new here is `counting ⟹ exponential sums vanish`.  Fix a nonzero frequency
`m` and cut `[0, 1)` into `K` equal intervals, `K > |m|`.  On the `j`-th interval the phase
`e(m t)` varies by at most `2π|m|/K` (`norm_e2pi_sub_e2pi_le`), so replacing each term
`e(m x n)` of the sum by the value `e(m j/K)` at the left endpoint of the interval containing
`Int.fract (x n)` costs at most `N · 2π|m|/K` in total (`norm_sum_e2pi_sub_stepSum_le`).  What
remains is `∑_{j<K} c_j(N) e(m j/K)` with `c_j(N)` the counting function, and by hypothesis
`c_j(N)/N → 1/K`, so the average tends to the mean of `e(m ·)` over the `K`-th roots of unity,
which vanishes because `K ∤ m` (`sum_e2pi_roots_eq_zero`).  Both terms are therefore below any
prescribed `ε`, which is the assertion.
-/

noncomputable section

open Complex Filter Finset Topology

namespace RiemannHypothesis

namespace WeylPortmanteau

open KusminLandau WeylCriterion WeylCount

/-- The counting (classical) form of equidistribution modulo one: every subinterval `[a, b)` of
`[0, 1]` receives its share `b − a` of the fractional parts. -/
def CountsEquidistribute (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a))

/-! ### Elementary estimates for the phase `e(θ)` -/

/-- The phase is `2π`-Lipschitz at `0`: `‖e(θ) − 1‖ ≤ 2π|θ|`. -/
theorem norm_e2pi_sub_one_le (θ : ℝ) : ‖e2pi θ - 1‖ ≤ 2 * Real.pi * |θ| := by
  rw [e2pi_sub_one_eq, norm_mul]
  have h3 : ‖((-Real.sin (Real.pi * θ) : ℝ) : ℂ)
      + (Real.cos (Real.pi * θ) : ℝ) * Complex.I‖ = 1 := by
    rw [Complex.norm_add_mul_I, show (-Real.sin (Real.pi * θ)) ^ 2 = Real.sin (Real.pi * θ) ^ 2 by
      ring, Real.sin_sq_add_cos_sq]
    exact Real.sqrt_one
  rw [h3, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsin := Real.abs_sin_le_abs (x := Real.pi * θ)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

/-- The phase is `2π`-Lipschitz: `‖e(u) − e(v)‖ ≤ 2π|u − v|`. -/
theorem norm_e2pi_sub_e2pi_le (u v : ℝ) : ‖e2pi u - e2pi v‖ ≤ 2 * Real.pi * |u - v| := by
  have hfac : e2pi u - e2pi v = e2pi v * (e2pi (u - v) - 1) := by
    rw [mul_sub, ← e2pi_add, mul_one]
    ring_nf
  rw [hfac, norm_mul, norm_e2pi, one_mul]
  exact norm_e2pi_sub_one_le _

/-- An integer frequency does not see the integer part of its argument. -/
theorem e2pi_int_mul_fract (m : ℤ) (y : ℝ) :
    e2pi ((m : ℝ) * Int.fract y) = e2pi ((m : ℝ) * y) := by
  rw [show (m : ℝ) * Int.fract y = (m : ℝ) * y - ((m * ⌊y⌋ : ℤ) : ℝ) by
    rw [Int.fract]; push_cast; ring, e2pi_sub_int]

/-- `e(nθ) = e(θ)ⁿ`. -/
theorem e2pi_nat_mul (n : ℕ) (θ : ℝ) : e2pi ((n : ℝ) * θ) = e2pi θ ^ n := by
  induction n with
  | zero => simp [e2pi]
  | succ k ih =>
      have hstep : ((k : ℝ) + 1) * θ = (k : ℝ) * θ + θ := by ring
      push_cast
      rw [hstep, e2pi_add, ih, pow_succ]

/-- The mean of a nontrivial character over the `K`-th roots of unity vanishes. -/
theorem sum_e2pi_roots_eq_zero {m : ℤ} {K : ℕ} (hK : 0 < K) (hm : ¬ ((K : ℤ) ∣ m)) :
    ∑ j ∈ Finset.range K, e2pi ((m : ℝ) * j / K) = 0 := by
  have hKR : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK.ne'
  set z : ℂ := e2pi ((m : ℝ) / K) with hz
  have hterm : ∀ j ∈ Finset.range K, e2pi ((m : ℝ) * j / K) = z ^ j := by
    intro j _
    rw [hz, ← e2pi_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hzK : z ^ K = 1 := by
    rw [hz, ← e2pi_nat_mul, show (K : ℝ) * ((m : ℝ) / K) = ((m : ℤ) : ℝ) by field_simp,
      show ((m : ℝ)) = (0 : ℝ) - ((-m : ℤ) : ℝ) by push_cast; ring, e2pi_sub_int]
    simp [e2pi]
  have hzne : z ≠ 1 := by
    intro hone
    rw [hz, e2pi, Complex.exp_eq_one_iff] at hone
    obtain ⟨n, hn⟩ := hone
    have h2 : ((2 * Real.pi * ((m : ℝ) / K) : ℝ) : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      push_cast
      push_cast at hn
      linear_combination hn
    have hre : 2 * Real.pi * ((m : ℝ) / K) = (n : ℝ) * (2 * Real.pi) := Complex.ofReal_inj.mp h2
    refine hm ⟨n, ?_⟩
    have hpi := Real.pi_pos
    have hmn : (m : ℝ) = (K : ℝ) * (n : ℝ) := by
      field_simp at hre
      nlinarith [hre]
    exact_mod_cast hmn
  rw [geom_sum_eq hzne, hzK, sub_self, zero_div]

/-! ### Replacing the phase by its value at the left endpoint of a cell -/

/-- The index of the cell of the partition of `[0, 1)` into `K` equal intervals which contains
the fractional part of `y`. -/
def cell (K : ℕ) (y : ℝ) : ℕ := ⌊(K : ℝ) * Int.fract y⌋₊

theorem cell_lt {K : ℕ} (hK : 0 < K) (y : ℝ) : cell K y < K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  rw [cell, Nat.floor_lt (by positivity)]
  nlinarith [Int.fract_lt_one y, Int.fract_nonneg y]

/-- The cell index describes membership in the cell: this is the partition of `[0, 1)` used
throughout. -/
theorem cell_eq_iff {K : ℕ} (hK : 0 < K) {y : ℝ} {j : ℕ} :
    cell K y = j ↔ (j : ℝ) / K ≤ Int.fract y ∧ Int.fract y < ((j : ℝ) + 1) / K := by
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  rw [cell, Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [div_le_iff₀ hK0]; linarith, by rw [lt_div_iff₀ hK0]; linarith⟩
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hK0] at h1
    rw [lt_div_iff₀ hK0] at h2
    exact ⟨by linarith, by linarith⟩

/-- Counting the terms of a cell: the counting function of the cell `[j/K, (j+1)/K)` is the
cardinality of the fibre of `cell K ∘ x`. -/
theorem countIn_cell_eq_card {K : ℕ} (hK : 0 < K) (x : ℕ → ℝ) (j N : ℕ) :
    countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N
      = ((Finset.range N).filter fun n => cell K (x n) = j).card := by
  classical
  unfold countIn
  congr 1
  exact Finset.filter_congr fun n _ => (cell_eq_iff hK).symm

/-- Replacing each phase by the value at the left endpoint of its cell costs at most
`N · 2π|m|/K`. -/
theorem norm_sum_e2pi_sub_stepSum_le {K : ℕ} (hK : 0 < K) (x : ℕ → ℝ) (m : ℤ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n))
        - ∑ j ∈ Finset.range K,
            (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℂ) * e2pi ((m : ℝ) * j / K)‖
      ≤ (N : ℝ) * (2 * Real.pi * |(m : ℝ)| / K) := by
  classical
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hmaps : ∀ n ∈ Finset.range N, cell K (x n) ∈ Finset.range K :=
    fun n _ => Finset.mem_range.2 (cell_lt hK _)
  have h1 : (∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n))
      = ∑ j ∈ Finset.range K,
          ∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), e2pi ((m : ℝ) * x n) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h2 : ∀ j ∈ Finset.range K,
      (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℂ) * e2pi ((m : ℝ) * j / K)
        = ∑ _n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), e2pi ((m : ℝ) * j / K) := by
    intro j _
    rw [countIn_cell_eq_card hK, Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.sum_congr rfl h2, ← Finset.sum_sub_distrib]
  have hbound : ∀ j ∈ Finset.range K,
      ‖(∑ n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), e2pi ((m : ℝ) * x n))
        - ∑ _n ∈ (Finset.range N).filter (fun n => cell K (x n) = j), e2pi ((m : ℝ) * j / K)‖
      ≤ (((Finset.range N).filter (fun n => cell K (x n) = j)).card : ℝ)
          * (2 * Real.pi * |(m : ℝ)| / K) := by
    intro j _
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum ?_
    intro n hn
    obtain ⟨hlo, hhi⟩ := (cell_eq_iff hK).1 (Finset.mem_filter.1 hn).2
    rw [← e2pi_int_mul_fract]
    refine le_trans (norm_e2pi_sub_e2pi_le _ _) ?_
    have hsplit : ((j : ℝ) + 1) / K = (j : ℝ) / K + 1 / K := by field_simp
    have h0 : 0 ≤ Int.fract (x n) - (j : ℝ) / K := by linarith
    have h1' : Int.fract (x n) - (j : ℝ) / K ≤ 1 / K := by rw [hsplit] at hhi; linarith
    have hdiff : |(m : ℝ) * Int.fract (x n) - (m : ℝ) * j / K| ≤ |(m : ℝ)| / K := by
      rw [show (m : ℝ) * Int.fract (x n) - (m : ℝ) * j / K
          = (m : ℝ) * (Int.fract (x n) - (j : ℝ) / K) by ring, abs_mul, abs_of_nonneg h0]
      calc |(m : ℝ)| * (Int.fract (x n) - (j : ℝ) / K) ≤ |(m : ℝ)| * (1 / K) :=
            mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
        _ = |(m : ℝ)| / K := by ring
    calc 2 * Real.pi * |(m : ℝ) * Int.fract (x n) - (m : ℝ) * j / K|
        ≤ 2 * Real.pi * (|(m : ℝ)| / K) := by nlinarith [Real.pi_pos]
      _ = 2 * Real.pi * |(m : ℝ)| / K := by ring
  refine le_trans (norm_sum_le_of_le _ hbound) ?_
  rw [← Finset.sum_mul]
  have hcard : ∑ j ∈ Finset.range K,
      (((Finset.range N).filter (fun n => cell K (x n) = j)).card : ℝ) = (N : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_range]
  rw [hcard]

/-! ### Weyl's criterion in counting form -/

/-- Equidistribution implies the counting form; this is `tendsto_countIn_div_of_le`. -/
theorem countsEquidistribute_of_equidistributedMod1 {x : ℕ → ℝ} (h : EquidistributedMod1 x) :
    CountsEquidistribute x :=
  fun _ _ ha hab hb => tendsto_countIn_div_of_le h ha hab hb

/-- **The counting form implies the vanishing of the exponential sums.** -/
theorem weylSumsVanish_of_countsEquidistribute {x : ℕ → ℝ} (h : CountsEquidistribute x) :
    WeylSumsVanish x := by
  intro m hm
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a partition of `[0, 1)` into `K` cells, fine enough for `ε` and with `K > |m|`
  obtain ⟨K, hKgt⟩ := exists_nat_gt (max ((m.natAbs : ℝ)) (4 * Real.pi * |(m : ℝ)| / ε))
  have hKm : (m.natAbs : ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hKgt
  have hKe : 4 * Real.pi * |(m : ℝ)| / ε < K := lt_of_le_of_lt (le_max_right _ _) hKgt
  have hK0 : (0 : ℝ) < K := lt_of_le_of_lt (Nat.cast_nonneg _) hKm
  have hK : 0 < K := Nat.cast_pos.mp hK0
  have hmpos : 0 < m.natAbs := Int.natAbs_pos.2 hm
  have hdvd : ¬ ((K : ℤ) ∣ m) := by
    intro hd
    have hdn : K ∣ m.natAbs := by simpa using Int.natAbs_dvd_natAbs.2 hd
    have hle : (K : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast Nat.le_of_dvd hmpos hdn
    linarith
  have hstep : 2 * Real.pi * |(m : ℝ)| / K < ε / 2 := by
    rw [div_lt_iff₀ hε] at hKe
    rw [div_lt_iff₀ hK0]
    linarith
  -- the averaged step sum tends to the mean of the character over the `K`-th roots of unity
  have hlim : ∀ j ∈ Finset.range K,
      Tendsto (fun N : ℕ =>
          (((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N : ℝ) : ℂ)
            * e2pi ((m : ℝ) * j / K)) atTop
        (𝓝 (((1 / K : ℝ) : ℂ) * e2pi ((m : ℝ) * j / K))) := by
    intro j hj
    have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hj
    have h0 : (0 : ℝ) ≤ (j : ℝ) / K := by positivity
    have hab : (j : ℝ) / K < ((j : ℝ) + 1) / K := by
      rw [div_lt_div_iff₀ hK0 hK0]
      nlinarith
    have hb : ((j : ℝ) + 1) / K ≤ 1 := by rw [div_le_one hK0]; exact hjK
    have hcount := h _ _ h0 hab hb
    rw [show ((j : ℝ) + 1) / K - (j : ℝ) / K = 1 / K by field_simp; ring] at hcount
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hcount).mul tendsto_const_nhds
  have hsum := tendsto_finsetSum (Finset.range K) hlim
  rw [show ∑ j ∈ Finset.range K, ((1 / K : ℝ) : ℂ) * e2pi ((m : ℝ) * j / K) = 0 by
    rw [← Finset.mul_sum, sum_e2pi_roots_eq_zero hK hdvd, mul_zero]] at hsum
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨N₀, hN₀⟩ := hsum (ε / 2) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hg := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Complex.dist_eq, sub_zero] at hg
  -- the two contributions
  set S : ℂ := ∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n) with hS
  set T : ℂ := ∑ j ∈ Finset.range K,
    (countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℂ) * e2pi ((m : ℝ) * j / K) with hT
  have hTg : T / (N : ℂ) = ∑ j ∈ Finset.range K,
      (((countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N : ℝ) : ℂ)
        * e2pi ((m : ℝ) * j / K) := by
    rw [hT, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hTnorm : ‖T‖ / N < ε / 2 := by
    calc ‖T‖ / N = ‖T / (N : ℂ)‖ := by
          rw [norm_div, Complex.norm_natCast]
      _ < ε / 2 := by rw [hTg]; exact hg
  have hdiff : ‖S - T‖ / N ≤ 2 * Real.pi * |(m : ℝ)| / K := by
    have hb := norm_sum_e2pi_sub_stepSum_le hK x m N
    rw [← hS, ← hT] at hb
    rw [div_le_iff₀ hNR]
    linarith
  have hfinal : ‖S‖ / N < ε := by
    have htri : ‖S‖ ≤ ‖S - T‖ + ‖T‖ := by
      simpa using norm_add_le (S - T) T
    have hmono : ‖S‖ / N ≤ (‖S - T‖ + ‖T‖) / N := by gcongr
    rw [add_div] at hmono
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hfinal

/-- The counting form implies equidistribution against continuous test functions. -/
theorem equidistributedMod1_of_countsEquidistribute {x : ℕ → ℝ} (h : CountsEquidistribute x) :
    EquidistributedMod1 x :=
  equidistributedMod1_of_weylSumsVanish (weylSumsVanish_of_countsEquidistribute h)

/-- **Weyl's criterion, counting form**: a sequence is equidistributed modulo one if and only if
every subinterval of `[0, 1]` receives its share of the fractional parts. -/
theorem equidistributedMod1_iff_countsEquidistribute (x : ℕ → ℝ) :
    EquidistributedMod1 x ↔ CountsEquidistribute x :=
  ⟨countsEquidistribute_of_equidistributedMod1, equidistributedMod1_of_countsEquidistribute⟩

/-- **Weyl's criterion, counting form against the exponential sums.** -/
theorem weylSumsVanish_iff_countsEquidistribute (x : ℕ → ℝ) :
    WeylSumsVanish x ↔ CountsEquidistribute x :=
  ⟨fun h => countsEquidistribute_of_equidistributedMod1
      (equidistributedMod1_of_weylSumsVanish h),
    weylSumsVanish_of_countsEquidistribute⟩

/-- For every irrational `α` the fractional parts of `α n²` are equidistributed in the counting
sense. -/
theorem countsEquidistribute_quadratic {α : ℝ} (hα : Irrational α) :
    CountsEquidistribute (fun n : ℕ => α * (n : ℝ) ^ 2) :=
  countsEquidistribute_of_equidistributedMod1 (equidistributedMod1_quadratic hα)

end WeylPortmanteau

end RiemannHypothesis
