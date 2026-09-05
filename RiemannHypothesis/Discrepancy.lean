/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDiscrepancyGeneral

/-!
# The discrepancy of a sequence modulo one, and a power saving for `α n`

`RiemannHypothesis.WeylDiscrepancyGeneral` proves the Erdős–Turán type inequality for *every*
subinterval of `[0, 1]`, which is what a discrepancy needs; this module introduces the
discrepancy itself and states the bounds in terms of it.

    D_N(x) = sup { |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| : 0 ≤ a ≤ b ≤ 1 } .

The supremum is over a nonempty set of reals bounded by `1`, so it exists; the two facts that
make it usable are `le_discrepancy` (every interval is dominated by it) and
`discrepancy_le_of_forall` (a bound valid for every interval bounds it).

With the discrepancy available, the rate for a badly approximable `α` can be stated in the shape
it is usually quoted in, with no auxiliary parameter `K`:

    D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9)   for N ≥ 8⁹ ,

obtained from `abs_countIn_div_sub_le_linear_of_le` by the choice `K = ⌊N^(1/9)⌋`, which is
legitimate exactly because the earlier bound is now available for all intervals.  In particular
`D_N(α n) → 0`, which is Weyl's theorem for `α n` with a rate.

## Main results

* `discrepancy` — the discrepancy of the first `N` terms.
* `discrepancy_nonneg`, `discrepancy_le_one`, `le_discrepancy`, `discrepancy_le_of_forall` — the
  basic interface.
* `discrepancy_le_pow` — the Erdős–Turán bound `D_N ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N`.
* `discrepancy_linear_le` — `D_N(α n) ≤ (20 + 2/c)/K` whenever `K ≥ 8` and `K⁹ ≤ N`.
* `discrepancy_linear_le_rpow` — **the power saving** `D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9)` for
  `N ≥ 8⁹`.
* `tendsto_discrepancy_linear` — hence `D_N(α n) → 0`.

## Scope

The exponent `1/9` is the one inherited from `RiemannHypothesis.WeylDiscrepancy`, whose kernel
carries the weight `1` rather than the `1/m` of the sharp Erdős–Turán inequality; the classical
rate for a badly approximable `α` is `O(log N / N)`.  Only badly approximable `α` are covered:
for an irrational of infinite type no power saving is true.  Nothing here concerns `ζ`.
-/

noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount

/-! ### The discrepancy -/

/-- The deviations `|#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)|` over all subintervals
`[a, b) ⊆ [0, 1]`. -/
def discrepancySet (x : ℕ → ℝ) (N : ℕ) : Set ℝ :=
  {d | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ d = |(countIn x a b N : ℝ) / N - (b - a)|}

/-- **The discrepancy** of the first `N` terms of `x` modulo one. -/
def discrepancy (x : ℕ → ℝ) (N : ℕ) : ℝ := sSup (discrepancySet x N)

/-- An empty interval catches nothing. -/
theorem countIn_self (x : ℕ → ℝ) (a : ℝ) (N : ℕ) : countIn x a a N = 0 := by
  classical
  unfold countIn
  rw [Finset.filter_false_of_mem, Finset.card_empty]
  rintro n - ⟨h1, h2⟩
  exact absurd h1 (not_le.2 h2)

theorem discrepancySet_nonempty (x : ℕ → ℝ) (N : ℕ) : (discrepancySet x N).Nonempty :=
  ⟨0, 0, 0, le_rfl, le_rfl, zero_le_one, by simp [countIn_self]⟩

/-- Each deviation is at most `1`. -/
theorem abs_countIn_div_sub_le_one (x : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (N : ℕ) : |(countIn x a b N : ℝ) / N - (b - a)| ≤ 1 := by
  have hcount0 : (0 : ℝ) ≤ (countIn x a b N : ℝ) / N := by positivity
  have hcount1 : (countIn x a b N : ℝ) / N ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast countIn_le x a b N
  rw [abs_le]
  constructor <;> linarith

theorem discrepancySet_bddAbove (x : ℕ → ℝ) (N : ℕ) : BddAbove (discrepancySet x N) := by
  refine ⟨1, ?_⟩
  rintro d ⟨a, b, ha, hab, hb, rfl⟩
  exact abs_countIn_div_sub_le_one x ha hab hb N

/-- Every interval is dominated by the discrepancy. -/
theorem le_discrepancy (x : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ) :
    |(countIn x a b N : ℝ) / N - (b - a)| ≤ discrepancy x N :=
  le_csSup (discrepancySet_bddAbove x N) ⟨a, b, ha, hab, hb, rfl⟩

/-- A bound valid for every interval bounds the discrepancy. -/
theorem discrepancy_le_of_forall (x : ℕ → ℝ) {N : ℕ} {C : ℝ}
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → |(countIn x a b N : ℝ) / N - (b - a)| ≤ C) :
    discrepancy x N ≤ C := by
  refine csSup_le (discrepancySet_nonempty x N) ?_
  rintro d ⟨a, b, ha, hab, hb, rfl⟩
  exact h a b ha hab hb

theorem discrepancy_nonneg (x : ℕ → ℝ) (N : ℕ) : 0 ≤ discrepancy x N := by
  have h := le_discrepancy x (a := 0) (b := 0) le_rfl le_rfl zero_le_one N
  simpa [countIn_self] using h

theorem discrepancy_le_one (x : ℕ → ℝ) (N : ℕ) : discrepancy x N ≤ 1 :=
  discrepancy_le_of_forall x fun _ _ ha hab hb => abs_countIn_div_sub_le_one x ha hab hb N

/-- The discrepancy is not a vacuous quantity: the constant sequence `0`, whose fractional parts
all sit at `0`, has discrepancy at least `1/2`, the interval `[1/2, 1)` receiving none of them. -/
theorem half_le_discrepancy_const_zero (N : ℕ) :
    (1 : ℝ) / 2 ≤ discrepancy (fun _ : ℕ => (0 : ℝ)) N := by
  classical
  have hcount : countIn (fun _ : ℕ => (0 : ℝ)) (1 / 2) 1 N = 0 := by
    unfold countIn
    rw [Finset.filter_false_of_mem, Finset.card_empty]
    rintro n - ⟨h1, -⟩
    rw [Int.fract_zero] at h1
    linarith
  have h := le_discrepancy (fun _ : ℕ => (0 : ℝ)) (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    le_rfl N
  rw [hcount] at h
  norm_num at h
  exact h

/-! ### The Erdős–Turán bound for the discrepancy -/

/-- **The Erdős–Turán inequality for the discrepancy**: for `K ≥ 8` and `N ≥ 1`,
`D_N ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N`. -/
theorem discrepancy_le_pow (x : ℕ → ℝ) {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N) :
    discrepancy x N
      ≤ 20 / K + 4 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N :=
  discrepancy_le_of_forall x fun _ _ ha hab hb =>
    abs_countIn_div_sub_le_pow_of_le x hK hN ha hab hb

/-- The rate for a badly approximable `α`, in terms of the discrepancy. -/
theorem discrepancy_linear_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {K N : ℕ} (hK : 8 ≤ K)
    (hNK : K ^ 9 ≤ N) :
    discrepancy (fun n : ℕ => α * n) N ≤ (20 + 2 / c) / K :=
  discrepancy_le_of_forall _ fun _ _ ha hab hb =>
    abs_countIn_div_sub_le_linear_of_le hc hbad hK hNK ha hab hb

/-! ### The power saving -/

/-- **A power saving for the discrepancy of `α n`.**  For a badly approximable `α` and `N ≥ 8⁹`,

    D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9) . -/
theorem discrepancy_linear_le_rpow {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {N : ℕ} (hN : 8 ^ 9 ≤ N) :
    discrepancy (fun n : ℕ => α * n) N ≤ 2 * (20 + 2 / c) * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set y : ℝ := (N : ℝ) ^ ((1 : ℝ) / 9) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hNR _
  have hy8 : (8 : ℝ) ≤ y := by
    have hcast : ((8 : ℝ) ^ (9 : ℕ)) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : ((8 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) ≤ y := by
      rw [hy]
      exact Real.rpow_le_rpow (by positivity) hcast (by norm_num)
    have h2 : ((8 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) = 8 := by
      rw [← Real.rpow_natCast (8 : ℝ) 9, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [h2 ▸ h1]
  set K : ℕ := ⌊y⌋₊ with hK
  have hK8 : 8 ≤ K := by
    rw [hK]
    exact Nat.le_floor (by exact_mod_cast hy8)
  have hKy : (K : ℝ) ≤ y := Nat.floor_le hy0.le
  have hKpos : (0 : ℝ) < K := by
    have : (8 : ℝ) ≤ K := by exact_mod_cast hK8
    linarith
  have hKN : K ^ 9 ≤ N := by
    have h1 : (K : ℝ) ^ (9 : ℕ) ≤ y ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hKy 9
    have h2 : y ^ (9 : ℕ) = (N : ℝ) := by
      rw [hy, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 9)) 9, ← Real.rpow_mul hNR.le]
      norm_num
    have : ((K ^ 9 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by push_cast; linarith [h2 ▸ h1]
    exact_mod_cast this
  have hylow : y - 1 < (K : ℝ) := by
    have := Nat.sub_one_lt_floor y
    rw [hK]
    exact_mod_cast this
  have hyhalf : y / 2 ≤ (K : ℝ) := by linarith
  have hmain := discrepancy_linear_le hc hbad hK8 hKN
  have hcoef : 0 < 20 + 2 / c := by positivity
  have hinv : (20 + 2 / c) / K ≤ 2 * (20 + 2 / c) / y := by
    rw [div_le_div_iff₀ hKpos hy0]
    nlinarith
  have hrpow : (N : ℝ) ^ (-(1 : ℝ) / 9) = 1 / y := by
    rw [hy, one_div, ← Real.rpow_neg hNR.le, neg_div]
  rw [hrpow]
  calc discrepancy (fun n : ℕ => α * n) N ≤ (20 + 2 / c) / K := hmain
    _ ≤ 2 * (20 + 2 / c) / y := hinv
    _ = 2 * (20 + 2 / c) * (1 / y) := by ring

/-- **Weyl's theorem for `α n` with a rate**: for a badly approximable `α` the discrepancy of the
first `N` terms tends to `0`. -/
theorem tendsto_discrepancy_linear {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) :
    Tendsto (fun N : ℕ => discrepancy (fun n : ℕ => α * n) N) atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun N : ℕ => 2 * (20 + 2 / c) * (N : ℝ) ^ (-(1 : ℝ) / 9)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-(1 : ℝ) / 9)) atTop (𝓝 0) := by
      have h := _root_.tendsto_rpow_neg_atTop (y := (1 : ℝ) / 9) (by norm_num)
      have h' := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      refine h'.congr fun N => ?_
      simp [Function.comp, neg_div]
    simpa using h1.const_mul (2 * (20 + 2 / c))
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with N using discrepancy_nonneg _ _
  · filter_upwards [eventually_ge_atTop (8 ^ 9)] with N hN
    exact discrepancy_linear_le_rpow hc hbad hN

end WeylDiscrepancy

end RiemannHypothesis
