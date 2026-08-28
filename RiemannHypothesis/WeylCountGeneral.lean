/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCount

/-!
# Equidistribution modulo one: the counting form for an arbitrary subinterval

`RiemannHypothesis.WeylCount` proves the counting form of equidistribution for an interval
`[a, b)` with `0 < a < b < 1`: the hypothesis keeps the interval away from the point `0` where
`[0, 1)` is glued into the circle, and the statement for an interval containing `0` was left
open there.  This module removes that restriction.

The device is a rotation.  If `x` is equidistributed modulo one then so is `x + c` for every
real `c` — immediate from Weyl's criterion, since translating the sequence multiplies each
exponential sum by the unimodular constant `e(m c)` — and for a suitable `c` the translated
interval `[a + c, b + c)` sits inside `(0, 1)`, where the previous result applies.  The
translation matches the counting problems exactly: for `0 ≤ a < b ≤ 1` and `c` with
`0 < a + c` and `b + c < 1`,

    `Int.fract y ∈ [a, b)  ↔  Int.fract (y + c) ∈ [a + c, b + c)` .

## Main results

* `equidistributedMod1_add_const` — equidistribution is invariant under translation.
* `countIn_add_const` — the counting function is invariant under the matched translation.
* `tendsto_countIn_div_of_le` — **the counting form for every subinterval of `[0, 1]`**: if `x`
  is equidistributed modulo one and `0 ≤ a < b ≤ 1`, then
  `#{n < N : Int.fract (x n) ∈ [a, b)} / N → b − a`; in particular the intervals `[0, b)` and
  the whole of `[0, 1)` are covered.
* `tendsto_countIn_div_quadratic_of_le` — the same for `x n = α n²` with `α` irrational.

## Scope

Nothing here concerns `ζ`; the module only widens the range of intervals for which the
classical counting statement is available, and claims no rate of convergence.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory AddCircle

namespace RiemannHypothesis

namespace WeylCount

open KusminLandau WeylCriterion

/-- Equidistribution modulo one is invariant under translating the sequence by a constant. -/
theorem equidistributedMod1_add_const {x : ℕ → ℝ} (h : EquidistributedMod1 x) (c : ℝ) :
    EquidistributedMod1 (fun n => x n + c) := by
  rw [equidistributedMod1_iff_weylSumsVanish] at h ⊢
  intro m hm
  have hnorm : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * (x n + c))‖
        = ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖ := by
    intro N
    have hfac : ∑ n ∈ Finset.range N, e2pi ((m : ℝ) * (x n + c))
        = e2pi ((m : ℝ) * c) * ∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← e2pi_add]
      ring_nf
    rw [hfac, norm_mul, norm_e2pi, one_mul]
  exact (h m hm).congr fun N => by rw [hnorm N]

/-- The membership of a fractional part in `[a, b)` is unchanged by a matched translation. -/
theorem fract_mem_Ico_iff_add {a b c y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hac : 0 < a + c) (hbc : b + c < 1) :
    (a ≤ Int.fract y ∧ Int.fract y < b)
      ↔ (a + c ≤ Int.fract (y + c) ∧ Int.fract (y + c) < b + c) := by
  have hfr : Int.fract (y + c) = Int.fract (Int.fract y + c) := by
    conv_lhs => rw [← Int.fract_add_floor y]
    rw [add_right_comm, Int.fract_add_intCast]
  set u : ℝ := Int.fract y with hu
  have hu0 : 0 ≤ u := Int.fract_nonneg y
  have hu1 : u < 1 := Int.fract_lt_one y
  rw [hfr]
  constructor
  · rintro ⟨h1, h2⟩
    have hmem : Int.fract (u + c) = u + c :=
      Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
    rw [hmem]
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (u + c) 0 with hlt | heq | hgt
    · exfalso
      have hfr' : Int.fract (u + c) = u + c + 1 := by
        have : Int.fract (u + c + 1) = Int.fract (u + c) := Int.fract_add_one (u + c)
        rw [← this]
        exact Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
      rw [hfr'] at h2
      linarith
    · have hfr' : Int.fract (u + c) = u + c := by
        rw [heq]
        simp
      rw [hfr'] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · rcases lt_or_ge (u + c) 1 with hlt1 | hge1
      · have hfr' : Int.fract (u + c) = u + c :=
          Int.fract_eq_self.2 ⟨hgt.le, hlt1⟩
        rw [hfr'] at h1 h2
        exact ⟨by linarith, by linarith⟩
      · exfalso
        have hfr' : Int.fract (u + c) = u + c - 1 := by
          have h1' : Int.fract (u + c - 1) = Int.fract (u + c) := Int.fract_sub_one (u + c)
          rw [← h1']
          exact Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
        rw [hfr'] at h1
        linarith

/-- The counting function is unchanged by a matched translation of the sequence and the
interval. -/
theorem countIn_add_const (x : ℕ → ℝ) {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hac : 0 < a + c) (hbc : b + c < 1) (N : ℕ) :
    countIn x a b N = countIn (fun n => x n + c) (a + c) (b + c) N := by
  classical
  unfold countIn
  refine congrArg Finset.card (Finset.filter_congr fun n _ => ?_)
  simpa using fract_mem_Ico_iff_add (y := x n) ha hb hac hbc

/-- The whole of `[0, 1)` catches every term. -/
theorem countIn_zero_one (x : ℕ → ℝ) (N : ℕ) : countIn x 0 1 N = N := by
  classical
  unfold countIn
  rw [Finset.filter_true_of_mem fun n _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    Finset.card_range]

/-- **The counting form of equidistribution for an arbitrary subinterval of `[0, 1]`**, including
intervals with an endpoint at `0` or at `1`. -/
theorem tendsto_countIn_div_of_le {x : ℕ → ℝ} (h : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  rcases eq_or_lt_of_le (show b - a ≤ 1 by linarith) with hlen | hlen
  · -- the full interval: `a = 0`, `b = 1`, and every term is counted
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst ha0; subst hb1
    have hcount : ∀ N : ℕ, (countIn x 0 1 N : ℝ) / N = if N = 0 then 0 else 1 := by
      intro N
      rw [countIn_zero_one]
      by_cases hN : N = 0
      · simp [hN]
      · rw [if_neg hN, div_self (by exact_mod_cast hN)]
    have : Tendsto (fun N : ℕ => if N = 0 then (0 : ℝ) else 1) atTop (𝓝 (1 - 0)) := by
      rw [show (1 : ℝ) - 0 = 1 by ring]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))
      filter_upwards [eventually_ge_atTop 1] with N hN
      have : N ≠ 0 := by omega
      simp [this]
    simpa [hcount] using this
  · -- a proper subinterval: rotate it into `(0, 1)`
    set c : ℝ := (1 - (b - a)) / 2 - a with hc
    have hac : 0 < a + c := by rw [hc]; linarith
    have hbc : b + c < 1 := by rw [hc]; linarith
    have habc : a + c < b + c := by linarith
    have hshift := tendsto_countIn_div (equidistributedMod1_add_const h c) hac habc hbc
    have heq : ∀ N : ℕ,
        (countIn (fun n => x n + c) (a + c) (b + c) N : ℝ) / N = (countIn x a b N : ℝ) / N := by
      intro N
      rw [countIn_add_const x ha hb hac hbc N]
    have hval : b + c - (a + c) = b - a := by ring
    rw [hval] at hshift
    exact hshift.congr heq

/-- **Weyl's theorem for quadratic sequences, for an arbitrary subinterval of `[0, 1]`.** -/
theorem tendsto_countIn_div_quadratic_of_le {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (countIn (fun n : ℕ => α * (n : ℝ) ^ 2) a b N : ℝ) / N) atTop
      (𝓝 (b - a)) :=
  tendsto_countIn_div_of_le (equidistributedMod1_quadratic hα) ha hab hb

end WeylCount

end RiemannHypothesis
