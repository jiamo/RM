/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.FourthMoment
import RiemannHypothesis.Mollifier

/-!
# The mean-square weight of the mollifier tail coefficients

The density theorems of Carlson and Ingham compare `ζ` with a mollifier
`M_y(s) = ∑_{n ≤ y} μ(n) n^{-s}`; the point of the comparison is that the coefficients
`c_y(n) = ∑_{d ∣ n, d ≤ y} μ(d)` of `ζ M_y` vanish for `2 ≤ n ≤ y`
(`RiemannHypothesis.Mollifier.detectCoeff_eq_zero_of_le`), so that `ζ M_y - 1` is a Dirichlet
series supported on `n > y`.  Any mean value theorem then produces the *mean-square weight*
of those tail coefficients on the line `re s = σ`,

`∑_{n > y} |c_y(n)|² n^{-2σ}`,

and the whole argument rests on this quantity being small for large `y`.  This file proves
exactly that, for every `σ > 1/2`.

## Main results

* `summable_divisorCount_sq_rpow` : `∑_n d(n)² n^{-a}` converges for every `a > 1`.  The proof
  is elementary and avoids the divisor bound `d(n) = O_ε(n^ε)`: from the injection
  `v ↦ (gcd u v, v / gcd u v)` one gets `d(n) ≤ d(u) d(n/u)` for every `u ∣ n`, hence
  `d(n)² ≤ ∑_{u ∣ n} d(u) d(n/u) = d₄(n)`, and `∑ d₄(n) n^{-a} < ∞` for `a > 1` because `d₄`
  is the Dirichlet convolution of two absolutely convergent series (its sum is `ζ(a)⁴`).
* `norm_detectCoeff_le_divisorCount` : `|c_y(n)| ≤ d(n)`.
* `exists_tsum_normSq_tailCoeff_lt` : for `σ > 1/2` and `ε > 0` there is a mollifier length
  `y` with `∑_{n > y} |c_y(n)|² n^{-2σ} < ε`.

Nothing here is conditional, and nothing here uses the Riemann hypothesis.

## Scope

This is the coefficient side of the density estimate only.  Turning it into a bound for
`N(σ, T)` needs, in addition, a mean value theorem transferring `∑_{n > y} |c_y(n)|² n^{-2σ}`
to `(1/T) ∫₀ᵀ |ζ M_y - 1|²` (Carlson's mean value theorem, or a Dirichlet-polynomial
approximation of `ζ` in the strip), which is not formalized here.
-/

noncomputable section

open Complex Filter Topology ArithmeticFunction Finset

namespace RiemannHypothesis

/-! ## `d(n) ≤ d(u) d(n/u)` for `u ∣ n` -/

/-- For `u ∣ n` and `v ∣ n`, the splitting `v = gcd(u, v) · (v / gcd(u, v))` has its second
factor dividing `n / u`, because `u · (v / gcd(u,v)) = lcm(u, v)` divides `n`. -/
theorem div_gcd_dvd_div_of_dvd {n u v : ℕ} (hu : u ∣ n) (hv : v ∣ n) :
    v / Nat.gcd u v ∣ n / u := by
  have hg : Nat.gcd u v ∣ v := Nat.gcd_dvd_right u v
  have key : u * (v / Nat.gcd u v) ∣ n := by
    have h : u * (v / Nat.gcd u v) = Nat.lcm u v := by
      rw [Nat.lcm, Nat.mul_div_assoc u hg]
    rw [h]
    exact Nat.lcm_dvd hu hv
  exact (Nat.dvd_div_iff_mul_dvd hu).mpr key

/-- **Sub-multiplicativity of the divisor function.**  If `u ∣ n` and `n ≠ 0` then
`d(n) ≤ d(u) · d(n / u)`: the map `v ↦ (gcd(u, v), v / gcd(u, v))` injects the divisors of `n`
into the pairs (divisor of `u`, divisor of `n/u`). -/
theorem divisorCount_le_mul_of_dvd {n u : ℕ} (hn : n ≠ 0) (hu : u ∣ n) :
    divisorCount n ≤ divisorCount u * divisorCount (n / u) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hu)
  have hnu0 : n / u ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hu0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hu⟩
  have hcard := Finset.card_le_card_of_injOn (s := n.divisors)
    (t := u.divisors ×ˢ (n / u).divisors) (fun v => (Nat.gcd u v, v / Nat.gcd u v)) ?_ ?_
  · simpa [divisorCount, Finset.card_product] using hcard
  · intro v hv
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at hv ⊢
    exact ⟨⟨Nat.gcd_dvd_left u v, hu0⟩, ⟨div_gcd_dvd_div_of_dvd hu hv.1, hnu0⟩⟩
  · intro v1 _ v2 _ heq
    simp only [Prod.mk.injEq] at heq
    have e1 : Nat.gcd u v1 * (v1 / Nat.gcd u v1) = v1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right u v1)
    have e2 : Nat.gcd u v2 * (v2 / Nat.gcd u v2) = v2 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right u v2)
    rw [← e1, ← e2, heq.2, heq.1]

/-! ## The four-fold divisor function -/

/-- The four-fold divisor function `d₄ = d * d` (Dirichlet convolution). -/
def divisorCount4 (n : ℕ) : ℕ :=
  ∑ p ∈ n.divisorsAntidiagonal, divisorCount p.1 * divisorCount p.2

/-- `d(n)² ≤ d₄(n)`: sum the sub-multiplicativity bound over the divisors of `n`. -/
theorem divisorCount_sq_le_divisorCount4 (n : ℕ) :
    divisorCount n ^ 2 ≤ divisorCount4 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [divisorCount, divisorCount4]
  · rw [divisorCount4, Nat.sum_divisorsAntidiagonal (fun a b => divisorCount a * divisorCount b)]
    calc divisorCount n ^ 2 = ∑ _u ∈ n.divisors, divisorCount n := by
          rw [Finset.sum_const, smul_eq_mul, sq, divisorCount]
      _ ≤ ∑ u ∈ n.divisors, divisorCount u * divisorCount (n / u) :=
          Finset.sum_le_sum fun _ hu => divisorCount_le_mul_of_dvd hn (Nat.dvd_of_mem_divisors hu)

/-- `d₄` is the Dirichlet convolution of the divisor counting function with itself. -/
theorem convolution_divisorCount (n : ℕ) :
    LSeries.convolution (fun m => (divisorCount m : ℂ)) (fun m => (divisorCount m : ℂ)) n
      = (divisorCount4 n : ℂ) := by
  rw [LSeries.convolution_def, divisorCount4]
  push_cast
  rfl

/-- The Dirichlet series of `d₄` converges absolutely for `re s > 1`. -/
theorem lseriesSummable_divisorCount4 {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorCount4 n : ℂ)) s := by
  have h := (lseriesSummable_divisorCount hs).convolution (lseriesSummable_divisorCount hs)
  exact (LSeriesSummable_congr s fun {n} _ => (convolution_divisorCount n)).mp h

/-! ## Summability of `∑ d(n)² n^{-a}` for `a > 1` -/

/-- `∑_n d₄(n) n^{-a}` converges for every `a > 1`. -/
theorem summable_divisorCount4_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ => (divisorCount4 (n + 1) : ℝ) * ((n : ℝ) + 1) ^ (-a) := by
  have hre : 1 < ((a : ℝ) : ℂ).re := by simpa using ha
  exact summable_shift_rpow_of_lseriesSummable (a := fun n => (divisorCount4 n : ℝ))
    ((lseriesSummable_divisorCount4 hre).congr fun n => by push_cast; ring)

/-- **`∑_n d(n)² n^{-a}` converges for every `a > 1`.** -/
theorem summable_divisorCount_sq_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a) := by
  refine (summable_divisorCount4_rpow ha).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-a) := Real.rpow_nonneg (by positivity) _
  have hle : ((divisorCount (n + 1) : ℝ)) ^ 2 ≤ (divisorCount4 (n + 1) : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (divisorCount_sq_le_divisorCount4 (n + 1))
  exact mul_le_mul_of_nonneg_right hle hpow

/-! ## The mollifier tail coefficients -/

/-- The coefficients of `ζ M_y` are bounded by the divisor function: `|c_y(n)| ≤ d(n)`. -/
theorem norm_detectCoeff_le_divisorCount (y n : ℕ) :
    ‖Mollifier.detectCoeff y n‖ ≤ divisorCount n := by
  classical
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ n.divisors.filter (fun d => d ≤ y), ‖((moebius d : ℤ) : ℂ)‖
      ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ y), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        have : |(moebius d : ℤ)| ≤ 1 := abs_moebius_le_one
        calc ‖((moebius d : ℤ) : ℂ)‖ = |(moebius d : ℤ)| := by
              rw [show ((moebius d : ℤ) : ℂ) = ((((moebius d : ℤ) : ℝ)) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
          _ ≤ 1 := by exact_mod_cast this
    _ = (n.divisors.filter (fun d => d ≤ y)).card := by simp
    _ ≤ divisorCount n := by
        have h : (n.divisors.filter (fun d => d ≤ y)).card ≤ divisorCount n :=
          Finset.card_filter_le _ _
        exact_mod_cast h

/-- The tail coefficients of `ζ M_y` are bounded by the divisor function. -/
theorem norm_tailCoeff_le_divisorCount (y n : ℕ) :
    ‖Mollifier.tailCoeff y n‖ ≤ divisorCount n := by
  rw [Mollifier.tailCoeff]
  split
  · exact norm_detectCoeff_le_divisorCount y n
  · simp

/-- The mean-square weight of the tail coefficients on the line `re s = σ` is summable, for
every `σ > 1/2`. -/
theorem summable_normSq_tailCoeff {σ : ℝ} (hσ : 1 / 2 < σ) (y : ℕ) :
    Summable fun n : ℕ =>
      ‖Mollifier.tailCoeff y (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) := by
  have ha : 1 < 2 * σ := by linarith
  refine (summable_divisorCount_sq_rpow ha).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
  refine mul_le_mul_of_nonneg_right ?_ hpow
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_tailCoeff_le_divisorCount y (n + 1)) 2

/-- **The tail of `∑ d(n)² n^{-2σ}` beyond `y` tends to `0`.**  For every `σ > 1/2` and every
`ε > 0` there is a length `y ≥ 1` with `∑_{n > y} d(n)² n^{-2σ} < ε`. -/
theorem exists_tsum_divisorCount_sq_tail_lt {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧
      ∑' n : ℕ, (divisorCount (n + y + 1) : ℝ) ^ 2 * (((n + y : ℕ) : ℝ) + 1) ^ (-(2 * σ)) < ε := by
  have ha : 1 < 2 * σ := by linarith
  set g : ℕ → ℝ := fun n => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) with hg
  have hgsum : Summable g := summable_divisorCount_sq_rpow ha
  have htail : Tendsto (fun y : ℕ => ∑' n : ℕ, g (n + y)) atTop (𝓝 0) :=
    tendsto_sum_nat_add g
  obtain ⟨y₀, hy₀⟩ := (htail.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨y₀ + 1, by omega, ?_⟩
  have hshift : ∀ n : ℕ, g (n + (y₀ + 1))
      = (divisorCount (n + (y₀ + 1) + 1) : ℝ) * (divisorCount (n + (y₀ + 1) + 1) : ℝ)
        * (((n + (y₀ + 1) : ℕ) : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [hg]
    ring
  have := hy₀ (y₀ + 1) (by omega)
  calc ∑' n : ℕ, (divisorCount (n + (y₀ + 1) + 1) : ℝ) ^ 2
          * (((n + (y₀ + 1) : ℕ) : ℝ) + 1) ^ (-(2 * σ))
      = ∑' n : ℕ, g (n + (y₀ + 1)) := by
        refine tsum_congr fun n => ?_
        rw [hshift n]
        ring
    _ < ε := this

/-- **The mean-square weight of the tail coefficients is small for a long mollifier.**  For
every `σ > 1/2` and every `ε > 0` there is a length `y ≥ 1` with
`∑_{n > y} |c_y(n)|² n^{-2σ} < ε`.  (The sum is written over all `n`, the coefficients
`tailCoeff y n` vanishing for `n ≤ y`.) -/
theorem exists_tsum_normSq_tailCoeff_lt {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧
      ∑' n : ℕ, ‖Mollifier.tailCoeff y (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) < ε := by
  have ha : 1 < 2 * σ := by linarith
  set g : ℕ → ℝ := fun n => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) with hg
  have hgsum : Summable g := summable_divisorCount_sq_rpow ha
  have htail : Tendsto (fun y : ℕ => ∑' n : ℕ, g (n + y)) atTop (𝓝 0) :=
    tendsto_sum_nat_add g
  obtain ⟨y₀, hy₀⟩ := (htail.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨y₀ + 1, by omega, ?_⟩
  set y := y₀ + 1 with hy
  set h : ℕ → ℝ := fun n => ‖Mollifier.tailCoeff y (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ))
    with hh
  have hhsum : Summable h := summable_normSq_tailCoeff hσ y
  have hle : ∀ n, h n ≤ g n := by
    intro n
    have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_tailCoeff_le_divisorCount y (n + 1)) 2) hpow
  have hzero : ∀ n < y₀, h n = 0 := by
    intro n hn
    have : Mollifier.tailCoeff y (n + 1) = 0 := by
      rw [Mollifier.tailCoeff, if_neg]
      omega
    simp [hh, this]
  have hsplit : ∑' n, h n = ∑ n ∈ Finset.range y₀, h n + ∑' n, h (n + y₀) :=
    (hhsum.sum_add_tsum_nat_add y₀).symm
  have hfirst : ∑ n ∈ Finset.range y₀, h n = 0 :=
    Finset.sum_eq_zero fun n hn => hzero n (Finset.mem_range.mp hn)
  have hcmp : ∑' n, h (n + y₀) ≤ ∑' n, g (n + y₀) :=
    Summable.tsum_le_tsum (fun n => hle (n + y₀)) ((summable_nat_add_iff y₀).mpr hhsum)
      ((summable_nat_add_iff y₀).mpr hgsum)
  have := hy₀ y₀ le_rfl
  calc ∑' n, h n = ∑' n, h (n + y₀) := by rw [hsplit, hfirst, zero_add]
    _ ≤ ∑' n, g (n + y₀) := hcmp
    _ < ε := this

end RiemannHypothesis
