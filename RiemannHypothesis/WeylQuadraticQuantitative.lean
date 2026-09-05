/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylEquidistribution

/-!
# A quantitative Weyl bound for the quadratic exponential sum

`RiemannHypothesis.WeylQuadratic` proves Weyl's inequality for the phase `α n²` but leaves the
diophantine input to the caller: the bound is in terms of a lower bound `δ` for the distances
`‖2αk‖`, and `RiemannHypothesis.WeylEquidistribution` obtains such a `δ` from irrationality only
as an ineffective minimum over finitely many `k`, which yields `o(N)` and no rate.

This file supplies the diophantine input in its classical, effective form: from a rational
approximation `|2α − a/q| ≤ 1/q²` with `a` and `q` coprime, the multiples `2αk` with `2k ≤ q`
stay at distance at least `1/(2q)` from the integers, because `ak/q` is at distance at least
`1/q` and the perturbation is at most `k/q² ≤ 1/(2q)`.  Feeding this into Weyl's inequality with
`H = q/2` gives an explicit bound, and choosing `q` of size `√N` gives

    ‖∑_{0 ≤ n < N} e(α n²)‖ ≤ 7 N^(3/4).

## Main results

* `inv_le_intDist_intCast_div` — a non-integral fraction with denominator `q` is at distance at
  least `1/q` from the integers.
* `intDist_le_intDist_add_abs_sub` — the distance to the nearest integer is `1`-Lipschitz.
* `inv_two_mul_le_intDist_of_approx` — **the diophantine input**: `‖βk‖ ≥ 1/(2q)` for `2k ≤ q`,
  when `|β − a/q| ≤ 1/q²` with `gcd(a, q) = 1`.
* `normSq_quadSum_le_of_approx` — **the quantitative Weyl inequality**:
  `‖∑_{n<N} e(α n²)‖² ≤ 4 (N + q)(N + q²)/q`.
* `normSq_quadSum_le_of_approx_sqrt`, `norm_quadSum_pow_four_le_of_approx_sqrt`,
  `norm_quadSum_le_of_approx_sqrt` — the choice `N ≤ q² ≤ 4N`, giving `‖S‖⁴ ≤ 1600 N³` and
  `‖S‖ ≤ 7 N^(3/4)`.

## Scope

The exponent `3/4` is not the classical `1/2 + ε` of Weyl's inequality: reaching that needs the
counting lemma `∑_{k<H} min(N, 1/‖αk‖) ≪ (H/q + 1)(N + q log q)`, which is not formalized here.
The bound is also, as it must be, conditional on the existence of an approximation with a *large*
denominator `q`: for `α` close to a rational with small denominator there is no cancellation.
Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology

namespace RiemannHypothesis

namespace WeylQuadratic

open KusminLandau WeylEquidistribution

/-- The distance to the nearest integer is at most the distance to any integer. -/
theorem intDist_le_abs_sub_int (θ : ℝ) (j : ℤ) : intDist θ ≤ |θ - j| := by
  rcases eq_or_ne j (round θ) with rfl | hj
  · exact le_of_eq rfl
  · have hhalf : |θ - round θ| ≤ 1 / 2 := intDist_le_half θ
    have hone : (1 : ℝ) ≤ |(j : ℝ) - (round θ : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |j - round θ| := Int.one_le_abs (sub_ne_zero.2 hj)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|j - round θ| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at h2
    have htri : |(j : ℝ) - (round θ : ℝ)| ≤ |(j : ℝ) - θ| + |θ - (round θ : ℝ)| :=
      abs_sub_le _ _ _
    have hcomm : |(j : ℝ) - θ| = |θ - j| := abs_sub_comm _ _
    have : intDist θ = |θ - (round θ : ℝ)| := rfl
    rw [this]
    linarith

/-- A fraction with denominator `q` that is not an integer is at distance at least `1/q` from
the integers. -/
theorem inv_le_intDist_intCast_div {m : ℤ} {q : ℕ} (hq : 0 < q) (hdvd : ¬ ((q : ℤ) ∣ m)) :
    1 / (q : ℝ) ≤ intDist ((m : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set j : ℤ := round ((m : ℝ) / q) with hjdef
  have hne : m - j * q ≠ 0 := fun h => hdvd ⟨j, by linear_combination h⟩
  have h1 : (1 : ℝ) ≤ |(m : ℝ) - (j : ℝ) * q| := by
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|m - j * q| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hne
    rwa [Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] at h2
  have hsplit : (m : ℝ) / q - (j : ℝ) = ((m : ℝ) - (j : ℝ) * q) / q := by
    field_simp
  have hval : intDist ((m : ℝ) / q) = |(m : ℝ) - (j : ℝ) * q| / q := by
    rw [show intDist ((m : ℝ) / q) = |(m : ℝ) / q - (j : ℝ)| from rfl, hsplit, abs_div,
      abs_of_pos hqR]
  rw [hval]
  gcongr

/-- The distance to the nearest integer is `1`-Lipschitz. -/
theorem intDist_le_intDist_add_abs_sub (x y : ℝ) : intDist y ≤ intDist x + |x - y| := by
  have h1 : intDist y ≤ |y - (round x : ℝ)| := intDist_le_abs_sub_int y (round x)
  have h2 : |y - (round x : ℝ)| ≤ |y - x| + |x - (round x : ℝ)| := abs_sub_le _ _ _
  have h3 : |y - x| = |x - y| := abs_sub_comm _ _
  have h4 : intDist x = |x - (round x : ℝ)| := rfl
  linarith

/-- **The diophantine input to Weyl's inequality.**  If `|β − a/q| ≤ 1/q²` with `a` and `q`
coprime, then every multiple `βk` with `0 < 2k ≤ q` is at distance at least `1/(2q)` from the
integers. -/
theorem inv_two_mul_le_intDist_of_approx {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hcop : IsCoprime (q : ℤ) a) (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {k : ℤ} (hk0 : 0 < k) (hk : 2 * k ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ intDist (β * k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkq : (k : ℝ) ≤ (q : ℝ) / 2 := by
    have : (2 : ℝ) * k ≤ (q : ℝ) := by exact_mod_cast hk
    linarith
  -- `a k / q` is not an integer
  have hdvd : ¬ ((q : ℤ) ∣ a * k) := by
    intro h
    have hk' : (q : ℤ) ∣ k := hcop.dvd_of_dvd_mul_left h
    have := Int.le_of_dvd hk0 hk'
    omega
  have h1 : 1 / (q : ℝ) ≤ intDist (((a * k : ℤ) : ℝ) / q) :=
    inv_le_intDist_intCast_div hq hdvd
  -- the perturbation is at most `1/(2q)`
  have hpert : |β * k - ((a * k : ℤ) : ℝ) / q| ≤ 1 / (2 * (q : ℝ)) := by
    have hrw : β * k - ((a * k : ℤ) : ℝ) / q = (k : ℝ) * (β - (a : ℝ) / q) := by
      push_cast
      field_simp
    rw [hrw, abs_mul, abs_of_pos hkR]
    calc (k : ℝ) * |β - (a : ℝ) / q| ≤ ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) := by gcongr
      _ = 1 / (2 * (q : ℝ)) := by field_simp
  have hlip := intDist_le_intDist_add_abs_sub (β * k) (((a * k : ℤ) : ℝ) / q)
  have hhalf : 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  linarith

/-- **The quantitative Weyl inequality for a quadratic phase.**  From a rational approximation
`|2α − a/q| ≤ 1/q²` with coprime `a`, `q` and `q ≥ 4`, the quadratic exponential sum obeys
`‖∑_{n<N} e(α n²)‖² ≤ 4 (N + q)(N + q²)/q`. -/
theorem normSq_quadSum_le_of_approx {α : ℝ} {a : ℤ} {q : ℕ} (hq : 4 ≤ q)
    (hcop : IsCoprime (q : ℤ) a) (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℕ) :
    ‖quadSum α N‖ ^ 2 ≤ 4 * ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) / q := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  set H : ℕ := q / 2 with hHdef
  have hH : 0 < H := by omega
  have hHq : 2 * H ≤ q := by omega
  have hHq4 : q ≤ 4 * H := by omega
  have hδ : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
  have hbound : ∀ k : ℤ, 0 < k → k < (H : ℤ) → 1 / (2 * (q : ℝ)) ≤ intDist (2 * α * k) := by
    intro k hk0 hk
    have hHZ : (2 * H : ℤ) ≤ (q : ℤ) := by exact_mod_cast hHq
    exact inv_two_mul_le_intDist_of_approx hq0 hcop happ hk0 (by omega)
  have hkey := normSq_sum_e2pi_quadratic_le_of_le α (1 / (2 * (q : ℝ))) N H hH hδ hbound
  rw [quadSum]
  refine hkey.trans ?_
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1R : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH1 : 2 * (H : ℝ) ≤ (q : ℝ) := by exact_mod_cast hHq
  have hH2 : (q : ℝ) ≤ 4 * (H : ℝ) := by exact_mod_cast hHq4
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hA : (N : ℝ) + H - 1 ≤ (N : ℝ) + q := by linarith
  have hBeq : ((H : ℝ) - 1) / (1 / (2 * (q : ℝ))) = ((H : ℝ) - 1) * (2 * (q : ℝ)) := by
    field_simp
  have hB : (N : ℝ) + ((H : ℝ) - 1) / (1 / (2 * (q : ℝ))) ≤ (N : ℝ) + (q : ℝ) ^ 2 := by
    rw [hBeq]
    nlinarith
  have hBnn : (0 : ℝ) ≤ (N : ℝ) + ((H : ℝ) - 1) / (1 / (2 * (q : ℝ))) := by
    rw [hBeq]; nlinarith
  have hnum : ((N : ℝ) + H - 1) * ((N : ℝ) + ((H : ℝ) - 1) / (1 / (2 * (q : ℝ))))
      ≤ ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) :=
    mul_le_mul hA hB hBnn (by linarith)
  calc ((N : ℝ) + H - 1) * ((N : ℝ) + ((H : ℝ) - 1) / (1 / (2 * (q : ℝ)))) / H
      ≤ ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) / H := by gcongr
    _ ≤ 4 * ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) / q := by
        have hP : (0 : ℝ) ≤ ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) := by positivity
        rw [div_le_div_iff₀ hHR hqR]
        nlinarith [mul_le_mul_of_nonneg_left hH2 hP]

/-- With an approximation whose denominator is of the size of `√N`, the quadratic Weyl sum is
`O(N^(3/4))`, in the square form. -/
theorem normSq_quadSum_le_of_approx_sqrt {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 16 ≤ N)
    (hcop : IsCoprime (q : ℤ) a) (hq1 : (N : ℝ) ≤ (q : ℝ) ^ 2) (hq2 : (q : ℝ) ^ 2 ≤ 4 * N)
    (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖quadSum α N‖ ^ 2 ≤ 40 * (N : ℝ) * Real.sqrt N := by
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast hN
  set s : ℝ := Real.sqrt N with hsdef
  have hs2 : s ^ 2 = N := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs4 : 4 ≤ s := by nlinarith
  have hqR0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqs : s ≤ (q : ℝ) := by nlinarith
  have hq4 : 4 ≤ q := by
    have : (4 : ℝ) ≤ (q : ℝ) := le_trans hs4 hqs
    exact_mod_cast this
  have hq2s : (q : ℝ) ≤ 2 * s := by nlinarith
  have hqR : (0 : ℝ) < q := by linarith
  refine (normSq_quadSum_le_of_approx hq4 hcop happ N).trans ?_
  rw [div_le_iff₀ hqR, ← hs2]
  have hA : s ^ 2 + (q : ℝ) ≤ s ^ 2 + 2 * s := by linarith
  have hB : s ^ 2 + (q : ℝ) ^ 2 ≤ 5 * s ^ 2 := by nlinarith
  have hC : (0 : ℝ) ≤ s ^ 2 + (q : ℝ) ^ 2 := by positivity
  have hD : (0 : ℝ) ≤ s ^ 2 + 2 * s := by nlinarith
  have hprod : (s ^ 2 + (q : ℝ)) * (s ^ 2 + (q : ℝ) ^ 2) ≤ (s ^ 2 + 2 * s) * (5 * s ^ 2) :=
    mul_le_mul hA hB hC hD
  have h1 : (0 : ℝ) ≤ s ^ 3 * ((q : ℝ) - s) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : (0 : ℝ) ≤ s ^ 3 * (s - 2) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- The same bound with no square root: `‖∑_{n<N} e(α n²)‖⁴ ≤ 1600 N³`. -/
theorem norm_quadSum_pow_four_le_of_approx_sqrt {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 16 ≤ N)
    (hcop : IsCoprime (q : ℤ) a) (hq1 : (N : ℝ) ≤ (q : ℝ) ^ 2) (hq2 : (q : ℝ) ^ 2 ≤ 4 * N)
    (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖quadSum α N‖ ^ 4 ≤ 1600 * (N : ℝ) ^ 3 := by
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have h := normSq_quadSum_le_of_approx_sqrt hN hcop hq1 hq2 happ
  have hsq : (‖quadSum α N‖ ^ 2) ^ 2 ≤ (40 * (N : ℝ) * Real.sqrt N) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h 2
  calc ‖quadSum α N‖ ^ 4 = (‖quadSum α N‖ ^ 2) ^ 2 := by ring
    _ ≤ (40 * (N : ℝ) * Real.sqrt N) ^ 2 := hsq
    _ = 1600 * (N : ℝ) ^ 3 := by
        have : (40 * (N : ℝ) * Real.sqrt N) ^ 2 = 1600 * (N : ℝ) ^ 2 * Real.sqrt N ^ 2 := by ring
        rw [this, hs2]; ring

/-- **`∑_{0 ≤ n < N} e(α n²) = O(N^(3/4))`**, for a coefficient with a rational approximation of
denominator of the size of `√N`. -/
theorem norm_quadSum_le_of_approx_sqrt {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 16 ≤ N)
    (hcop : IsCoprime (q : ℤ) a) (hq1 : (N : ℝ) ≤ (q : ℝ) ^ 2) (hq2 : (q : ℝ) ^ 2 ≤ 4 * N)
    (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖quadSum α N‖ ≤ 7 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h4 := norm_quadSum_pow_four_le_of_approx_sqrt hN hcop hq1 hq2 happ
  have hpow : (7 * (N : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = 2401 * (N : ℝ) ^ 3 := by
    have hx : ((N : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) = (N : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul hN0]
      norm_num
    rw [mul_pow, hx]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
  rw [hpow]
  nlinarith [pow_nonneg hN0 3]

end WeylQuadratic

end RiemannHypothesis
