/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib

/-!
# The Kusmin–Landau inequality: the first-derivative test for exponential *sums*

`RiemannHypothesis.VanDerCorput` bounds an exponential *integral* whose phase moves fast enough.
This file does the same for an exponential *sum*, which is the form the theory of `ζ` actually
needs: the Dirichlet polynomial `∑_{n ≤ N} n^{-it}` is `∑ e(f(n))` with `f(x) = −(t/2π) log x`.

The classical statement is due to Kusmin and to Landau: if `f'` is monotone and stays at distance
at least `λ` from every integer, then

`|∑_{a < n ≤ b} e(f(n))| ≪ 1/λ`,

*with no dependence on the length of the range*.  It is the exact analogue of the first-derivative
test for integrals, and the starting point of van der Corput's method for sums.

## Main results

* `norm_sum_e2pi_le` — the inequality in its purely discrete form: for a sequence `u` whose
  consecutive differences `d i = u(i+1) − u(i)` are monotone and lie in `[λ, 1−λ]`,

      ‖∑_{j ≤ K} e(u j)‖ ≤ 1 + 2/λ.

  No calculus is involved; this is the combinatorial core.
* `norm_sum_e2pi_le_of_deriv` — the classical form: `f` twice differentiable on `[c, c+K]` with
  `f''` of constant sign (so `f'` monotone) and `λ ≤ f' ≤ 1 − λ` there gives

      ‖∑_{j ≤ K} e(f(c+j))‖ ≤ 1 + 2/λ.

* `norm_sum_e2pi_le_of_deriv_sub_int` — the same with `f'` in `[k+λ, k+1−λ]` for an *arbitrary*
  integer `k`, which is what "`f'` is at distance `≥ λ` from every integer" means in practice.
  The reduction is that `e(f(n) − k n) = e(f(n))`.

## Proof

Summation by parts against the amplitude `g i = 1/(e(d i) − 1)`.  Since
`e(u(i+1)) − e(u i) = e(u i)(e(d i) − 1)`, each term of the sum is
`e(u i) = g i · (e(u(i+1)) − e(u i))`, and Abel summation turns the sum into a boundary term plus
`∑ |g(i+1) − g i|`.  The identity

`1/(e(θ) − 1) = −1/2 − (i/2) cot(πθ)`

shows that the real part of `g` is constant, so `|g(i+1) − g i| = ½|cot(π d(i+1)) − cot(π d i)|`;
`cot(π·)` is antitone on `(0,1)` and `d` is monotone, so that sum telescopes.  Finally
`|cot(πθ)| ≤ 1/sin(πθ) ≤ 1/(2λ)` on `[λ, 1−λ]`, by Jordan's inequality.
-/

noncomputable section

open Complex Real Finset

namespace RiemannHypothesis

namespace KusminLandau

/-- `e(θ) = exp(2πiθ)`. -/
def e2pi (θ : ℝ) : ℂ := Complex.exp ((2 * Real.pi * θ : ℝ) * Complex.I)

/-- `cot(πθ)`. -/
def cotpi (θ : ℝ) : ℝ := Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ)

@[simp] theorem norm_e2pi (θ : ℝ) : ‖e2pi θ‖ = 1 := by
  simp [e2pi, Complex.norm_exp]

theorem e2pi_add (x y : ℝ) : e2pi (x + y) = e2pi x * e2pi y := by
  simp only [e2pi]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e` is unchanged by an integer shift of the argument. -/
theorem e2pi_sub_int (θ : ℝ) (k : ℤ) : e2pi (θ - k) = e2pi θ := by
  have h : e2pi (θ - k) * e2pi (k : ℝ) = e2pi θ := by
    rw [← e2pi_add]
    ring_nf
  have h1 : e2pi ((k : ℝ)) = 1 := by
    simp only [e2pi]
    rw [show ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul]
    simp [Complex.exp_two_pi_mul_I]
  rw [h1, mul_one] at h
  exact h

/-- The basic decomposition `e(θ) − 1 = 2 sin(πθ) · (−sin(πθ) + i cos(πθ))`. -/
theorem e2pi_sub_one_eq (θ : ℝ) :
    e2pi θ - 1 = (2 * Real.sin (Real.pi * θ) : ℂ) *
      ((-Real.sin (Real.pi * θ) : ℝ) + (Real.cos (Real.pi * θ) : ℝ) * Complex.I) := by
  have hkey : e2pi θ = (Real.cos (2 * Real.pi * θ) : ℂ)
      + (Real.sin (2 * Real.pi * θ) : ℂ) * Complex.I := by
    simp only [e2pi, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : Real.cos (2 * Real.pi * θ) = 1 - 2 * Real.sin (Real.pi * θ) ^ 2 := by
    have : (2 : ℝ) * Real.pi * θ = 2 * (Real.pi * θ) := by ring
    rw [this, Real.cos_two_mul']
    have := Real.sin_sq_add_cos_sq (Real.pi * θ)
    nlinarith [this]
  have hs : Real.sin (2 * Real.pi * θ)
      = 2 * Real.sin (Real.pi * θ) * Real.cos (Real.pi * θ) := by
    have : (2 : ℝ) * Real.pi * θ = 2 * (Real.pi * θ) := by ring
    rw [this, Real.sin_two_mul]
  rw [hkey, hc, hs]
  push_cast
  ring

theorem sin_pi_mul_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : 0 < Real.sin (Real.pi * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

theorem norm_e2pi_sub_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ‖e2pi θ - 1‖ = 2 * Real.sin (Real.pi * θ) := by
  have hs : 0 < Real.sin (Real.pi * θ) := sin_pi_mul_pos h0 h1
  rw [e2pi_sub_one_eq, norm_mul]
  have h2 : ‖(2 : ℂ) * ((Real.sin (Real.pi * θ) : ℝ) : ℂ)‖ = 2 * Real.sin (Real.pi * θ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    norm_num
  have h3 : ‖((-Real.sin (Real.pi * θ) : ℝ) : ℂ)
      + (Real.cos (Real.pi * θ) : ℝ) * Complex.I‖ = 1 := by
    rw [Complex.norm_add_mul_I]
    rw [show (-Real.sin (Real.pi * θ)) ^ 2 = Real.sin (Real.pi * θ) ^ 2 by ring]
    rw [Real.sin_sq_add_cos_sq]
    exact Real.sqrt_one
  rw [h2, h3, mul_one]

theorem e2pi_sub_one_ne_zero {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : e2pi θ - 1 ≠ 0 := by
  intro hcon
  have := norm_e2pi_sub_one h0 h1
  rw [hcon, norm_zero] at this
  have := sin_pi_mul_pos h0 h1
  linarith

/-- **The amplitude identity.**  `1/(e(θ) − 1) = −1/2 − (i/2) cot(πθ)`: the real part is the
constant `−1/2`, which is what makes the differences telescope. -/
theorem inv_e2pi_sub_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    (e2pi θ - 1)⁻¹ = -(1 / 2 : ℂ) - (Complex.I / 2) * (cotpi θ : ℂ) := by
  have hs : 0 < Real.sin (Real.pi * θ) := sin_pi_mul_pos h0 h1
  set S : ℂ := ((Real.sin (Real.pi * θ) : ℝ) : ℂ) with hS
  set C : ℂ := ((Real.cos (Real.pi * θ) : ℝ) : ℂ) with hC
  have hSne : S ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hpyth : S ^ 2 + C ^ 2 = 1 := by
    rw [hS, hC, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.sin_sq_add_cos_sq]
    norm_num
  have hcot : ((cotpi θ : ℝ) : ℂ) = C / S := by
    rw [cotpi, Complex.ofReal_div, hS, hC]
  have hfac : e2pi θ - 1 = 2 * S * (-S + C * Complex.I) := by
    rw [e2pi_sub_one_eq, hS, hC]
    push_cast
    ring
  have hprod : (-(1 / 2 : ℂ) - (Complex.I / 2) * (C / S)) * (e2pi θ - 1) = 1 := by
    rw [hfac]
    have expand : (-(1 / 2 : ℂ) - (Complex.I / 2) * (C / S)) * (2 * S * (-S + C * Complex.I))
        = S ^ 2 - Complex.I ^ 2 * C ^ 2 := by
      field_simp
      ring
    rw [expand, Complex.I_sq]
    linear_combination hpyth
  rw [hcot]
  exact inv_eq_of_mul_eq_one_left hprod

/-- Jordan's inequality on `[λ, 1−λ]`: `sin(πθ) ≥ 2λ`. -/
theorem two_mul_le_sin_pi_mul {θ lam : ℝ} (hlam : 0 < lam) (h0 : lam ≤ θ) (h1 : θ ≤ 1 - lam) :
    2 * lam ≤ Real.sin (Real.pi * θ) := by
  rcases le_total θ (1 / 2) with hle | hle
  · have hx0 : 0 ≤ Real.pi * θ := by
      have : 0 < θ := lt_of_lt_of_le hlam h0
      positivity
    have hx1 : Real.pi * θ ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    have hpi : 2 / Real.pi * (Real.pi * θ) = 2 * θ := by
      field_simp
    rw [hpi] at this
    linarith
  · have hsym : Real.sin (Real.pi * θ) = Real.sin (Real.pi * (1 - θ)) := by
      rw [show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring, Real.sin_pi_sub]
    rw [hsym]
    have hx0 : 0 ≤ Real.pi * (1 - θ) := by
      have : θ ≤ 1 := by linarith
      have : 0 ≤ 1 - θ := by linarith
      positivity
    have hx1 : Real.pi * (1 - θ) ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    have hpi : 2 / Real.pi * (Real.pi * (1 - θ)) = 2 * (1 - θ) := by
      field_simp
    rw [hpi] at this
    linarith

theorem abs_cotpi_le {θ lam : ℝ} (hlam : 0 < lam) (h0 : lam ≤ θ) (h1 : θ ≤ 1 - lam) :
    |cotpi θ| ≤ 1 / (2 * lam) := by
  have hsin : 2 * lam ≤ Real.sin (Real.pi * θ) := two_mul_le_sin_pi_mul hlam h0 h1
  have hspos : 0 < Real.sin (Real.pi * θ) := lt_of_lt_of_le (by linarith) hsin
  have hc : |Real.cos (Real.pi * θ)| ≤ 1 := Real.abs_cos_le_one _
  rw [cotpi, abs_div, abs_of_pos hspos]
  calc |Real.cos (Real.pi * θ)| / Real.sin (Real.pi * θ)
      ≤ 1 / Real.sin (Real.pi * θ) := by gcongr
    _ ≤ 1 / (2 * lam) := one_div_le_one_div_of_le (by linarith) hsin

/-- `cot(π ·)` is antitone on `(0,1)`. -/
theorem cotpi_antitone {x y : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hy1 : y < 1) :
    cotpi y ≤ cotpi x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hsx : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx0 hx1
  have hsy : 0 < Real.sin (Real.pi * y) := sin_pi_mul_pos hy0 hy1
  have key : ∀ z : ℝ, 0 < z → z < 1 → cotpi z = Real.tan (Real.pi / 2 - Real.pi * z) := by
    intro z hz0 hz1
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos]
    rw [cotpi]
    rw [inv_div]
  rw [key x hx0 hx1, key y hy0 hy1]
  apply Real.strictMonoOn_tan.monotoneOn
  · constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-! ## The inequality -/

/-- **The Kusmin–Landau inequality, discrete form.**  If the consecutive differences
`d i = u(i+1) − u(i)` of a sequence are monotone and lie in `[λ, 1−λ]`, then

`‖∑_{j ≤ K} e(u j)‖ ≤ 1 + 2/λ`,

a bound with no dependence on the number `K` of terms. -/
theorem norm_sum_e2pi_le {K : ℕ} {lam : ℝ} {u : ℕ → ℝ}
    (hlam : 0 < lam)
    (hlb : ∀ i, i < K → lam ≤ u (i + 1) - u i)
    (hub : ∀ i, i < K → u (i + 1) - u i ≤ 1 - lam)
    (hmono : (∀ i j, i ≤ j → j < K → u (i + 1) - u i ≤ u (j + 1) - u j) ∨
             (∀ i j, i ≤ j → j < K → u (j + 1) - u j ≤ u (i + 1) - u i)) :
    ‖∑ j ∈ Finset.range (K + 1), e2pi (u j)‖ ≤ 1 + 2 / lam := by
  have hpos : 0 < 2 / lam := by positivity
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [Finset.sum_range_one, norm_e2pi]
    linarith
  set d : ℕ → ℝ := fun i => u (i + 1) - u i with hd
  have hd0 : ∀ i, i < K → 0 < d i := fun i hi => lt_of_lt_of_le hlam (hlb i hi)
  have hd1 : ∀ i, i < K → d i < 1 := fun i hi => lt_of_le_of_lt (hub i hi) (by linarith)
  set w : ℕ → ℂ := fun j => e2pi (u j) with hw
  set g : ℕ → ℂ := fun i => (e2pi (d i) - 1)⁻¹ with hg
  have hwnorm : ∀ j, ‖w j‖ = 1 := fun j => norm_e2pi _
  have hwdiff : ∀ j k, ‖w j - w k‖ ≤ 2 := by
    intro j k
    calc ‖w j - w k‖ ≤ ‖w j‖ + ‖w k‖ := norm_sub_le _ _
      _ = 2 := by rw [hwnorm, hwnorm]; norm_num
  -- each term is `g i` times a difference
  have hstep : ∀ i, i < K → w i = g i * (w (i + 1) - w i) := by
    intro i hi
    have hne : e2pi (d i) - 1 ≠ 0 := e2pi_sub_one_ne_zero (hd0 i hi) (hd1 i hi)
    have hsucc : w (i + 1) = w i * e2pi (d i) := by
      simp only [hw, hd]
      rw [← e2pi_add]
      congr 1
      ring
    rw [hsucc]
    simp only [hg]
    field_simp
  have hsum : ∑ j ∈ Finset.range (K + 1), w j
      = w K + ∑ i ∈ Finset.range K, g i * (w (i + 1) - w i) := by
    rw [Finset.sum_range_succ, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_range.mp hi)
  -- summation by parts
  have habel : ∑ i ∈ Finset.range K, g i * (w (i + 1) - w i)
      = g (K - 1) * (w K - w 0)
        - ∑ i ∈ Finset.range (K - 1), (g (i + 1) - g i) * (w (i + 1) - w 0) := by
    have hbp := Finset.sum_range_by_parts g (fun i => w (i + 1) - w i) K
    simp only [smul_eq_mul] at hbp
    rw [hbp, Finset.sum_range_sub w K]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_range_sub w (i + 1)]
  -- the amplitude is small
  have hgnorm : ∀ i, i < K → ‖g i‖ ≤ 1 / (4 * lam) := by
    intro i hi
    have hsin : 2 * lam ≤ Real.sin (Real.pi * d i) :=
      two_mul_le_sin_pi_mul hlam (hlb i hi) (hub i hi)
    simp only [hg]
    rw [norm_inv, norm_e2pi_sub_one (hd0 i hi) (hd1 i hi), inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- the differences of the amplitude are a telescoping cotangent difference
  have hdg : ∀ i, i + 1 < K →
      ‖g (i + 1) - g i‖ = |cotpi (d (i + 1)) - cotpi (d i)| / 2 := by
    intro i hi
    have hi' : i < K := by omega
    have heq : g (i + 1) - g i
        = -(Complex.I / 2) * ((cotpi (d (i + 1)) - cotpi (d i) : ℝ) : ℂ) := by
      simp only [hg]
      rw [inv_e2pi_sub_one (hd0 (i + 1) hi) (hd1 (i + 1) hi),
        inv_e2pi_sub_one (hd0 i hi') (hd1 i hi')]
      push_cast
      ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [show ‖Complex.I / 2‖ = 1 / 2 by simp]
    ring
  have hcotbd : ∀ i, i < K → |cotpi (d i)| ≤ 1 / (2 * lam) :=
    fun i hi => abs_cotpi_le hlam (hlb i hi) (hub i hi)
  set ct : ℕ → ℝ := fun i => cotpi (d i) with hct
  have htel : ∑ i ∈ Finset.range (K - 1), ‖g (i + 1) - g i‖ ≤ 1 / (2 * lam) := by
    have hrw : ∑ i ∈ Finset.range (K - 1), ‖g (i + 1) - g i‖
        = (∑ i ∈ Finset.range (K - 1), |ct (i + 1) - ct i|) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi1 : i + 1 < K := by simp only [Finset.mem_range] at hi; omega
      exact hdg i hi1
    have hbd0 : |ct 0| ≤ 1 / (2 * lam) := hcotbd 0 hK
    have hbdn : |ct (K - 1)| ≤ 1 / (2 * lam) := hcotbd (K - 1) (by omega)
    have hB : (1 : ℝ) / (2 * lam) + 1 / (2 * lam) = 1 / lam := by
      field_simp
      ring
    have hkey : ∑ i ∈ Finset.range (K - 1), |ct (i + 1) - ct i| ≤ 1 / lam := by
      obtain ⟨h0a, h0b⟩ := abs_le.mp hbd0
      obtain ⟨hna, hnb⟩ := abs_le.mp hbdn
      rcases hmono with hinc | hdec
      · have habs : ∀ i ∈ Finset.range (K - 1),
            |ct (i + 1) - ct i| = ct i - ct (i + 1) := by
          intro i hi
          simp only [Finset.mem_range] at hi
          have hi1 : i + 1 < K := by omega
          have hle : ct (i + 1) ≤ ct i :=
            cotpi_antitone (hd0 i (by omega)) (hinc i (i + 1) (by omega) hi1) (hd1 (i + 1) hi1)
          rw [abs_of_nonpos (by linarith)]; ring
        rw [Finset.sum_congr rfl habs, Finset.sum_range_sub' ct (K - 1)]
        linarith
      · have habs : ∀ i ∈ Finset.range (K - 1),
            |ct (i + 1) - ct i| = ct (i + 1) - ct i := by
          intro i hi
          simp only [Finset.mem_range] at hi
          have hi1 : i + 1 < K := by omega
          have hle : ct i ≤ ct (i + 1) :=
            cotpi_antitone (hd0 (i + 1) hi1) (hdec i (i + 1) (by omega) hi1) (hd1 i (by omega))
          rw [abs_of_nonneg (by linarith)]
        rw [Finset.sum_congr rfl habs, Finset.sum_range_sub ct (K - 1)]
        linarith
    rw [hrw]
    linarith
  -- assembling the three pieces
  rw [hsum, habel]
  have h2 : ‖g (K - 1) * (w K - w 0)‖ ≤ 1 / (4 * lam) * 2 := by
    rw [norm_mul]
    exact mul_le_mul (hgnorm (K - 1) (by omega)) (hwdiff K 0) (norm_nonneg _) (by positivity)
  have h3 : ‖∑ i ∈ Finset.range (K - 1), (g (i + 1) - g i) * (w (i + 1) - w 0)‖
      ≤ 1 / (2 * lam) * 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ i ∈ Finset.range (K - 1), ‖(g (i + 1) - g i) * (w (i + 1) - w 0)‖
        ≤ ∑ i ∈ Finset.range (K - 1), ‖g (i + 1) - g i‖ * 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hwdiff _ _) (norm_nonneg _)
      _ = (∑ i ∈ Finset.range (K - 1), ‖g (i + 1) - g i‖) * 2 := by rw [Finset.sum_mul]
      _ ≤ 1 / (2 * lam) * 2 := by linarith
  have hfin : 1 / (4 * lam) * 2 + 1 / (2 * lam) * 2 ≤ 2 / lam := by
    have hgap : 2 / lam - (1 / (4 * lam) * 2 + 1 / (2 * lam) * 2) = 1 / (2 * lam) := by
      field_simp
      ring
    have : (0 : ℝ) < 1 / (2 * lam) := by positivity
    linarith
  calc ‖w K + (g (K - 1) * (w K - w 0)
          - ∑ i ∈ Finset.range (K - 1), (g (i + 1) - g i) * (w (i + 1) - w 0))‖
      ≤ ‖w K‖ + ‖g (K - 1) * (w K - w 0)
          - ∑ i ∈ Finset.range (K - 1), (g (i + 1) - g i) * (w (i + 1) - w 0)‖ :=
        norm_add_le _ _
    _ ≤ ‖w K‖ + (‖g (K - 1) * (w K - w 0)‖
          + ‖∑ i ∈ Finset.range (K - 1), (g (i + 1) - g i) * (w (i + 1) - w 0)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ 1 + (1 / (4 * lam) * 2 + 1 / (2 * lam) * 2) := by rw [hwnorm]; gcongr
    _ ≤ 1 + 2 / lam := by linarith

/-! ## The classical form -/

/-- **The Kusmin–Landau inequality, differentiable form.**  If `f` is differentiable on
`[c, c+K]` with `f'` monotone (or antitone) and `λ ≤ f' ≤ 1 − λ` there, then

`‖∑_{j ≤ K} e(f (c+j))‖ ≤ 1 + 2/λ`,

with no dependence on `K`.  The differences `f(c+i+1) − f(c+i)` are values of `f'` by the mean
value theorem, taken at points that increase with `i`, so they inherit both the bounds and the
monotonicity required by `norm_sum_e2pi_le`. -/
theorem norm_sum_e2pi_le_of_deriv {K : ℕ} {lam c : ℝ} {f f' : ℝ → ℝ}
    (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hlb : ∀ x ∈ Set.Icc c (c + K), lam ≤ f' x)
    (hub : ∀ x ∈ Set.Icc c (c + K), f' x ≤ 1 - lam)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))‖ ≤ 1 + 2 / lam := by
  -- the mean value theorem supplies, for each step, an interior point where `f'` is the difference
  have key : ∀ i : ℕ, ∃ x : ℝ, i < K →
      c + i < x ∧ x < c + i + 1 ∧ f' x = f (c + ((i : ℝ) + 1)) - f (c + i) := by
    intro i
    by_cases hi : i < K
    · have hsub : Set.Icc (c + i) (c + i + 1) ⊆ Set.Icc c (c + K) := by
        have hiK : (i : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hi
        intro x hx
        simp only [Set.mem_Icc] at hx ⊢
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      obtain ⟨x, hx, hfx⟩ :=
        exists_hasDerivAt_eq_slope f f' (a := c + i) (b := c + i + 1) (by linarith)
          (fun y hy => ((hf y (hsub hy)).continuousAt).continuousWithinAt)
          (fun y hy => hf y (hsub (Set.Ioo_subset_Icc_self hy)))
      refine ⟨x, fun _ => ⟨hx.1, hx.2, ?_⟩⟩
      rw [hfx]
      have : c + i + 1 - (c + i) = 1 := by ring
      rw [this, div_one]
      congr 2
      ring
    · exact ⟨0, fun h => absurd h hi⟩
  choose xi hxi using key
  have hmem : ∀ i, i < K → xi i ∈ Set.Icc c (c + K) := by
    intro i hi
    obtain ⟨h1, h2, _⟩ := hxi i hi
    have hiK : (i : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact ⟨by linarith, by linarith⟩
  have hdiff : ∀ i, i < K → f (c + ((i : ℕ) + 1 : ℕ)) - f (c + i) = f' (xi i) := by
    intro i hi
    obtain ⟨_, _, h3⟩ := hxi i hi
    rw [h3]
    push_cast
    ring_nf
  refine norm_sum_e2pi_le (u := fun j => f (c + j)) hlam ?_ ?_ ?_
  · intro i hi
    rw [hdiff i hi]
    exact hlb _ (hmem i hi)
  · intro i hi
    rw [hdiff i hi]
    exact hub _ (hmem i hi)
  · have hxmono : ∀ i j : ℕ, i ≤ j → j < K → xi i ≤ xi j := by
      intro i j hij hj
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · obtain ⟨_, h2, _⟩ := hxi i (by omega)
        obtain ⟨h1', _, _⟩ := hxi j hj
        have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
        linarith
    rcases hmono with h | h
    · left
      intro i j hij hj
      rw [hdiff i (by omega), hdiff j hj]
      exact h (hmem i (by omega)) (hmem j hj) (hxmono i j hij hj)
    · right
      intro i j hij hj
      rw [hdiff i (by omega), hdiff j hj]
      exact h (hmem i (by omega)) (hmem j hj) (hxmono i j hij hj)

/-- **The Kusmin–Landau inequality in the form actually used.**  The hypothesis "`f'` is at
distance at least `λ` from every integer" is, on an interval where `f'` is monotone, the statement
that `f'` lies in `[k + λ, k + 1 − λ]` for one integer `k`.  Subtracting the linear function
`k (x − c)`, which changes `e(f(c+j))` not at all because `k j` is an integer, reduces this to
`norm_sum_e2pi_le_of_deriv`. -/
theorem norm_sum_e2pi_le_of_deriv_sub_int {K : ℕ} {lam c : ℝ} {k : ℤ} {f f' : ℝ → ℝ}
    (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hlb : ∀ x ∈ Set.Icc c (c + K), (k : ℝ) + lam ≤ f' x)
    (hub : ∀ x ∈ Set.Icc c (c + K), f' x ≤ (k : ℝ) + 1 - lam)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))‖ ≤ 1 + 2 / lam := by
  set F : ℝ → ℝ := fun y => f y - (k : ℝ) * (y - c) with hFdef
  set F' : ℝ → ℝ := fun x => f' x - (k : ℝ) with hF'def
  have hFval : ∀ y, F y = f y - (k : ℝ) * (y - c) := fun y => rfl
  have hF'val : ∀ x, F' x = f' x - (k : ℝ) := fun x => rfl
  have hFd : ∀ x ∈ Set.Icc c (c + K), HasDerivAt F (F' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * (y - c)) ((k : ℝ) * 1) x :=
      ((hasDerivAt_id x).sub_const c).const_mul (k : ℝ)
    rw [mul_one] at h1
    rw [hF'val]
    exact (hf x hx).sub h1
  have hFlb : ∀ x ∈ Set.Icc c (c + K), lam ≤ F' x := by
    intro x hx; rw [hF'val]; linarith [hlb x hx]
  have hFub : ∀ x ∈ Set.Icc c (c + K), F' x ≤ 1 - lam := by
    intro x hx; rw [hF'val]; linarith [hub x hx]
  have hFmono : MonotoneOn F' (Set.Icc c (c + K)) ∨ AntitoneOn F' (Set.Icc c (c + K)) := by
    rcases hmono with h | h
    · exact Or.inl fun x hx y hy hxy => by
        rw [hF'val, hF'val]; linarith [h hx hy hxy]
    · exact Or.inr fun x hx y hy hxy => by
        rw [hF'val, hF'val]; linarith [h hx hy hxy]
  have hmain := norm_sum_e2pi_le_of_deriv (f := F) (f' := F') (c := c) (K := K)
    hlam hFd hFlb hFub hFmono
  have hEq : ∀ j : ℕ, e2pi (F (c + j)) = e2pi (f (c + j)) := by
    intro j
    rw [hFval]
    have hrw : f (c + j) - (k : ℝ) * (c + j - c) = f (c + j) - ((k * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [hrw, e2pi_sub_int]
  rwa [Finset.sum_congr rfl fun j _ => hEq j] at hmain

end KusminLandau

end RiemannHypothesis
