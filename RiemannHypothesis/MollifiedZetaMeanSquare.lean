/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MollifiedMeanSquare
import RiemannHypothesis.GaussianMeanValue
import RiemannHypothesis.StripMeanSquareUniform

/-!
# The mean square of `ζ M_y − 1` inside the critical strip

`RiemannHypothesis/MollifiedMeanSquare.lean` bounds the mean square of `M_y P_K − 1`, where
`P_K(s) = ∑_{k ≤ K} k^{-s}` is the truncated zeta sum: a statement about *Dirichlet
polynomials* only.  `RiemannHypothesis/StripMeanSquareBohrLandau.lean` bounds `ζ − P_K` by
Euler–Maclaurin to order `m`.  This file joins the two: it replaces `P_K` by `ζ` and so gives
the mean square of `ζ M_y − 1` on a vertical segment inside the strip, uniformly in the
abscissa.  That is the analytic input of the Carlson density theorem.

## The mechanism

Write `ζ M_y − 1 = (M_y P_K − 1) + M_y (ζ − P_K)` and choose the length `K` of the truncation
as a fixed power `b^α` of the height `b`, with

`α = (1 + 1 / (3/2 − σ₀)) / 2 ∈ (1, 1 / (3/2 − σ₀))`.

* For the first term the *Montgomery–Vaughan shape* of the mean value theorem is essential:
  `RiemannHypothesis/GaussianMeanValue.lean` puts the error term inside the sum, so the
  polynomial may be as long as `y K ≈ b^α` and still contribute
  `∑_{m ≤ yK} d(m)² m^{1−2σ} ≪ (yK)^{3/2−σ₀} = o(b)`, because `α (3/2 − σ₀) < 1`.  The
  elementary mean value theorem, whose error `8 N (1 + log N)` sits outside the sum, forces
  `K ≪ b / log b` and is useless here.
* For the second term Euler–Maclaurin of order `m` gives
  `‖ζ − P_K‖ ≤ (K+1)^{1−σ} / ‖s − 1‖ + C (K^{−σ} + (σ + |t| + m)^m K^{1−σ−m})`.
  Since `K ≥ b^α` with `α > 1`, the last term is `≪ b^{m + α(1−σ₀) − α m}`, which is `o(1)`
  once `m` is large enough, and the first is `≪ K^{1−σ₀} / |t|`, whose square integrates to
  `O(K^{2−2σ₀}) = o(b)`.

## Main results

* `exists_sum_divisorCount_sq_mul_le` : `∑_{m ≤ M} d(m)² m^{1−2σ} ≤ S M^{3/2−σ₀}` for
  `σ ≥ σ₀ > 1/2`, an elementary consequence of the convergence of `∑ d(m)² m^{-2σ'}`.
* `integral_normSq_mollified_partialSum_sub_one_le_mv` : the Montgomery–Vaughan shape of the
  mean square of `M_y P_K − 1`.
* `exists_integral_normSq_zeta_sub_partialSum_le` : the mean square of `ζ − P_K` for
  `K = ⌈b^α⌉` is `o(b)`.
* `exists_integral_normSq_zeta_mul_mollifier_sub_one_le` : **for every `σ₀ > 1/2` and every
  `ε > 0` there is a mollifier length `y` and a height `b₀` such that**
  `∫_a^b ‖ζ M_y − 1‖² dt ≤ ε b` for all `1 ≤ a ≤ b`, `b ≥ b₀`, uniformly for `σ₀ ≤ σ ≤ 6`.

Nothing here is conditional.  No zero-density estimate is claimed in this file; the counting
is done in `RiemannHypothesis/CarlsonDensity.lean`.
-/

noncomputable section

open Complex MeasureTheory Finset

namespace RiemannHypothesis

open scoped ArithmeticFunction.Moebius

/-! ## Elementary bounds on the mollifier -/

/-- The mollifier is bounded by its length on the closed half-plane `re s ≥ 0`. -/
theorem norm_mollifier_le_length (y : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Mollifier.mollifier y s‖ ≤ y := by
  classical
  rw [Mollifier.mollifier]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 y, ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ (1 : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hmu : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      have h : |(μ n : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      calc ‖((μ n : ℤ) : ℂ)‖ = |(μ n : ℤ)| := by
            rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        _ ≤ 1 := by exact_mod_cast h
    have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
    calc ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ = ‖((μ n : ℤ) : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖ := norm_mul _ _
      _ ≤ 1 * 1 := by
          refine mul_le_mul hmu hpow (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc ∑ n ∈ Finset.Icc 1 y, ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ ∑ _n ∈ Finset.Icc 1 y, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (y : ℝ) := by simp

/-! ## The weighted divisor sum -/

/-- **`∑_{m ≤ M} d(m)² m^{1−2σ} ≤ S M^{3/2−σ₀}`** for every `σ ≥ σ₀ > 1/2`.  Only the
convergence of `∑ d(m)² m^{-2σ'}` for `σ' = (σ₀ + 1/2)/2 > 1/2` is used. -/
theorem exists_sum_divisorCount_sq_mul_le {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) (hσ₀1 : σ₀ < 1) :
    ∃ S : ℝ, 0 < S ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ M : ℕ,
      ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
        ≤ S * (M : ℝ) ^ (3 / 2 - σ₀) := by
  classical
  set a : ℝ := σ₀ + 1 / 2 with ha
  have ha1 : 1 < a := by rw [ha]; linarith
  set g : ℕ → ℝ := fun n => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a) with hg
  have hgsum : Summable g := summable_divisorCount_sq_rpow ha1
  have hgnn : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-a) := Real.rpow_nonneg (by positivity) _
    rw [hg]; positivity
  set S : ℝ := (∑' n : ℕ, g n) + 1 with hS
  have hSpos : 0 < S := by
    have : 0 ≤ ∑' n : ℕ, g n := tsum_nonneg hgnn
    rw [hS]; linarith
  refine ⟨S, hSpos, fun σ hσ M => ?_⟩
  have hMnn : (0 : ℝ) ≤ (M : ℝ) ^ (3 / 2 - σ₀) := Real.rpow_nonneg (by positivity) _
  -- termwise bound
  have hstep : ∀ m ∈ Finset.Icc 1 M,
      (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
        ≤ ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)) * (M : ℝ) ^ (3 / 2 - σ₀) := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hmM' : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    have e1 : (m : ℝ) ^ (-2 * σ) * (m : ℝ) = (m : ℝ) ^ (1 - 2 * σ) := by
      rw [show (1 : ℝ) - 2 * σ = -2 * σ + 1 by ring, Real.rpow_add hm0, Real.rpow_one]
    have e2 : (m : ℝ) ^ (-a) * (m : ℝ) ^ (a - 2 * σ + 1) = (m : ℝ) ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add hm0]
      ring_nf
    have hexp : (m : ℝ) ^ (a - 2 * σ + 1) ≤ (M : ℝ) ^ (3 / 2 - σ₀) := by
      have hle : a - 2 * σ + 1 ≤ 3 / 2 - σ₀ := by rw [ha]; linarith
      have h1 : (m : ℝ) ^ (a - 2 * σ + 1) ≤ (m : ℝ) ^ (3 / 2 - σ₀) :=
        Real.rpow_le_rpow_of_exponent_le hm1' hle
      have h2 : (m : ℝ) ^ (3 / 2 - σ₀) ≤ (M : ℝ) ^ (3 / 2 - σ₀) :=
        Real.rpow_le_rpow (by linarith) hmM' (by linarith)
      linarith
    have hpowa : (0 : ℝ) < (m : ℝ) ^ (-a) := Real.rpow_pos_of_pos hm0 _
    have hd : (0 : ℝ) ≤ (divisorCount m : ℝ) ^ 2 := by positivity
    calc (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
        = (divisorCount m : ℝ) ^ 2 * ((m : ℝ) ^ (-2 * σ) * (m : ℝ)) := by ring
      _ = (divisorCount m : ℝ) ^ 2 * ((m : ℝ) ^ (-a) * (m : ℝ) ^ (a - 2 * σ + 1)) := by
          rw [e1, e2]
      _ ≤ (divisorCount m : ℝ) ^ 2 * ((m : ℝ) ^ (-a) * (M : ℝ) ^ (3 / 2 - σ₀)) := by
          refine mul_le_mul_of_nonneg_left ?_ hd
          exact mul_le_mul_of_nonneg_left hexp hpowa.le
      _ = ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)) * (M : ℝ) ^ (3 / 2 - σ₀) := by ring
  -- the sum of the weights is at most `S`
  have hweights : ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a) ≤ S := by
    have hrw : ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)
        = ∑ n ∈ Finset.range M, g n := by
      refine Finset.sum_nbij' (i := fun m => m - 1) (j := fun n => n + 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        simp only [Finset.mem_range]
        omega
      · intro n hn
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Icc]
        omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        omega
      · intro n _
        omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        have e1 : m - 1 + 1 = m := by omega
        have e2 : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
          have h : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℝ) := by
            exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) e1
          push_cast at h ⊢
          linarith
        rw [hg]
        simp only
        rw [e1, e2]
    rw [hrw, hS]
    have hle : ∑ n ∈ Finset.range M, g n ≤ ∑' n : ℕ, g n :=
      Summable.sum_le_tsum _ (fun i _ => hgnn i) hgsum
    linarith
  calc ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a))
          * (M : ℝ) ^ (3 / 2 - σ₀) := Finset.sum_le_sum hstep
    _ = (∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a))
          * (M : ℝ) ^ (3 / 2 - σ₀) := by rw [← Finset.sum_mul]
    _ ≤ S * (M : ℝ) ^ (3 / 2 - σ₀) := mul_le_mul_of_nonneg_right hweights hMnn

/-- The tail `∑_{m > y} d(m)² m^{-2σ}` is monotone in the abscissa: the bound obtained at
`σ₀` applies at every `σ ≥ σ₀`. -/
theorem sum_Ioc_divisorCount_sq_le_of_le {σ₀ σ : ℝ} (hσ : σ₀ ≤ σ) (y M : ℕ) :
    ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₀) := by
  refine Finset.sum_le_sum fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hpow : (m : ℝ) ^ (-2 * σ) ≤ (m : ℝ) ^ (-2 * σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hm1' (by linarith)
  have hd : (0 : ℝ) ≤ (divisorCount m : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hpow hd

/-! ## The mean square of the mollified partial sum, Montgomery–Vaughan shape -/

/-- **The mean square of `M_y P_K − 1` with the error term inside the sum.**  This is the
mean value theorem of `RiemannHypothesis/GaussianMeanValue.lean` applied to the mollified
partial sum; compared with `integral_normSq_mollified_partialSum_sub_one_le` the error
`8 yK (1 + log (yK))` is replaced by the sum of `d(m)² m^{-2σ} m`. -/
theorem integral_normSq_mollified_partialSum_sub_one_le_mv {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K)
    (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
      ≤ 58 * ∑ m ∈ Finset.Ioc y (y * K),
          (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (T + m) := by
  classical
  have hK1 : 1 ≤ K := le_trans hy hyK
  have hyyK : y ≤ y * K := Nat.le_mul_of_pos_right y (by omega)
  have hcongr : (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
      = ∫ t in (0 : ℝ)..T,
          ‖dirichletPoly (mollifiedTailCoeff y K) (y * K) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mollifiedTail_eq hy hyK]
  rw [hcongr]
  refine (integral_Icc_normSq_dirichletPoly_le_mv (mollifiedTailCoeff y K) (y * K) σ hT).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hIcc : Finset.Icc 1 (y * K) = Finset.Ioc 0 (y * K) := by
    ext m; simp [Finset.mem_Icc]; omega
  rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) hyyK]
  have hlow : ∑ m ∈ Finset.Ioc 0 y,
      ‖mollifiedTailCoeff y K m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) * (T + m) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [mollifiedTailCoeff_eq_zero_of_le (Finset.mem_Ioc.mp hm).2]
    simp
  rw [hlow, zero_add]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hm0 _
  have hT0 : (0 : ℝ) ≤ T + m := by linarith
  have hcoeff : ‖mollifiedTailCoeff y K m‖ ^ 2 ≤ (divisorCount m : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedTailCoeff_le_divisorCount y K m) 2
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hpow) hT0
  exact this

/-! ## The truncation length -/

/-- The exponent `α = (1 + 1/(3/2 − σ₀))/2` used for the length of the truncation: it lies
strictly between `1` and `1 / (3/2 − σ₀)`, so `b^α` is longer than `b` while
`(b^α)^{3/2−σ₀} = o(b)`. -/
def carlsonExponent (σ₀ : ℝ) : ℝ := (1 + 1 / (3 / 2 - σ₀)) / 2

/-- `1 < α`. -/
theorem one_lt_carlsonExponent {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    1 < carlsonExponent σ₀ := by
  have hb : 0 < 3 / 2 - σ₀ := by linarith
  have hb1 : 3 / 2 - σ₀ < 1 := by linarith
  have h : 1 < 1 / (3 / 2 - σ₀) := by
    rw [lt_div_iff₀ hb]
    linarith
  rw [carlsonExponent]
  linarith

/-- `α (3/2 − σ₀) < 1`. -/
theorem carlsonExponent_mul_lt_one {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    carlsonExponent σ₀ * (3 / 2 - σ₀) < 1 := by
  have hb : 0 < 3 / 2 - σ₀ := by linarith
  have hb1 : 3 / 2 - σ₀ < 1 := by linarith
  have hinv : 1 / (3 / 2 - σ₀) * (3 / 2 - σ₀) = 1 := one_div_mul_cancel (ne_of_gt hb)
  rw [carlsonExponent]
  nlinarith [hinv]

/-- The truncation length: `K(b) = ⌈b^α⌉`. -/
def truncationLength (σ₀ b : ℝ) : ℕ := ⌈b ^ carlsonExponent σ₀⌉₊

/-! ## Two analytic preliminaries -/

/-- `∫_a^b t^{-2} dt ≤ 1` whenever `1 ≤ a ≤ b`: the contribution of the pole of `ζ` to the
mean square is bounded, uniformly in the length of the segment. -/
theorem integral_inv_sq_le_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) ≤ 1 := by
  have hb : (1 : ℝ) ≤ b := le_trans ha hab
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.uIcc 1 b) := by
    rw [Set.uIcc_of_le hb]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := ht.1
    positivity
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume 1 b := hcont.intervalIntegrable
  have hmain : (∫ t in (1 : ℝ)..b, 1 / t ^ 2) ≤ 1 := by
    have h := integral_inv_sq_shift_le_one 1 hb
    simpa using h
  refine le_trans ?_ hmain
  refine intervalIntegral.integral_mono_interval ha hab le_rfl ?_ hi
  filter_upwards with t
  have : (0 : ℝ) ≤ 1 / t ^ 2 := by positivity
  simpa using this

/-- `t ↦ ‖ζ(σ + i t) − P_N(σ + i t)‖²` is continuous on `[1, ∞)`. -/
theorem continuousOn_normSq_riemannZeta_sub_dirichletPoly_line (σ : ℝ) (N : ℕ) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Set.Ici 1) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hline : ContinuousAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
  have hz : ContinuousAt (fun u : ℝ => riemannZeta ((σ : ℂ) + (u : ℂ) * I)) t :=
    ContinuousAt.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (g := riemannZeta)
      ((differentiableAt_riemannZeta hne).continuousAt) hline
  have hp : ContinuousAt (fun u : ℝ => dirichletPoly (fun _ => 1) N ((σ : ℂ) + (u : ℂ) * I)) t :=
    (continuous_dirichletPoly_line N).continuousAt
  exact (((hz.sub hp).norm).pow 2).continuousWithinAt

/-! ## The mean square of `ζ − P_K` -/

set_option maxHeartbeats 1000000 in
-- the proof carries a large context (Euler–Maclaurin constants, four exponent thresholds)
/-- **The mean square of `ζ − P_K` at length `K = ⌈b^α⌉` is `o(b)`.**  Uniformly for
`σ₀ ≤ σ ≤ 6`, and for every `1 ≤ a ≤ b` with `b` large. -/
theorem exists_integral_normSq_zeta_sub_partialSum_le {σ₀ ε : ℝ} (h0 : 1 / 2 < σ₀)
    (h1 : σ₀ < 1) (hε : 0 < ε) :
    ∃ b₀ : ℝ, 6 ≤ b₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
      (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ ε * b := by
  have hσ₀₀ : (0 : ℝ) < σ₀ := by linarith
  set α := carlsonExponent σ₀ with hαdef
  have hα1 : 1 < α := one_lt_carlsonExponent h0 h1
  have hα10 : (0 : ℝ) < α - 1 := by linarith
  have hαmul : α * (3 / 2 - σ₀) < 1 := carlsonExponent_mul_lt_one h0 h1
  set β := 2 * α * (1 - σ₀) with hβdef
  have hβ1 : β < 1 := by rw [hβdef]; nlinarith
  have hβ0 : 0 < β := by rw [hβdef]; nlinarith
  set m : ℕ := max 1 ⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmbig : α * (1 - σ₀) + 1 ≤ (α - 1) * m := by
    have hceil : (α * (1 - σ₀) + 1) / (α - 1) ≤ (⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hmm : ((⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊
    have := (div_le_iff₀ hα10).mp (hceil.trans hmm)
    linarith
  clear_value β m
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_norm_riemannZeta_sub_dirichletPoly_le_em_uniform m hm1 hσ₀₀
  set E : ℝ := C * (1 + (2 + (m : ℝ)) ^ m) with hEdef
  have hE0 : 0 < E := by
    have : (0 : ℝ) < (2 + (m : ℝ)) ^ m := by positivity
    rw [hEdef]; nlinarith
  clear_value E
  refine ⟨max (max 6 ((2 : ℝ) ^ (1 / (α - 1))))
      (max ((36 / ε) ^ (1 / (1 - β))) (4 * E ^ 2 / ε)),
    (le_max_left (6 : ℝ) _).trans (le_max_left _ _), ?_⟩
  intro σ hσ hσ6 a b ha hab hb
  have hb6 : (6 : ℝ) ≤ b := ((le_max_left (6 : ℝ) _).trans (le_max_left _ _)).trans hb
  have hbpow2 : (2 : ℝ) ^ (1 / (α - 1)) ≤ b :=
    ((le_max_right (6 : ℝ) _).trans (le_max_left _ _)).trans hb
  have hbeps : (36 / ε) ^ (1 / (1 - β)) ≤ b :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hb
  have hbE : 4 * E ^ 2 / ε ≤ b := ((le_max_right _ _).trans (le_max_right _ _)).trans hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set N : ℕ := truncationLength σ₀ b with hNdef
  have hKceil : N = ⌈b ^ α⌉₊ := by rw [hNdef, truncationLength, hαdef]
  clear_value N α
  have hbα0 : (0 : ℝ) < b ^ α := Real.rpow_pos_of_pos hb0 α
  have hbb : b ≤ b ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hα1.le
    rwa [Real.rpow_one] at h
  have hbα1 : (1 : ℝ) ≤ b ^ α := le_trans hb1 hbb
  have hsplit : b ^ α = b ^ (α - 1) * b := by
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add hb0, Real.rpow_one]
  have hbpow : (2 : ℝ) ≤ b ^ (α - 1) := by
    have h := Real.rpow_le_rpow (by positivity) hbpow2 hα10.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hα10),
      Real.rpow_one] at h
  have h2b : 2 * b ≤ b ^ α := by
    rw [hsplit]
    nlinarith only [hbpow, hb0]
  have hKge : b ^ α ≤ (N : ℝ) := by rw [hKceil]; exact Nat.le_ceil _
  have hKle : (N : ℝ) ≤ b ^ α + 1 := by
    rw [hKceil]; exact le_of_lt (Nat.ceil_lt_add_one hbα0.le)
  have hK1R : (1 : ℝ) ≤ (N : ℝ) := le_trans hbα1 hKge
  have hK1 : 1 ≤ N := by exact_mod_cast hK1R
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h6bm : (0 : ℝ) ≤ 6 + b + (m : ℝ) := by linarith
  set A : ℝ := ((N : ℝ) + 1) ^ (1 - σ₀) with hAdef
  set B : ℝ := C * ((N : ℝ) ^ (-σ₀)
    + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))) with hBdef
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by linarith) _
  have hB0 : 0 ≤ B := by
    have e1 : (0 : ℝ) ≤ (N : ℝ) ^ (-σ₀) := Real.rpow_nonneg hN0.le _
    have e2 : (0 : ℝ) ≤ (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) :=
      mul_nonneg (pow_nonneg h6bm m) (Real.rpow_nonneg hN0.le _)
    rw [hBdef]; nlinarith
  clear_value A B
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 2 * A ^ 2 * (1 / t ^ 2) + 2 * B ^ 2 := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    have htb : t ≤ b := ht.2
    have htabs : |t| = t := abs_of_nonneg (by linarith)
    have hNt : σ + |t| ≤ (N : ℝ) := by rw [htabs]; linarith
    have hem := hCbd σ hσ N hK1 t (by rw [htabs]; linarith) hNt
    have hnorm : t ≤ ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ := by
      have h := Complex.abs_im_le_norm (((σ : ℂ) + (t : ℂ) * I) - 1)
      have him : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by simp
      rw [him, htabs] at h
      exact h
    have hterm1 : ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ ≤ A / t := by
      have hnum : ((N : ℝ) + 1) ^ (1 - σ) ≤ A := by
        rw [hAdef]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hnum0 : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
      have hstep : ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          ≤ ((N : ℝ) + 1) ^ (1 - σ) / t :=
        div_le_div_of_nonneg_left hnum0 (by linarith) hnorm
      exact hstep.trans (by gcongr)
    have hterm2 : C * ((N : ℝ) ^ (-σ) + (σ + |t| + (m : ℝ)) ^ m
        * (N : ℝ) ^ (1 - σ - (m : ℝ))) ≤ B := by
      have e1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ₀) :=
        Real.rpow_le_rpow_of_exponent_le hK1R (by linarith)
      have e2 : (σ + |t| + (m : ℝ)) ^ m ≤ (6 + b + (m : ℝ)) ^ m :=
        pow_le_pow_left₀ (by rw [htabs]; linarith) (by rw [htabs]; linarith) m
      have e3 : (N : ℝ) ^ (1 - σ - (m : ℝ)) ≤ (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hK1R (by linarith)
      have e4 := mul_le_mul e2 e3 (Real.rpow_nonneg hN0.le _)
        (pow_nonneg h6bm m)
      rw [hBdef]
      exact mul_le_mul_of_nonneg_left (add_le_add e1 e4) hC0.le
    have hle : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A / t + B :=
      hem.trans (add_le_add hterm1 hterm2)
    have ht0 : (0 : ℝ) < t := by linarith
    have hdiv : (A / t) ^ 2 = A ^ 2 * (1 / t ^ 2) := by field_simp
    have hexp2 : (A / t + B) ^ 2 ≤ 2 * (A / t) ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (A / t - B)]
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (A / t + B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ 2 * (A / t) ^ 2 + 2 * B ^ 2 := hexp2
      _ = 2 * A ^ 2 * (1 / t ^ 2) + 2 * B ^ 2 := by rw [hdiv]; ring
  -- integrate
  have hcontLHS : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_normSq_riemannZeta_sub_dirichletPoly_line σ N).mono
      fun t ht => le_trans ha ht.1
  have hiL : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume a b :=
    hcontLHS.intervalIntegrable
  have hi1 : IntervalIntegrable (fun t : ℝ => 2 * A ^ 2 * (1 / t ^ 2)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.mul (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    positivity
  have hi2 : IntervalIntegrable (fun _ : ℝ => 2 * B ^ 2) volume a b := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hiL (hi1.add hi2) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul]
  set X : ℝ := ∫ t in a..b, 1 / t ^ 2 with hXdef
  have hX1 : X ≤ 1 := integral_inv_sq_le_one ha hab
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine intervalIntegral.integral_nonneg hab fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    positivity
  clear_value X
  -- the two constants
  have h3 : (3 : ℝ) ^ (1 - σ₀) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith : (1 - σ₀) ≤ 1)
    rwa [Real.rpow_one] at h
  have hNA : (N : ℝ) + 1 ≤ 3 * b ^ α := by linarith
  have hAle : A ≤ 3 * b ^ (α * (1 - σ₀)) := by
    calc A = ((N : ℝ) + 1) ^ (1 - σ₀) := hAdef
      _ ≤ (3 * b ^ α) ^ (1 - σ₀) :=
          Real.rpow_le_rpow (by linarith) hNA (by linarith)
      _ = (3 : ℝ) ^ (1 - σ₀) * (b ^ α) ^ (1 - σ₀) := Real.mul_rpow (by norm_num) hbα0.le
      _ = (3 : ℝ) ^ (1 - σ₀) * b ^ (α * (1 - σ₀)) := by rw [← Real.rpow_mul hb0.le]
      _ ≤ 3 * b ^ (α * (1 - σ₀)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hb0.le _)
  have hA2 : A ^ 2 ≤ 9 * b ^ β := by
    have hpow : (b ^ (α * (1 - σ₀))) ^ 2 = b ^ β := by
      rw [← Real.rpow_natCast (b ^ (α * (1 - σ₀))) 2, ← Real.rpow_mul hb0.le, hβdef]
      congr 1
      push_cast
      ring
    calc A ^ 2 ≤ (3 * b ^ (α * (1 - σ₀))) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
      _ = 9 * (b ^ (α * (1 - σ₀))) ^ 2 := by ring
      _ = 9 * b ^ β := by rw [hpow]
  have hBle : B ≤ E * b ^ (-σ₀) := by
    have ebα : ((b : ℝ) ^ α) ^ (-σ₀) ≤ b ^ (-σ₀) := by
      rw [← Real.rpow_mul hb0.le]
      exact Real.rpow_le_rpow_of_exponent_le hb1 (by nlinarith only [hα1, hσ₀₀])
    have e1 : (N : ℝ) ^ (-σ₀) ≤ b ^ (-σ₀) :=
      (Real.rpow_le_rpow_of_nonpos hbα0 hKge (by linarith)).trans ebα
    have e2 : (6 + b + (m : ℝ)) ^ m ≤ (2 + (m : ℝ)) ^ m * b ^ (m : ℝ) := by
      have hle : 6 + b + (m : ℝ) ≤ (2 + (m : ℝ)) * b := by
        nlinarith only [mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))
          (by linarith only [hb1] : (0 : ℝ) ≤ b - 1), hb6]
      calc (6 + b + (m : ℝ)) ^ m ≤ ((2 + (m : ℝ)) * b) ^ m := pow_le_pow_left₀ h6bm hle m
        _ = (2 + (m : ℝ)) ^ m * b ^ m := mul_pow _ _ _
        _ = (2 + (m : ℝ)) ^ m * b ^ (m : ℝ) := by rw [Real.rpow_natCast]
    have e3 : (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) ≤ b ^ (α * (1 - σ₀ - (m : ℝ))) := by
      have h := Real.rpow_le_rpow_of_nonpos hbα0 hKge (by linarith : (1 : ℝ) - σ₀ - (m : ℝ) ≤ 0)
      rwa [← Real.rpow_mul hb0.le] at h
    have hexp : (m : ℝ) + α * (1 - σ₀ - (m : ℝ)) ≤ -σ₀ := by
      nlinarith only [hmbig, h1, h0]
    have e4 : b ^ (m : ℝ) * b ^ (α * (1 - σ₀ - (m : ℝ))) ≤ b ^ (-σ₀) := by
      rw [← Real.rpow_add hb0]
      exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
    have hprod : (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
        ≤ (2 + (m : ℝ)) ^ m * b ^ (-σ₀) := by
      calc (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
          ≤ ((2 + (m : ℝ)) ^ m * b ^ (m : ℝ)) * b ^ (α * (1 - σ₀ - (m : ℝ))) :=
            mul_le_mul e2 e3 (Real.rpow_nonneg hN0.le _) (by positivity)
        _ = (2 + (m : ℝ)) ^ m * (b ^ (m : ℝ) * b ^ (α * (1 - σ₀ - (m : ℝ)))) := by ring
        _ ≤ (2 + (m : ℝ)) ^ m * b ^ (-σ₀) := mul_le_mul_of_nonneg_left e4 (by positivity)
    have hsum : (N : ℝ) ^ (-σ₀)
        + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
        ≤ (1 + (2 + (m : ℝ)) ^ m) * b ^ (-σ₀) := by nlinarith only [e1, hprod]
    calc B = C * ((N : ℝ) ^ (-σ₀)
            + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))) := hBdef
      _ ≤ C * ((1 + (2 + (m : ℝ)) ^ m) * b ^ (-σ₀)) :=
          mul_le_mul_of_nonneg_left hsum hC0.le
      _ = E * b ^ (-σ₀) := by rw [hEdef]; ring
  have hB2 : B ^ 2 ≤ E ^ 2 / b := by
    have hsq : (E * b ^ (-σ₀)) ^ 2 = E ^ 2 * b ^ (-(2 * σ₀)) := by
      rw [mul_pow, ← Real.rpow_natCast (b ^ (-σ₀)) 2, ← Real.rpow_mul hb0.le]
      congr 2
      push_cast
      ring
    have h3' : b ^ (-(2 * σ₀)) ≤ b ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have h4' : b ^ (-(1 : ℝ)) = 1 / b := by
      rw [Real.rpow_neg hb0.le, Real.rpow_one, one_div]
    calc B ^ 2 ≤ (E * b ^ (-σ₀)) ^ 2 := pow_le_pow_left₀ hB0 hBle 2
      _ = E ^ 2 * b ^ (-(2 * σ₀)) := hsq
      _ ≤ E ^ 2 * (1 / b) := by rw [← h4']; exact mul_le_mul_of_nonneg_left h3' (by positivity)
      _ = E ^ 2 / b := by ring
  -- the thresholds
  have hfinal1 : 18 * b ^ β ≤ ε / 2 * b := by
    have hbb1 : (36 / ε) ≤ b ^ (1 - β) := by
      have h := Real.rpow_le_rpow (by positivity) hbeps (by linarith : (0 : ℝ) ≤ 1 - β)
      rwa [← Real.rpow_mul (by positivity), one_div,
        inv_mul_cancel₀ (by linarith : (1 : ℝ) - β ≠ 0), Real.rpow_one] at h
    have hbb1' : (36 : ℝ) ≤ b ^ (1 - β) * ε := (div_le_iff₀ hε).mp hbb1
    have hX : (0 : ℝ) < b ^ β := Real.rpow_pos_of_pos hb0 β
    have hsplit2 : b ^ (1 - β) * b ^ β = b := by
      rw [← Real.rpow_add hb0]
      norm_num
    have key : 18 * b ^ β ≤ ε / 2 * (b ^ (1 - β) * b ^ β) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hbb1') hX.le, hX, hbb1']
    rwa [hsplit2] at key
  have hfinal2 : 2 * E ^ 2 ≤ ε / 2 * b := by
    have h := (div_le_iff₀ hε).mp hbE
    linarith only [h]
  -- assemble
  have hAX : 2 * A ^ 2 * X ≤ 18 * b ^ β := by
    have hA2nn : (0 : ℝ) ≤ 2 * A ^ 2 := by positivity
    calc 2 * A ^ 2 * X ≤ 2 * A ^ 2 * 1 := mul_le_mul_of_nonneg_left hX1 hA2nn
      _ = 2 * A ^ 2 := by ring
      _ ≤ 18 * b ^ β := by linarith only [hA2]
  have hBb : (b - a) * (2 * B ^ 2) ≤ 2 * E ^ 2 := by
    have hstep1 : (b - a) * (2 * B ^ 2) ≤ b * (2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [ha] : b - a ≤ b) (by positivity)
    have hstep2 : b * (2 * B ^ 2) ≤ b * (2 * (E ^ 2 / b)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hB2]) hb0.le
    have hstep3 : b * (2 * (E ^ 2 / b)) = 2 * E ^ 2 := by
      field_simp
    linarith only [hstep1, hstep2, hstep3]
  linarith only [hAX, hBb, hfinal1, hfinal2]

/-! ## The mean square of `M_y P_K − 1` at the Carlson length -/

/-- The Dirichlet polynomial with all coefficients `1`, as a sum over `Icc 1 K`. -/
theorem dirichletPoly_one_eq_sum (K : ℕ) (s : ℂ) :
    dirichletPoly (fun _ => 1) K s = ∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s) := by
  unfold dirichletPoly
  simp

/-- The mollifier is continuous along a vertical line. -/
theorem continuous_mollifier_line (y : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I)) := by
  unfold Mollifier.mollifier
  refine continuous_finsetSum _ fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  refine continuous_const.mul (Continuous.cpow continuous_const (by fun_prop) fun t => ?_)
  left
  simpa using hn0

set_option maxHeartbeats 1000000 in
-- the proof combines the Montgomery–Vaughan mean value theorem with two exponent thresholds
/-- **The mean square of `M_y P_K − 1` at the Carlson length `K = ⌈b^α⌉` is `≤ ε b`.**  The
Montgomery–Vaughan shape of the mean value theorem is what makes this possible: the error
term sits inside the sum, so the polynomial may be as long as `y K ≈ b^α` and still
contribute `∑_{m ≤ yK} d(m)² m^{1−2σ} ≪ (yK)^{3/2−σ₀} = o(b)`. -/
theorem exists_integral_normSq_mollified_partialSum_sub_one_le_carlson {σ₀ ε : ℝ}
    (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y : ℕ, y₀ ≤ y → ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → ∀ b : ℝ, b₀ ≤ b →
        (∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
          ≤ ε * b := by
  obtain ⟨S, hS0, hSbd⟩ := exists_sum_divisorCount_sq_mul_le h0 h1
  obtain ⟨y₁, hy₁, htail⟩ :=
    exists_tsum_divisorCount_sq_tail_lt h0 (show (0 : ℝ) < ε / 116 by positivity)
  refine ⟨max 4 y₁, le_max_left _ _, ?_⟩
  intro y hy
  have hy4 : 4 ≤ y := le_trans (le_max_left _ _) hy
  have hy₁y : y₁ ≤ y := le_trans (le_max_right _ _) hy
  have hy1 : 1 ≤ y := by omega
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  set e : ℝ := 3 / 2 - σ₀ with hedef
  have he0 : 0 < e := by rw [hedef]; linarith
  set α : ℝ := carlsonExponent σ₀ with hαdef
  have hα1 : 1 < α := one_lt_carlsonExponent h0 h1
  set γ : ℝ := α * e with hγdef
  have hγ1 : γ < 1 := by
    rw [hγdef, hαdef, hedef]
    exact carlsonExponent_mul_lt_one h0 h1
  have hγ0 : 0 < γ := by rw [hγdef]; nlinarith only [hα1, he0]
  have hbase : (0 : ℝ) < 2 * (y : ℝ) := by linarith
  have hpowpos : (0 : ℝ) < (2 * (y : ℝ)) ^ e := Real.rpow_pos_of_pos hbase e
  set c : ℝ := 116 * S * (2 * (y : ℝ)) ^ e / ε with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]
    exact div_pos (mul_pos (mul_pos (by norm_num) hS0) hpowpos) hε
  clear_value e α γ c
  refine ⟨max (max 6 (y : ℝ)) (c ^ (1 / (1 - γ))),
    (le_max_left (6 : ℝ) _).trans (le_max_left _ _), ?_⟩
  intro σ hσ b hb
  have hb6 : (6 : ℝ) ≤ b := ((le_max_left (6 : ℝ) _).trans (le_max_left _ _)).trans hb
  have hby : (y : ℝ) ≤ b := ((le_max_right (6 : ℝ) _).trans (le_max_left _ _)).trans hb
  have hbc : c ^ (1 / (1 - γ)) ≤ b := (le_max_right _ _).trans hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hKceil : truncationLength σ₀ b = ⌈b ^ α⌉₊ := by rw [truncationLength, hαdef]
  set K : ℕ := truncationLength σ₀ b with hKdef
  clear_value K
  have hbα0 : (0 : ℝ) < b ^ α := Real.rpow_pos_of_pos hb0 α
  have hbb : b ≤ b ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hα1.le
    rwa [Real.rpow_one] at h
  have hbα1 : (1 : ℝ) ≤ b ^ α := le_trans hb1 hbb
  have hKge : b ^ α ≤ (K : ℝ) := by rw [hKceil]; exact Nat.le_ceil _
  have hKle : (K : ℝ) ≤ b ^ α + 1 := by
    rw [hKceil]; exact le_of_lt (Nat.ceil_lt_add_one hbα0.le)
  have hyKR : (y : ℝ) ≤ (K : ℝ) := by linarith
  have hyK : y ≤ K := by exact_mod_cast hyKR
  have hcongr : (∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        dirichletPoly (fun _ => 1) K ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      = ∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [dirichletPoly_one_eq_sum]
  rw [hcongr]
  refine (integral_normSq_mollified_partialSum_sub_one_le_mv hy1 hyK σ hb6).trans ?_
  have hsplit : ∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (b + m)
      = b * (∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ))
        + ∑ m ∈ Finset.Ioc y (y * K),
            (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit]
  -- the tail of the divisor sum
  have hT1 : ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ ε / 116 := by
    have s1 := sum_Ioc_divisorCount_sq_le_of_le hσ y (y * K)
    have s2 : ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₀)
        ≤ ∑ m ∈ Finset.Ioc y₁ (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₀) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        simp only [Finset.mem_Ioc] at hm ⊢
        omega
      · intro m _ _
        have hp : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ₀) := Real.rpow_nonneg (by positivity) _
        positivity
    have s3 := sum_Ioc_divisorCount_sq_le_tsum h0 y₁ (y * K)
    linarith only [s1, s2, s3, htail]
  -- the weighted divisor sum
  have hT2 : ∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
      ≤ S * (((y * K : ℕ) : ℝ)) ^ e := by
    have s1 : ∑ m ∈ Finset.Ioc y (y * K),
          (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 (y * K),
          (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_Icc]
        omega
      · intro m _ _
        have hp : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
        positivity
    exact s1.trans (hSbd σ hσ (y * K))
  have hyKcast : (((y * K : ℕ)) : ℝ) = (y : ℝ) * (K : ℝ) := by push_cast; ring
  have hyKb : (y : ℝ) * (K : ℝ) ≤ (2 * (y : ℝ)) * b ^ α := by
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := by linarith
    have q1 : (y : ℝ) * (K : ℝ) ≤ (y : ℝ) * (b ^ α + 1) := mul_le_mul_of_nonneg_left hKle hy0
    have q2 : (y : ℝ) * 1 ≤ (y : ℝ) * b ^ α := mul_le_mul_of_nonneg_left hbα1 hy0
    nlinarith only [q1, q2]
  have hpowyK : (((y * K : ℕ)) : ℝ) ^ e ≤ (2 * (y : ℝ)) ^ e * b ^ γ := by
    rw [hyKcast]
    calc ((y : ℝ) * (K : ℝ)) ^ e ≤ ((2 * (y : ℝ)) * b ^ α) ^ e :=
          Real.rpow_le_rpow (by positivity) hyKb he0.le
      _ = (2 * (y : ℝ)) ^ e * (b ^ α) ^ e := Real.mul_rpow hbase.le hbα0.le
      _ = (2 * (y : ℝ)) ^ e * b ^ (α * e) := by rw [← Real.rpow_mul hb0.le]
      _ = (2 * (y : ℝ)) ^ e * b ^ γ := by rw [hγdef]
  -- the threshold in `b`
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hbc' : c ≤ b ^ (1 - γ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hc0.le _) hbc (by linarith : (0 : ℝ) ≤ 1 - γ)
    rwa [← Real.rpow_mul hc0.le, one_div,
      inv_mul_cancel₀ (by linarith : (1 : ℝ) - γ ≠ 0), Real.rpow_one] at h
  have hbγ0 : (0 : ℝ) < b ^ γ := Real.rpow_pos_of_pos hb0 γ
  have hsplitγ : b ^ (1 - γ) * b ^ γ = b := by
    rw [← Real.rpow_add hb0]
    norm_num
  have hcb : c * b ^ γ ≤ b := by nlinarith only [hbc', hbγ0, hsplitγ]
  have hkey : 116 * S * (2 * (y : ℝ)) ^ e * b ^ γ ≤ ε * b := by
    calc 116 * S * (2 * (y : ℝ)) ^ e * b ^ γ = ε * (c * b ^ γ) := by
          rw [hcdef]; field_simp
      _ ≤ ε * b := mul_le_mul_of_nonneg_left hcb hε.le
  have hstep1 : b * (∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)) ≤ b * (ε / 116) :=
    mul_le_mul_of_nonneg_left hT1 hb0.le
  have hstep2 : (∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ))
      ≤ S * ((2 * (y : ℝ)) ^ e * b ^ γ) :=
    hT2.trans (mul_le_mul_of_nonneg_left hpowyK hS0.le)
  linarith only [hstep1, hstep2, hkey]

/-! ## The mean square of `ζ M_y − 1` -/

/-- **The mean square of `ζ M_y − 1` on a vertical segment in the strip.**  For every
`σ₀ > 1/2` and every `ε > 0` there are a mollifier length `y` and a height `b₀` such that

`∫_a^b ‖ζ(σ + i t) M_y(σ + i t) − 1‖² dt ≤ ε b`

for every `1 ≤ a ≤ b` with `b ≥ b₀`, uniformly for `σ₀ ≤ σ ≤ 6`.  This is the statement that
`M_y` mollifies `ζ` *inside* the critical strip; the mollifier identity of
`RiemannHypothesis/Mollifier.lean` only gives it in `re s > 1`, where `ζ` has no zeroes.

The mollifier length may be taken as long as one likes: the bound is stated for *every*
`y ≥ y₀`, with a height `b₀` depending on `y`.  That extra freedom is what the Carlson
counting argument needs, since it also wants `1/y` small. -/
theorem exists_integral_normSq_zeta_mul_mollifier_sub_one_le {σ₀ ε : ℝ} (h0 : 1 / 2 < σ₀)
    (h1 : σ₀ < 1) (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y : ℕ, y₀ ≤ y → ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤ ε * b := by
  obtain ⟨y₀, hy₀4, hmoll⟩ :=
    exists_integral_normSq_mollified_partialSum_sub_one_le_carlson h0 h1
      (show (0 : ℝ) < ε / 4 by positivity)
  refine ⟨y₀, hy₀4, ?_⟩
  intro y hy
  have hy4 : 4 ≤ y := le_trans hy₀4 hy
  have hy1 : 1 ≤ y := by omega
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  obtain ⟨b₁, hb₁6, hb₁⟩ := hmoll y hy
  obtain ⟨b₂, hb₂6, hb₂⟩ := exists_integral_normSq_zeta_sub_partialSum_le h0 h1
    (show (0 : ℝ) < ε / (4 * (y : ℝ) ^ 2) by positivity)
  refine ⟨max b₁ b₂, le_max_of_le_left hb₁6, ?_⟩
  intro σ hσ hσ6 a b ha hab hb
  have hbb₁ : b₁ ≤ b := (le_max_left _ _).trans hb
  have hbb₂ : b₂ ≤ b := (le_max_right _ _).trans hb
  have hb6 : (6 : ℝ) ≤ b := le_trans hb₁6 hbb₁
  have hb0 : (0 : ℝ) < b := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the two continuity facts
  have hcM : Continuous (fun t : ℝ => Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I)) :=
    continuous_mollifier_line y σ
  have hcF : Continuous (fun t : ℝ => ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) :=
    (((hcM.mul (continuous_dirichletPoly_line (truncationLength σ₀ b))).sub
      continuous_const).norm).pow 2
  have hcL : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) (Set.Ici 1) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    have hline : ContinuousAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
    have hz : ContinuousAt (fun u : ℝ => riemannZeta ((σ : ℂ) + (u : ℂ) * I)) t :=
      ContinuousAt.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (g := riemannZeta)
        ((differentiableAt_riemannZeta hne).continuousAt) hline
    exact ((((hz.mul hcM.continuousAt).sub continuousAt_const).norm).pow 2).continuousWithinAt
  have hcG : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Set.Ici 1) :=
    continuousOn_normSq_riemannZeta_sub_dirichletPoly_line σ (truncationLength σ₀ b)
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2
      ≤ 2 * ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2
        + 2 * (y : ℝ) ^ 2 * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t _
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have hM : ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (y : ℝ) :=
      norm_mollifier_le_length y (by rw [hre]; linarith)
    have hid : riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1
        = (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
          + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
              - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)) := by
      ring
    rw [hid]
    set U : ℝ := ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ with hUdef
    set V : ℝ := ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ with hVdef
    have hprod : ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖
        ≤ (y : ℝ) * V := by
      rw [norm_mul, hVdef]
      exact mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    have hsum : ‖(Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖
        ≤ U + (y : ℝ) * V :=
      (norm_add_le (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b)
              ((σ : ℂ) + (t : ℂ) * I)))).trans (add_le_add (le_refl U) hprod)
    have hU0 : 0 ≤ U := norm_nonneg _
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖(Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2
        ≤ (U + (y : ℝ) * V) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsum 2
      _ ≤ 2 * U ^ 2 + 2 * (y : ℝ) ^ 2 * V ^ 2 := by
          nlinarith only [sq_nonneg (U - (y : ℝ) * V)]
  -- integrability
  have hiL : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hcL.mono fun t ht => le_trans ha ht.1
  have hiF : IntervalIntegrable (fun t : ℝ => 2 * ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      volume a b := (hcF.const_smul (2 : ℝ)).intervalIntegrable a b
  have hiG : IntervalIntegrable (fun t : ℝ => 2 * (y : ℝ) ^ 2 *
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul (hcG.mono fun t ht => le_trans ha ht.1)
  have hmain := intervalIntegral.integral_mono_on hab hiL (hiF.add hiG) hpt
  rw [intervalIntegral.integral_add hiF hiG, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmain
  -- the two integral bounds
  have hI1 : (∫ t in a..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      ≤ ε / 4 * b := by
    refine le_trans ?_ (hb₁ σ hσ b hbb₁)
    refine intervalIntegral.integral_mono_interval (by linarith) hab le_rfl ?_
      (hcF.intervalIntegrable 0 b)
    filter_upwards with t
    simp only [Pi.zero_apply]
    positivity
  have hI2 : (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ε / (4 * (y : ℝ) ^ 2) * b := hb₂ σ hσ hσ6 a b ha hab hbb₂
  have hI2' : 2 * (y : ℝ) ^ 2 * (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ε / 2 * b := by
    have hfac : (0 : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hI2 hfac
    have heq : 2 * (y : ℝ) ^ 2 * (ε / (4 * (y : ℝ) ^ 2) * b) = ε / 2 * b := by
      field_simp
      ring
    linarith only [hstep, heq]
  linarith only [hmain, hI1, hI2']

end RiemannHypothesis
