/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AFEIntegrals
import RiemannHypothesis.PoissonSummationInterval
import RiemannHypothesis.ZetaPartialSum
import RiemannHypothesis.ApproximateFunctionalEquation

/-!
# The approximate functional equation on the critical line (R3)

For `s = 1/2 + it`, `N = ⌊√(t/2π)⌋`, `a = N + 1/2`, `b = B + 1/2` with `B` large (`t ≤ √b`), and
`c = t/(2πa)` (so the stationary point of the `ν`-th Poisson integral sits at `u = t/(2πν) = ac/ν`):

* `hasSum_Fν` — **exact Poisson summation between half-integers**
  (`PoissonInterval.hasSum_sum_Ioc_halfInt` applied to `G(x) = x^(-s)`):
  `∑_{a < n ≤ b} n^(-s) − ∫_a^b x^(-s) dx = ∑_{ν ≥ 1} F_ν`, with
  `F_ν = ∫_a^b x^(-s) 2 cos(2πνx) dx = I_{+2πν}(a, b) + I_{-2πν}(a, b)`.  At half-integers the
  sawtooth boundary terms vanish, so no truncation error has to be estimated.
* `norm_zeta_sub_zetaSum_sub_le` — Theorem 4.11 at `x = b` (`ZetaPartialSum`) turns this into
  `‖ζ(s) − ∑_{n ≤ N} n^(-s) − X‖ ≤ 11 b^(-1/2) + √a/t + ‖∑_ν F_ν − X‖` for every `X`.
* The frequencies are split in three ranges.  **Lower range** `1 ≤ ν ≤ c − 1`
  (`norm_sum_lower_le`): the stationary point lies inside `(a, b)`, and
  `ZetaStationaryPhase.norm_integral_sub_zetaChi_add_boundary_le` gives
  `F_ν = χ(s) ν^(s-1) + (endpoint terms) + O(…)`; the endpoint terms at `a` carry the sign
  `(-1)^ν` (`bdry_pair_halfInt`) and are summed as an alternating series with monotone
  amplitudes (`abs_alternating_sum_le`).  **Near range** — the at most four `ν` with
  `c − 1 < ν < c + 1` (`norm_Fν_le_remR`, from `AFEIntegrals.norm_mI_le_of_near`), and the
  difference between `∑_{ν ≤ c − 1}` and `∑_{ν ≤ N}` of the main terms (`zetaSumDual_split`).
  **Upper range** `ν ≥ c + 1` (`norm_sum_upper_le`): no stationary point, second-order
  integration by parts, the endpoint terms again alternating.  The reflected frequencies `−2πν`
  never have a stationary point (`AFEIntegrals.norm_mI_neg_add_boundary_le`).
* `norm_poisson_sub_main_le` — the three ranges together:
  `‖∑_ν F_ν − χ(s) ∑_{n ≤ N} n^(s-1)‖` is at most an explicit expression in `t, a, b, c`.
* `afe_bound_numeric` — the numerical bookkeeping (`num_T1` … `num_T8`): for `N ≥ 5`,
  `4a² ≤ t`, `c ≤ 2a` and `t ≤ √b`, the total error is at most `80/√a`.

The assembly into `AFECriticalLine 250` is in `RiemannHypothesis.AFECriticalLineProof`.
Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset

namespace RiemannHypothesis

namespace AFEProof

open VanDerCorput Oscillatory ZetaMellinPhase

/-! ## Elementary sums -/

theorem alternating_sum_mem (L : ℕ) : ∀ (g : ℕ → ℝ), Antitone g → (∀ j, 0 ≤ g j) →
    0 ≤ ∑ j ∈ range L, (-1 : ℝ) ^ j * g j ∧ ∑ j ∈ range L, (-1 : ℝ) ^ j * g j ≤ g 0 := by
  induction L with
  | zero => intro g _ h0; simp [h0 0]
  | succ L ih =>
    intro g hg h0
    obtain ⟨h1, h2⟩ := ih (fun j => g (j + 1)) (fun i j hij => hg (by omega)) (fun j => h0 _)
    rw [sum_range_succ']
    have e : ∑ j ∈ range L, (-1 : ℝ) ^ (j + 1) * g (j + 1)
        = -∑ j ∈ range L, (-1 : ℝ) ^ j * g (j + 1) := by
      rw [← sum_neg_distrib]; refine sum_congr rfl fun j _ => ?_; ring
    rw [e]
    have h3 : g 1 ≤ g 0 := hg (by omega)
    simp only [pow_zero, one_mul]
    constructor <;> linarith

/-- **Alternating sums**: if `g` is antitone and nonnegative, then
`|∑_{j < L} (-1)^j g(j)| ≤ g(0)`. -/
theorem abs_alternating_sum_le {g : ℕ → ℝ} (hg : Antitone g) (h0 : ∀ j, 0 ≤ g j) (L : ℕ) :
    |∑ j ∈ range L, (-1 : ℝ) ^ j * g j| ≤ g 0 := by
  obtain ⟨h1, h2⟩ := alternating_sum_mem L g hg h0
  rw [abs_of_nonneg h1]; exact h2

theorem sum_inv_sq_shift_aux {d : ℝ} (hd : 1 ≤ d) (L : ℕ) :
    ∑ j ∈ range (L + 1), 1 / (d + j) ^ 2 ≤ 2 / d - 1 / (d + L) := by
  induction L with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, add_zero]
    rw [div_sub_div_same, show (2 : ℝ) - 1 = 1 by norm_num, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  | succ L ih =>
    rw [sum_range_succ]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have key : 1 / (d + ((L + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (d + L) - 1 / (d + ((L + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `∑_{j < L} 1/(d + j)² ≤ 2/d` for `d ≥ 1`. -/
theorem sum_inv_sq_shift_le {d : ℝ} (hd : 1 ≤ d) (L : ℕ) :
    ∑ j ∈ range L, 1 / (d + j) ^ 2 ≤ 2 / d := by
  rcases L with _ | L
  · simp; positivity
  · have := sum_inv_sq_shift_aux hd L
    have : 0 ≤ 1 / (d + L) := by positivity
    linarith


/-! ## The Poisson integrals, one frequency at a time -/

/-- `e^{iΦ(A + 1/2)} = (-1)^ν a^{-it}` for `ω = ±2πν`. -/
theorem expI_phase_halfInt (t : ℝ) (A ν : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    expI (phase t (ε * (2 * Real.pi * ν))) ((A : ℝ) + 1 / 2)
      = (-1 : ℂ) ^ ν * expI (phase t 0) ((A : ℝ) + 1 / 2) := by
  unfold expI phase
  have hsplit : I * (((ε * (2 * Real.pi * ν)) * ((A : ℝ) + 1 / 2) - t * Real.log ((A : ℝ) + 1 / 2) : ℝ) : ℂ)
      = ((ε * (ν * (2 * A + 1)) : ℝ) : ℂ) * (Real.pi * I)
        + I * (((0 : ℝ) * ((A : ℝ) + 1 / 2) - t * Real.log ((A : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add]
  congr 1
  have hpow : cexp (((2 * A + 1) * ν : ℕ) * (Real.pi * I)) = (-1 : ℂ) ^ ν := by
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I, pow_mul,
      Odd.neg_one_pow (by exact odd_two_mul_add_one A)]
  rcases hε with rfl | rfl
  · rw [← hpow]; congr 1; push_cast; ring
  · rw [show ((((-1 : ℝ) * (ν * (2 * A + 1)) : ℝ)) : ℂ) * (Real.pi * I)
        = -(((2 * A + 1) * ν : ℕ) * (Real.pi * I)) by push_cast; ring, Complex.exp_neg, hpow]
    rw [← inv_pow, inv_neg, inv_one]

theorem expI_phase_pos_halfInt (t : ℝ) (A ν : ℕ) :
    expI (phase t (2 * Real.pi * ν)) ((A : ℝ) + 1 / 2)
      = (-1 : ℂ) ^ ν * expI (phase t 0) ((A : ℝ) + 1 / 2) := by
  have := expI_phase_halfInt t A ν 1 (Or.inl rfl)
  rwa [one_mul] at this

theorem expI_phase_neg_halfInt (t : ℝ) (A ν : ℕ) :
    expI (phase t (-(2 * Real.pi * ν))) ((A : ℝ) + 1 / 2)
      = (-1 : ℂ) ^ ν * expI (phase t 0) ((A : ℝ) + 1 / 2) := by
  have := expI_phase_halfInt t A ν (-1) (Or.inr rfl)
  rwa [neg_one_mul] at this

/-- The combined first-order boundary amplitude `h_{+}(u) + h_{-}(u)` of the frequencies `±2πν`. -/
def Ha (t ν u : ℝ) : ℝ := ampH t (2 * Real.pi * ν) u + ampH t (-(2 * Real.pi * ν)) u

/-- The `ν`-th Poisson integral `∫_a^b u^(-s) 2 cos(2πνu) du`, as the sum of the two
oscillatory integrals of frequencies `±2πν`. -/
def Fν (t ν a b : ℝ) : ℂ := mI t (2 * Real.pi * ν) a b + mI t (-(2 * Real.pi * ν)) a b

/-- The endpoint factor `a^{-it} = e^{-it log a}`. -/
def E0 (t u : ℝ) : ℂ := expI (phase t 0) u

theorem bdry_pair_halfInt (t : ℝ) (A ν : ℕ) :
    bdry t (2 * Real.pi * ν) ((A : ℝ) + 1 / 2) + bdry t (-(2 * Real.pi * ν)) ((A : ℝ) + 1 / 2)
      = (Ha t ν ((A : ℝ) + 1 / 2) : ℂ) * ((-1 : ℂ) ^ ν * E0 t ((A : ℝ) + 1 / 2)) := by
  unfold bdry Ha E0
  rw [expI_phase_pos_halfInt, expI_phase_neg_halfInt]
  push_cast; ring

theorem norm_Ha_term (t ν u : ℝ) (ν' : ℕ) :
    ‖I * ((Ha t ν u : ℂ) * ((-1 : ℂ) ^ ν' * E0 t u))‖ = |Ha t ν u| := by
  simp [E0, Complex.norm_real]

/-- **The `ν`-th Poisson integral, stationary point inside `(a, b)`.** -/
theorem norm_Fν_sub_main_le {t : ℝ} (ht : 0 < t) {A B ν : ℕ} (hν : 1 ≤ ν) (hAB : A ≤ B)
    (hat : 2 * Real.pi * ν * ((A : ℝ) + 1 / 2) < t) (hbt : t < 2 * Real.pi * ν * ((B : ℝ) + 1 / 2)) :
    ‖Fν t ν ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)
        - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        - I * ((Ha t ν ((A : ℝ) + 1 / 2) : ℂ) * ((-1 : ℂ) ^ ν * E0 t ((A : ℝ) + 1 / 2)))‖
      ≤ 2 * (|ampK t (2 * Real.pi * ν) ((A : ℝ) + 1 / 2)| + |ampK t (2 * Real.pi * ν) ((B : ℝ) + 1 / 2)|)
        + (ν : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t))
        + 2 / ((2 * Real.pi * ν) ^ 2 * (((A : ℝ) + 1 / 2) * Real.sqrt ((A : ℝ) + 1 / 2)))
        + |Ha t ν ((B : ℝ) + 1 / 2)| := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by rw [ha, hb]; have : (A : ℝ) ≤ B := by exact_mod_cast hAB
                         linarith
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν
  have hP := norm_integral_sub_zetaChi_add_boundary_le ht hν0 ha0 hat hbt
  have hQ := norm_mI_neg_add_boundary_le ht.le (by positivity : (0 : ℝ) < 2 * Real.pi * ν) ha0 hab
  have hpa := bdry_pair_halfInt t A ν
  have hpb := bdry_pair_halfInt t B ν
  rw [← ha] at hpa; rw [← hb] at hpb
  have hcast : ((ν : ℝ) : ℂ) = (ν : ℂ) := by push_cast; rfl
  rw [hcast] at hP
  have e : Fν t ν a b - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        - I * ((Ha t ν a : ℂ) * ((-1 : ℂ) ^ ν * E0 t a))
      = (mI t (2 * Real.pi * ν) a b - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
          + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a))
        + (mI t (-(2 * Real.pi * ν)) a b + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a))
        - I * ((Ha t ν b : ℂ) * ((-1 : ℂ) ^ ν * E0 t b)) := by
    rw [← hpb]
    have : I * ((Ha t ν a : ℂ) * ((-1 : ℂ) ^ ν * E0 t a))
        = I * (bdry t (2 * Real.pi * ν) a + bdry t (-(2 * Real.pi * ν)) a) := by rw [hpa]
    rw [this]; unfold Fν; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_Ha_term]
  have := norm_add_le (mI t (2 * Real.pi * ν) a b - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
          + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a))
        (mI t (-(2 * Real.pi * ν)) a b + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a))
  linarith

/-- **The `ν`-th Poisson integral, no stationary point** (`2πνa > t`). -/
theorem norm_Fν_sub_boundary_le {t : ℝ} (ht : 0 < t) {A B ν : ℕ} (hAB : A ≤ B)
    (hat : t < 2 * Real.pi * ν * ((A : ℝ) + 1 / 2)) :
    ‖Fν t ν ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)
        - I * ((Ha t ν ((A : ℝ) + 1 / 2) : ℂ) * ((-1 : ℂ) ^ ν * E0 t ((A : ℝ) + 1 / 2)))‖
      ≤ 2 * (|ampK t (2 * Real.pi * ν) ((A : ℝ) + 1 / 2)| + |ampK t (2 * Real.pi * ν) ((B : ℝ) + 1 / 2)|)
        + 2 / ((2 * Real.pi * ν) ^ 2 * (((A : ℝ) + 1 / 2) * Real.sqrt ((A : ℝ) + 1 / 2)))
        + |Ha t ν ((B : ℝ) + 1 / 2)| := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by rw [ha, hb]; have : (A : ℝ) ≤ B := by exact_mod_cast hAB
                         linarith
  have hω : 0 < 2 * Real.pi * ν := by
    by_contra h; push Not at h
    have : 2 * Real.pi * ν * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ha0.le
    linarith
  have hne : ∀ u ∈ Icc a b, 2 * Real.pi * ν * u - t ≠ 0 := by
    intro u hu
    have : 2 * Real.pi * ν * a ≤ 2 * Real.pi * ν * u := mul_le_mul_of_nonneg_left hu.1 hω.le
    linarith
  have hP := norm_integral_add_boundary_le_of_pos ht.le hω.le ha0 hab hne
  have hQ := norm_mI_neg_add_boundary_le ht.le hω ha0 hab
  have hpa := bdry_pair_halfInt t A ν
  have hpb := bdry_pair_halfInt t B ν
  rw [← ha] at hpa; rw [← hb] at hpb
  have e : Fν t ν a b - I * ((Ha t ν a : ℂ) * ((-1 : ℂ) ^ ν * E0 t a))
      = (mI t (2 * Real.pi * ν) a b + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a))
        + (mI t (-(2 * Real.pi * ν)) a b + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a))
        - I * ((Ha t ν b : ℂ) * ((-1 : ℂ) ^ ν * E0 t b)) := by
    rw [← hpb]
    have : I * ((Ha t ν a : ℂ) * ((-1 : ℂ) ^ ν * E0 t a))
        = I * (bdry t (2 * Real.pi * ν) a + bdry t (-(2 * Real.pi * ν)) a) := by rw [hpa]
    rw [this]; unfold Fν; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_Ha_term]
  have := norm_add_le (mI t (2 * Real.pi * ν) a b + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a))
        (mI t (-(2 * Real.pi * ν)) a b + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a))
  linarith

/-- **The `ν`-th Poisson integral near the stationary point**: a plain bound. -/
theorem norm_Fν_le_of_near {t : ℝ} (ht : 0 < t) {ν a b : ℝ} (hν : 0 < ν) (ha : 0 < a)
    (h2ab : 2 * a ≤ b) (h2a : t < 2 * Real.pi * ν * (2 * a)) :
    ‖Fν t ν a b‖ ≤ 24 * Real.sqrt a / Real.sqrt t + 2 * ampH t (2 * Real.pi * ν) (2 * a)
      + 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a))
      + |ampH t (-(2 * Real.pi * ν)) a| + |ampH t (-(2 * Real.pi * ν)) b| := by
  have hab : a ≤ b := by linarith
  have hω : 0 < 2 * Real.pi * ν := by positivity
  have h1 := norm_mI_le_of_near ht ha h2ab h2a
  have hQ := norm_mI_neg_add_boundary_le ht.le hω ha hab
  have h2 : ‖mI t (-(2 * Real.pi * ν)) a b‖ ≤ 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a))
      + |ampH t (-(2 * Real.pi * ν)) a| + |ampH t (-(2 * Real.pi * ν)) b| := by
    have e : mI t (-(2 * Real.pi * ν)) a b
        = (mI t (-(2 * Real.pi * ν)) a b + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a))
          - I * bdry t (-(2 * Real.pi * ν)) b + I * bdry t (-(2 * Real.pi * ν)) a := by ring
    rw [e]
    set P := mI t (-(2 * Real.pi * ν)) a b
      + I * (bdry t (-(2 * Real.pi * ν)) b - bdry t (-(2 * Real.pi * ν)) a)
    have k1 := norm_add_le (P - I * bdry t (-(2 * Real.pi * ν)) b) (I * bdry t (-(2 * Real.pi * ν)) a)
    have k2 := norm_sub_le P (I * bdry t (-(2 * Real.pi * ν)) b)
    simp only [norm_mul, norm_I, one_mul, norm_bdry] at k1 k2
    linarith
  unfold Fν
  refine (norm_add_le _ _).trans ?_
  linarith

/-! ## Poisson summation and Theorem 4.11 -/

/-- `2 u^(-s) cos(2πνu) = u^(-1/2) (e^{iΦ₊(u)} + e^{iΦ₋(u)})`. -/
theorem two_cpow_mul_cos_eq (t ν : ℝ) {u : ℝ} (hu : 0 < u) :
    2 * ((u : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * (Real.cos (2 * Real.pi * ν * u) : ℂ))
      = ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t (2 * Real.pi * ν)) u
        + ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t (-(2 * Real.pi * ν))) u := by
  rw [← cpow_mul_exp_eq t _ hu, ← cpow_mul_exp_eq t _ hu, Complex.ofReal_cos, Complex.cos]
  push_cast
  have e1 : I * (-(2 * (Real.pi : ℂ) * ν) * u) = -((2 * Real.pi * ν * u : ℂ) * I) := by ring
  have e2 : I * (2 * (Real.pi : ℂ) * ν * u) = (2 * Real.pi * ν * u : ℂ) * I := by ring
  rw [e1, e2]
  ring_nf

theorem two_integral_eq_Fν (t ν : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * ∫ x in a..b, (x : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * (Real.cos (2 * Real.pi * ν * x) : ℂ)
      = Fν t ν a b := by
  rw [← intervalIntegral.integral_const_mul]
  unfold Fν mI
  rw [← intervalIntegral.integral_add (intervalIntegrable_mellin' t _ ha.le (ha.le.trans hab))
    (intervalIntegrable_mellin' t _ ha.le (ha.le.trans hab))]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hab] at hx
  exact two_cpow_mul_cos_eq t ν (lt_of_lt_of_le ha hx.1)

theorem continuousOn_ofReal_cpow {r : ℂ} {S : Set ℝ} (hS : ∀ x ∈ S, 0 < x) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) S := by
  by_cases hr : r = 0
  · subst hr; simp only [cpow_zero]; exact continuousOn_const
  intro x hx
  exact (hasDerivAt_ofReal_cpow_const (hS x hx).ne' hr).continuousAt.continuousWithinAt

/-- **Poisson summation for `n^(-s)` between half-integers.** -/
theorem hasSum_Fν (t : ℝ) {A B : ℕ} (hAB : A ≤ B) :
    HasSum (fun n : ℕ => Fν t ((n + 1 : ℕ) : ℝ) ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))
      (∑ k ∈ Ioc A B, (k : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
        - ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2), (x : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))) := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  have hs0 : -s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this
  have hs1 : -s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; norm_num at this
  have hs2 : -s - 1 - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; norm_num at this
  have hpos : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), 0 < x := fun x hx =>
    lt_of_lt_of_le (by positivity) hx.1
  have h := PoissonInterval.hasSum_sum_Ioc_halfInt hAB (G := fun x : ℝ => (x : ℂ) ^ (-s))
    (G' := fun x : ℝ => -s * (x : ℂ) ^ (-s - 1))
    (G'' := fun x : ℝ => -s * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
    (fun x hx => hasDerivAt_ofReal_cpow_const (hpos x hx).ne' hs0)
    (fun x hx => (hasDerivAt_ofReal_cpow_const (hpos x hx).ne' hs1).const_mul _)
    (continuousOn_const.mul (continuousOn_const.mul (continuousOn_ofReal_cpow hpos)))
  have hab : (A : ℝ) + 1 / 2 ≤ (B : ℝ) + 1 / 2 := by
    have : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith
  have key : (fun n : ℕ => Fν t ((n + 1 : ℕ) : ℝ) ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))
      = fun n : ℕ => 2 * ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2),
          (x : ℂ) ^ (-s) * (Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) : ℂ) := by
    funext n
    exact (two_integral_eq_Fν t _ (by positivity) hab).symm
  rw [key]
  convert h using 2
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- **Reduction of the approximate functional equation to the Poisson series.**  With
`a = N + 1/2`, `b = B + 1/2 ≥ t` and `S = ∑_{ν ≥ 1} F_ν` the Poisson series of `n^(-s)` on
`(a, b]`, for every `X`:
`‖ζ(s) − ∑_{n ≤ N} n^(-s) − X‖ ≤ 11 b^(-1/2) + √a/t + ‖S − X‖`. -/
theorem norm_zeta_sub_zetaSum_sub_le {t : ℝ} (ht : 0 < t) {N B : ℕ} (hNB : N ≤ B)
    (hBt : t ≤ (B : ℝ) + 1 / 2) {S : ℂ}
    (hS : HasSum (fun n : ℕ => Fν t ((n + 1 : ℕ) : ℝ) ((N : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)) S)
    (X : ℂ) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum N (1 / 2 + (t : ℂ) * I) - X‖
      ≤ 11 * ((B : ℝ) + 1 / 2) ^ (-(1 / 2 : ℝ)) + Real.sqrt ((N : ℝ) + 1 / 2) / t + ‖S - X‖ := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  set a : ℝ := (N : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hab : a ≤ b := by rw [ha, hb]; have : (N : ℝ) ≤ B := by exact_mod_cast hNB
                         linarith
  have hS' := hasSum_Fν t hNB
  rw [← ha, ← hb] at hS'
  have hSeq := hS.unique hS'
  -- Theorem 4.11 at `x = b`
  have h411 := ZetaPartialSum.norm_riemannZeta_criticalLine_sub_partialSum_le hb0
    (by rw [abs_of_pos ht]; exact hBt)
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [hhalf, hb, PoissonInterval.floor_halfInt, ← hb] at h411
  -- the integral
  have hint : ∫ x in a..b, (x : ℂ) ^ (-s) = ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_cpow (Or.inl (by simp [hs]; norm_num))]
    rw [show -s + 1 = 1 - s by ring]
  -- the sums
  have hsum : ∑ n ∈ Icc 1 B, (n : ℂ) ^ (-s) = zetaSum N s + ∑ k ∈ Ioc N B, (k : ℂ) ^ (-s) := by
    unfold zetaSum
    rw [show Finset.Icc 1 B = Finset.Icc (0 + 1) B from rfl,
      show Finset.Icc 1 N = Finset.Icc (0 + 1) N from rfl,
      Finset.Icc_add_one_left_eq_Ioc, Finset.Icc_add_one_left_eq_Ioc]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNB).symm
  have h1s : (1 : ℂ) - s = 1 / 2 - (t : ℂ) * I := by rw [hs]; ring
  rw [← h1s, ← hs, hsum] at h411
  have hid : riemannZeta s - zetaSum N s - X
      = (riemannZeta s - (zetaSum N s + ∑ k ∈ Ioc N B, (k : ℂ) ^ (-s)) + (b : ℂ) ^ (1 - s) / (1 - s))
        + (S - X) - (a : ℂ) ^ (1 - s) / (1 - s) := by
    rw [hSeq, hint]; ring
  rw [hid]
  have hA : ‖(a : ℂ) ^ (1 - s) / (1 - s)‖ ≤ Real.sqrt a / t := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
    have hre : (1 - s).re = 1 / 2 := by rw [h1s]; simp
    rw [hre, ← Real.sqrt_eq_rpow]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) ht
    have : |(1 - s).im| ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
    rw [h1s] at this ⊢
    simp at this
    rw [abs_of_pos ht] at this
    rw [one_div]; exact this
  calc _ ≤ ‖riemannZeta s - (zetaSum N s + ∑ k ∈ Ioc N B, (k : ℂ) ^ (-s)) + (b : ℂ) ^ (1 - s) / (1 - s)‖
        + ‖S - X‖ + ‖(a : ℂ) ^ (1 - s) / (1 - s)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by linarith

/-! ## Explicit per-frequency bounds -/

theorem Ha_eq {t ν u : ℝ} (ht : 0 < t) (hν : 0 ≤ ν) (hu : 0 < u) (hne : 2 * Real.pi * ν * u ≠ t) :
    Ha t ν u = 2 * t * Real.sqrt u / ((2 * Real.pi * ν * u) ^ 2 - t ^ 2) := by
  have h1 : 2 * Real.pi * ν * u - t ≠ 0 := sub_ne_zero.mpr hne
  have h2 : -(2 * Real.pi * ν) * u - t ≠ 0 := by
    have : 0 ≤ 2 * Real.pi * ν * u := by positivity
    intro h; linarith
  have h3 : (2 * Real.pi * ν * u) ^ 2 - t ^ 2 ≠ 0 := by
    have : (2 * Real.pi * ν * u) ^ 2 - t ^ 2 = (2 * Real.pi * ν * u - t) * (2 * Real.pi * ν * u + t) := by ring
    rw [this]; apply mul_ne_zero h1
    have : 0 ≤ 2 * Real.pi * ν * u := by positivity
    linarith
  have hp : 2 * Real.pi * ν * u + t ≠ 0 := by
    have : 0 ≤ 2 * Real.pi * ν * u := by positivity
    linarith
  unfold Ha ampH
  rw [show -(2 * Real.pi * ν) * u - t = -(2 * Real.pi * ν * u + t) by ring,
    div_add_div _ _ h1 (neg_ne_zero.mpr hp), div_eq_div_iff (mul_ne_zero h1 (neg_ne_zero.mpr hp)) h3]
  ring

theorem abs_ampK_le_far {t ω u D : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (hω : 0 ≤ ω) (hD : 0 < D)
    (hd : D ≤ |ω * u - t|) :
    |ampK t ω u| ≤ Real.sqrt u * (1 / 2 + t / D) / (ω * u - t) ^ 2 := by
  have hs := Real.sqrt_nonneg u
  have hdpos : 0 < |ω * u - t| := lt_of_lt_of_le hD hd
  set d := |ω * u - t| with hdd
  have hsq : (ω * u - t) ^ 2 = d ^ 2 := (sq_abs _).symm
  unfold ampK
  rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hs, abs_mul, abs_pow, ← hdd, abs_of_pos (by norm_num : (0:ℝ) < 2),
    hsq, abs_of_nonneg (by positivity : 0 ≤ ω * u + t)]
  have hnum : ω * u + t ≤ d + 2 * t := by
    have := le_abs_self (ω * u - t); linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have htD : t / D * D = t := div_mul_cancel₀ t hD.ne'
  have key : (ω * u + t) * d ^ 2 ≤ (1 / 2 + t / D) * (2 * d ^ 3) := by
    have h1 : (ω * u + t) * d ^ 2 ≤ (d + 2 * t) * d ^ 2 := by gcongr
    have h2 : 2 * t * d ^ 2 ≤ 2 * (t / D) * d ^ 3 := by
      have : t * d ^ 2 = (t / D) * D * d ^ 2 := by rw [htD]
      rw [show 2 * t * d ^ 2 = 2 * (t * d ^ 2) by ring, this]
      have : 0 ≤ t / D := by positivity
      have : (t / D) * D * d ^ 2 ≤ (t / D) * d * d ^ 2 := by gcongr
      nlinarith
    nlinarith
  calc Real.sqrt u * (ω * u + t) * d ^ 2 = Real.sqrt u * ((ω * u + t) * d ^ 2) := by ring
    _ ≤ Real.sqrt u * ((1 / 2 + t / D) * (2 * d ^ 3)) := by gcongr
    _ = _ := by ring

theorem abs_Ha_b_le {t ν b : ℝ} (ht : 0 < t) (hν : 0 < ν) (hb : 0 < b)
    (hbt : 2 * t ≤ 2 * Real.pi * ν * b) :
    |Ha t ν b| ≤ 3 * t / ((2 * Real.pi * ν) ^ 2 * (b * Real.sqrt b)) := by
  have hW : 0 < 2 * Real.pi * ν * b := by positivity
  rw [Ha_eq ht hν.le hb (by linarith)]
  have hden : 3 / 4 * (2 * Real.pi * ν * b) ^ 2 ≤ (2 * Real.pi * ν * b) ^ 2 - t ^ 2 := by nlinarith
  have hden0 : 0 < (2 * Real.pi * ν * b) ^ 2 - t ^ 2 := by nlinarith
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.mul_self_sqrt hb.le
  rw [abs_of_pos (by positivity), div_le_div_iff₀ hden0 (by positivity)]
  have e : (2 * Real.pi * ν * b) ^ 2 = (2 * Real.pi * ν) ^ 2 * b * (Real.sqrt b * Real.sqrt b) := by
    rw [hs2]; ring
  have h1 : 2 * t * Real.sqrt b * ((2 * Real.pi * ν) ^ 2 * (b * Real.sqrt b))
      = 2 * t * (2 * Real.pi * ν * b) ^ 2 := by rw [e]; ring
  rw [h1]
  have : 0 < t := ht
  nlinarith

/-- Per-frequency remainder in the upper range, `ν ≥ c + 1`. -/
theorem upper_rem_le {t c a b ν : ℝ} (ht : 0 < t) (ha : 0 < a) (hc : t = 2 * Real.pi * a * c)
    (hb1 : 1 ≤ b) (hbt : 2 * t ≤ 2 * Real.pi * b) (hν : c + 1 ≤ ν) :
    2 * (|ampK t (2 * Real.pi * ν) a| + |ampK t (2 * Real.pi * ν) b|)
        + 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a)) + |Ha t ν b|
      ≤ (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 12 / (4 * Real.pi ^ 2 * Real.sqrt b)
          + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)))
        / (ν - c) ^ 2 := by
  have hc0 : 0 < c := by
    have : 0 < 2 * Real.pi * a := by positivity
    by_contra h; push Not at h; nlinarith
  have hν0 : 0 < ν := by linarith
  have hb0 : 0 < b := by linarith
  have hd : 0 < ν - c := by linarith
  have hd2 : (ν - c) ^ 2 ≤ ν ^ 2 := by nlinarith
  have hsa := Real.sqrt_pos.mpr ha
  have hsb := Real.sqrt_pos.mpr hb0
  have hpi := Real.pi_pos
  -- `|k(a)|`
  have hka : |ampK t (2 * Real.pi * ν) a| ≤ (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (ν - c) ^ 2 := by
    have hD : 2 * Real.pi * a ≤ |2 * Real.pi * ν * a - t| := by
      rw [hc, show 2 * Real.pi * ν * a - 2 * Real.pi * a * c = 2 * Real.pi * a * (ν - c) by ring,
        abs_of_pos (by positivity)]
      have : 0 < 2 * Real.pi * a := by positivity
      nlinarith
    refine (abs_ampK_le_far ha ht.le (by positivity) (by positivity) hD).trans (le_of_eq ?_)
    rw [show t / (2 * Real.pi * a) = c by rw [hc]; field_simp,
      show 2 * Real.pi * ν * a - t = 2 * Real.pi * a * (ν - c) by rw [hc]; ring]
    have hs2 := Real.mul_self_sqrt ha.le
    field_simp
    rw [Real.sq_sqrt ha.le]; ring
  have hkb : |ampK t (2 * Real.pi * ν) b| ≤ 6 / (4 * Real.pi ^ 2 * Real.sqrt b) / (ν - c) ^ 2 := by
    have hbt' : 2 * t ≤ 2 * Real.pi * ν * b := by nlinarith
    refine (abs_ampK_le_of_large ht.le (by positivity) hb1 hbt').trans ?_
    rw [div_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : 4 * Real.pi ^ 2 * (ν - c) ^ 2 ≤ (2 * Real.pi * ν) ^ 2 := by nlinarith
    calc 4 * Real.pi ^ 2 * Real.sqrt b * (ν - c) ^ 2 = 4 * Real.pi ^ 2 * (ν - c) ^ 2 * Real.sqrt b := by ring
      _ ≤ (2 * Real.pi * ν) ^ 2 * Real.sqrt b := by gcongr
  have h3 : 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a))
      ≤ 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (ν - c) ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : 4 * Real.pi ^ 2 * (ν - c) ^ 2 ≤ (2 * Real.pi * ν) ^ 2 := by nlinarith
    calc 4 * Real.pi ^ 2 * (a * Real.sqrt a) * (ν - c) ^ 2
        = 4 * Real.pi ^ 2 * (ν - c) ^ 2 * (a * Real.sqrt a) := by ring
      _ ≤ (2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a) := by gcongr
  have h4 : |Ha t ν b| ≤ 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)) / (ν - c) ^ 2 := by
    have hbt' : 2 * t ≤ 2 * Real.pi * ν * b := by nlinarith
    refine (abs_Ha_b_le ht hν0 hb0 hbt').trans ?_
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : 4 * Real.pi ^ 2 * (ν - c) ^ 2 ≤ (2 * Real.pi * ν) ^ 2 := by nlinarith
    calc 4 * Real.pi ^ 2 * (b * Real.sqrt b) * (ν - c) ^ 2
        = 4 * Real.pi ^ 2 * (ν - c) ^ 2 * (b * Real.sqrt b) := by ring
      _ ≤ (2 * Real.pi * ν) ^ 2 * (b * Real.sqrt b) := by gcongr
  have e : (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 12 / (4 * Real.pi ^ 2 * Real.sqrt b)
          + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)))
        / (ν - c) ^ 2
      = 2 * ((1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (ν - c) ^ 2
          + 6 / (4 * Real.pi ^ 2 * Real.sqrt b) / (ν - c) ^ 2)
        + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (ν - c) ^ 2
        + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)) / (ν - c) ^ 2 := by ring
  rw [e]
  gcongr

theorem abs_ampK_a_le {t c a ν : ℝ} (ht : 0 < t) (ha : 0 < a) (hc : t = 2 * Real.pi * a * c)
    (hν : 0 ≤ ν) (hd : 1 ≤ |ν - c|) :
    |ampK t (2 * Real.pi * ν) a| ≤ (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (ν - c) ^ 2 := by
  have hpa : 0 < 2 * Real.pi * a := by positivity
  have hD : 2 * Real.pi * a ≤ |2 * Real.pi * ν * a - t| := by
    rw [hc, show 2 * Real.pi * ν * a - 2 * Real.pi * a * c = 2 * Real.pi * a * (ν - c) by ring,
      abs_mul, abs_of_pos hpa]
    nlinarith
  refine (abs_ampK_le_far ha ht.le (by positivity) hpa hD).trans (le_of_eq ?_)
  have hsa := Real.sqrt_pos.mpr ha
  have hd0 : ν - c ≠ 0 := by intro h; rw [h, abs_zero] at hd; linarith
  rw [show t / (2 * Real.pi * a) = c by rw [hc]; field_simp,
    show 2 * Real.pi * ν * a - t = 2 * Real.pi * a * (ν - c) by rw [hc]; ring]
  field_simp
  rw [Real.sq_sqrt ha.le]; ring

/-- Per-frequency remainder in the lower range, `1 ≤ ν ≤ c − 1`. -/
theorem lower_rem_le {t c a b ν : ℝ} (ht : 0 < t) (ha : 0 < a) (hc : t = 2 * Real.pi * a * c)
    (hb1 : 1 ≤ b) (hbt : 2 * t ≤ 2 * Real.pi * b) (hν1 : 1 ≤ ν) (hνc : ν + 1 ≤ c) :
    2 * (|ampK t (2 * Real.pi * ν) a| + |ampK t (2 * Real.pi * ν) b|)
        + ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t))
        + 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a)) + |Ha t ν b|
      ≤ 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (c - ν) ^ 2
        + (12 / (4 * Real.pi ^ 2 * Real.sqrt b) + Real.exp (-(Real.pi * t))
          + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))) := by
  have hν0 : 0 < ν := by linarith
  have hb0 : 0 < b := by linarith
  have hsa := Real.sqrt_pos.mpr ha
  have hsb := Real.sqrt_pos.mpr hb0
  have hpi := Real.pi_pos
  have hka := abs_ampK_a_le ht ha hc hν0.le (by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith)
  rw [show (ν - c) ^ 2 = (c - ν) ^ 2 by ring] at hka
  have h4pi : 4 * Real.pi ^ 2 ≤ (2 * Real.pi * ν) ^ 2 := by
    have h1 : 1 ≤ ν ^ 2 := by nlinarith
    have h2 : (2 * Real.pi * ν) ^ 2 = 4 * Real.pi ^ 2 * ν ^ 2 := by ring
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)
    linarith
  have hkb : |ampK t (2 * Real.pi * ν) b| ≤ 6 / (4 * Real.pi ^ 2 * Real.sqrt b) := by
    have hbt' : 2 * t ≤ 2 * Real.pi * ν * b := by nlinarith
    refine (abs_ampK_le_of_large ht.le (by positivity) hb1 hbt').trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have h3 : 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a)) ≤ 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have h4 : |Ha t ν b| ≤ 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)) := by
    have hbt' : 2 * t ≤ 2 * Real.pi * ν * b := by nlinarith
    refine (abs_Ha_b_le ht hν0 hb0 hbt').trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have h5 : ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) ≤ Real.exp (-(Real.pi * t)) := by
    have : ν ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hν1 (by norm_num)
    have := Real.exp_pos (-(Real.pi * t))
    nlinarith
  have e : 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (c - ν) ^ 2
      = 2 * ((1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (c - ν) ^ 2) := by ring
  have e2 : 12 / (4 * Real.pi ^ 2 * Real.sqrt b) = 2 * (6 / (4 * Real.pi ^ 2 * Real.sqrt b)) := by ring
  rw [e, e2]
  set K1 := (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / (c - ν) ^ 2
  set K2 := 6 / (4 * Real.pi ^ 2 * Real.sqrt b)
  set K3 := 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a))
  set K4 := 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))
  set K5 := Real.exp (-(Real.pi * t))
  linarith

/-! ## The lower and upper ranges of frequencies -/

/-- The coefficient of the upper-range remainder. -/
def remQ (t c a b : ℝ) : ℝ :=
  2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 12 / (4 * Real.pi ^ 2 * Real.sqrt b)
    + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))

theorem remQ_nonneg {t c a b : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ remQ t c a b := by
  unfold remQ; positivity

theorem norm_I_Ha_sum' (t a : ℝ) (S : Finset ℕ) (f : ℕ → ℝ) (e : ℕ → ℕ) :
    ‖∑ ν ∈ S, I * ((f ν : ℂ) * ((-1 : ℂ) ^ e ν * E0 t a))‖ = |∑ ν ∈ S, (-1 : ℝ) ^ e ν * f ν| := by
  have e : ∑ ν ∈ S, I * ((f ν : ℂ) * ((-1 : ℂ) ^ e ν * E0 t a))
      = I * E0 t a * ((∑ ν ∈ S, (-1 : ℝ) ^ e ν * f ν : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_; ring
  rw [e, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs]
  simp [E0]

theorem norm_I_Ha_sum (t a : ℝ) (S : Finset ℕ) (f : ℕ → ℝ) :
    ‖∑ ν ∈ S, I * ((f ν : ℂ) * ((-1 : ℂ) ^ ν * E0 t a))‖ = |∑ ν ∈ S, (-1 : ℝ) ^ ν * f ν| :=
  norm_I_Ha_sum' t a S f id

/-- **The upper range** `ν ≥ n₂ ≥ c + 1` (no stationary point). -/
theorem norm_sum_upper_le {t c : ℝ} {A B n2 : ℕ} (M : ℕ) (ht : 0 < t) (hAB : A ≤ B)
    (hc : t = 2 * Real.pi * ((A : ℝ) + 1 / 2) * c) (hb1 : 1 ≤ (B : ℝ) + 1 / 2)
    (hbt : 2 * t ≤ 2 * Real.pi * ((B : ℝ) + 1 / 2)) (hn2 : c + 1 ≤ n2) :
    ‖∑ ν ∈ Finset.Ico n2 M, Fν t ν ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)‖
      ≤ 1 / (2 * Real.pi * Real.sqrt ((A : ℝ) + 1 / 2))
        + 2 * remQ t c ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2) := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have ha0 : 0 < a := by positivity
  have hpa : 0 < 2 * Real.pi * a := by positivity
  have hc0 : 0 < c := by
    by_contra h; push Not at h
    have : 2 * Real.pi * a * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpa.le h
    linarith
  have hνbig : ∀ ν : ℕ, n2 ≤ ν → t + 2 * Real.pi * a ≤ 2 * Real.pi * ν * a := by
    intro ν hν
    have : (n2 : ℝ) ≤ ν := by exact_mod_cast hν
    have : c + 1 ≤ ν := by linarith
    rw [hc]; nlinarith
  set Iterm : ℕ → ℂ := fun ν => I * ((Ha t ν a : ℂ) * ((-1 : ℂ) ^ ν * E0 t a)) with hIterm
  have hsplit : ∑ ν ∈ Finset.Ico n2 M, Fν t ν a b
      = ∑ ν ∈ Finset.Ico n2 M, (Fν t ν a b - Iterm ν) + ∑ ν ∈ Finset.Ico n2 M, Iterm ν := by
    rw [← Finset.sum_add_distrib]; simp
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) |>.trans_eq (add_comm _ _)
  · -- the remainders
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ ν ∈ Finset.Ico n2 M, ‖Fν t ν a b - Iterm ν‖
        ≤ remQ t c a b / ((ν : ℝ) - c) ^ 2 := by
      intro ν hν
      have hν' := (Finset.mem_Ico.mp hν).1
      have h1 := norm_Fν_sub_boundary_le (B := B) ht hAB (by linarith [hνbig ν hν'] :
        t < 2 * Real.pi * ν * a)
      refine h1.trans ?_
      have : c + 1 ≤ (ν : ℝ) := by
        have : (n2 : ℝ) ≤ ν := by exact_mod_cast hν'
        linarith
      exact upper_rem_le ht ha0 hc hb1 hbt this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have e : ∑ j ∈ range (M - n2), remQ t c a b / (((n2 + j : ℕ) : ℝ) - c) ^ 2
        = remQ t c a b * ∑ j ∈ range (M - n2), 1 / (((n2 : ℝ) - c) + j) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; push_cast; ring
    rw [e]
    have hd : 1 ≤ (n2 : ℝ) - c := by linarith
    have hs := sum_inv_sq_shift_le hd (M - n2)
    have hQ : 0 ≤ remQ t c a b := remQ_nonneg ht.le hc0.le ha0.le (by linarith)
    have : 2 / ((n2 : ℝ) - c) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc remQ t c a b * ∑ j ∈ range (M - n2), 1 / (((n2 : ℝ) - c) + j) ^ 2
        ≤ remQ t c a b * 2 := by gcongr; linarith
      _ = 2 * remQ t c a b := by ring
  · -- the alternating boundary sum
    rw [hIterm, norm_I_Ha_sum, Finset.sum_Ico_eq_sum_range]
    set g : ℕ → ℝ := fun j => Ha t ((n2 + j : ℕ) : ℝ) a with hg
    have hgeq : ∀ j, g j = 2 * t * Real.sqrt a / ((2 * Real.pi * ((n2 + j : ℕ) : ℝ) * a) ^ 2 - t ^ 2) := by
      intro j
      have := hνbig (n2 + j) (by omega)
      exact Ha_eq ht (Nat.cast_nonneg _) ha0 (by linarith)
    have hden : ∀ j, (t + 2 * Real.pi * a) ^ 2 - t ^ 2 ≤ (2 * Real.pi * ((n2 + j : ℕ) : ℝ) * a) ^ 2 - t ^ 2 := by
      intro j
      have := hνbig (n2 + j) (by omega)
      have : 0 ≤ t + 2 * Real.pi * a := by positivity
      nlinarith
    have hden0 : 0 < (t + 2 * Real.pi * a) ^ 2 - t ^ 2 := by nlinarith
    have hanti : Antitone g := by
      apply antitone_nat_of_succ_le
      intro j
      rw [hgeq, hgeq]
      apply div_le_div_of_nonneg_left (by positivity) (lt_of_lt_of_le hden0 (hden j))
      have h1 := hνbig (n2 + j) (by omega)
      have h2 : (2 * Real.pi * ((n2 + j : ℕ) : ℝ) * a) ≤ 2 * Real.pi * ((n2 + (j + 1) : ℕ) : ℝ) * a := by
        push_cast; nlinarith
      have : 0 ≤ 2 * Real.pi * ((n2 + j : ℕ) : ℝ) * a := by positivity
      nlinarith
    have hnn : ∀ j, 0 ≤ g j := fun j => by
      rw [hgeq]; exact div_nonneg (by positivity) (le_trans hden0.le (hden j))
    have e : ∑ j ∈ range (M - n2), (-1 : ℝ) ^ (n2 + j) * Ha t ((n2 + j : ℕ) : ℝ) a
        = (-1 : ℝ) ^ n2 * ∑ j ∈ range (M - n2), (-1 : ℝ) ^ j * g j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [pow_add]; ring
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    refine (abs_alternating_sum_le hanti hnn _).trans ?_
    rw [hgeq, div_le_div_iff₀ (lt_of_lt_of_le hden0 (hden 0)) (by positivity)]
    have hsa := Real.sqrt_pos.mpr ha0
    have hsa2 := Real.mul_self_sqrt ha0.le
    have h0 := hden 0
    -- 2t√a · 2π√a = 4πat ≤ (t+2πa)² − t² ≤ den
    have : 2 * t * Real.sqrt a * (2 * Real.pi * Real.sqrt a) = 4 * Real.pi * a * t := by
      rw [show 2 * t * Real.sqrt a * (2 * Real.pi * Real.sqrt a) = 4 * Real.pi * t * (Real.sqrt a * Real.sqrt a) by ring, hsa2]; ring
    rw [this]
    have : 4 * Real.pi * a * t ≤ (t + 2 * Real.pi * a) ^ 2 - t ^ 2 := by nlinarith [Real.pi_pos]
    linarith

/-- The constant part of the lower-range remainder. -/
def remK (t a b : ℝ) : ℝ :=
  12 / (4 * Real.pi ^ 2 * Real.sqrt b) + Real.exp (-(Real.pi * t))
    + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))

/-- **The lower range** `1 ≤ ν ≤ n₁ ≤ c − 1` (stationary point inside), indexed by `j = n₁ − ν`. -/
theorem norm_sum_lower_le {t c : ℝ} {A B n1 : ℕ} (ht : 0 < t) (hAB : A ≤ B)
    (hc : t = 2 * Real.pi * ((A : ℝ) + 1 / 2) * c) (hb1 : 1 ≤ (B : ℝ) + 1 / 2)
    (hbt : 2 * t ≤ 2 * Real.pi * ((B : ℝ) + 1 / 2)) (hn1 : (n1 : ℝ) + 1 ≤ c) :
    ‖∑ j ∈ range n1, (Fν t ((n1 - j : ℕ) : ℝ) ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)
        - zetaChi (1 / 2 + (t : ℂ) * I) * ((n1 - j : ℕ) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1))‖
      ≤ 1 / (Real.pi * Real.sqrt ((A : ℝ) + 1 / 2))
        + 2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (((A : ℝ) + 1 / 2) * Real.sqrt ((A : ℝ) + 1 / 2))))
        + n1 * remK t ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2) := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  set χ := zetaChi (1 / 2 + (t : ℂ) * I) with hχ
  have ha0 : 0 < a := by positivity
  have hpa : 0 < 2 * Real.pi * a := by positivity
  have hνsmall : ∀ j : ℕ, 2 * Real.pi * ((n1 - j : ℕ) : ℝ) * a ≤ t - 2 * Real.pi * a := by
    intro j
    have : ((n1 - j : ℕ) : ℝ) ≤ n1 := by exact_mod_cast Nat.sub_le n1 j
    rw [hc]; nlinarith
  set Iterm : ℕ → ℂ := fun j =>
    I * ((Ha t ((n1 - j : ℕ) : ℝ) a : ℂ) * ((-1 : ℂ) ^ (n1 - j) * E0 t a)) with hIterm
  have hsplit : ∑ j ∈ range n1, (Fν t ((n1 - j : ℕ) : ℝ) a b - χ * ((n1 - j : ℕ) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1))
      = ∑ j ∈ range n1, (Fν t ((n1 - j : ℕ) : ℝ) a b - χ * ((n1 - j : ℕ) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
          - Iterm j) + ∑ j ∈ range n1, Iterm j := by
    rw [← Finset.sum_add_distrib]; simp
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hR : ‖∑ j ∈ range n1, (Fν t ((n1 - j : ℕ) : ℝ) a b - χ * ((n1 - j : ℕ) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
          - Iterm j)‖
      ≤ 2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a))) + n1 * remK t a b := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ range n1, ‖Fν t ((n1 - j : ℕ) : ℝ) a b
          - χ * ((n1 - j : ℕ) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1) - Iterm j‖
        ≤ 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / ((c - n1) + j) ^ 2
          + remK t a b := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hν1 : 1 ≤ n1 - j := by omega
      have hcast : ((n1 - j : ℕ) : ℝ) = n1 - j := by push_cast [Nat.cast_sub hj'.le]; ring
      have h1 := norm_Fν_sub_main_le (B := B) ht hν1 hAB
        (by rw [← ha]; linarith [hνsmall j]) (by
          have : (1 : ℝ) ≤ ((n1 - j : ℕ) : ℝ) := by exact_mod_cast hν1
          rw [← hb]; nlinarith)
      refine h1.trans ?_
      have h2 := lower_rem_le ht ha0 hc hb1 hbt (by exact_mod_cast hν1)
        (show ((n1 - j : ℕ) : ℝ) + 1 ≤ c by rw [hcast]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
      rw [hcast] at h2 ⊢
      rw [show c - ((n1 : ℝ) - j) = (c - n1) + j by ring] at h2
      exact h2
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ∑ j ∈ range n1, 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) / ((c - n1) + j) ^ 2
        = 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) * ∑ j ∈ range n1, 1 / ((c - n1) + j) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [e]
    have hd : 1 ≤ c - n1 := by linarith
    have hs := sum_inv_sq_shift_le hd n1
    have : 2 / (c - n1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hc0 : 0 ≤ c := by have : (0 : ℝ) ≤ n1 := Nat.cast_nonneg n1; linarith
    have hK : 0 ≤ 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) := by positivity
    have := mul_le_mul_of_nonneg_left (hs.trans this) hK
    linarith
  have hB : ‖∑ j ∈ range n1, Iterm j‖ ≤ 1 / (Real.pi * Real.sqrt a) := by
    rw [hIterm, norm_I_Ha_sum' t a (range n1) (fun j => Ha t ((n1 - j : ℕ) : ℝ) a) (fun j => n1 - j)]
    set g : ℕ → ℝ := fun j => 2 * t * Real.sqrt a / (t ^ 2 - (2 * Real.pi * ((n1 - j : ℕ) : ℝ) * a) ^ 2)
      with hg
    have hden : ∀ j, t ^ 2 - (t - 2 * Real.pi * a) ^ 2 ≤ t ^ 2 - (2 * Real.pi * ((n1 - j : ℕ) : ℝ) * a) ^ 2 := by
      intro j
      have := hνsmall j
      have : 0 ≤ 2 * Real.pi * ((n1 - j : ℕ) : ℝ) * a := by positivity
      nlinarith
    have htpa : 2 * Real.pi * a ≤ t := by
      rw [hc]; have : (1 : ℝ) ≤ c := by have : (0 : ℝ) ≤ n1 := Nat.cast_nonneg n1; linarith
      nlinarith
    have hden0 : 0 < t ^ 2 - (t - 2 * Real.pi * a) ^ 2 := by nlinarith
    have hHa : ∀ j, Ha t ((n1 - j : ℕ) : ℝ) a = -g j := by
      intro j
      rw [Ha_eq ht (Nat.cast_nonneg _) ha0 (by linarith [hνsmall j]), hg]
      simp only
      rw [← div_neg, neg_sub]
    have hanti : Antitone g := by
      apply antitone_nat_of_succ_le
      intro j
      simp only [hg]
      apply div_le_div_of_nonneg_left (by positivity) (lt_of_lt_of_le hden0 (hden j))
      have h1 : ((n1 - (j + 1) : ℕ) : ℝ) ≤ ((n1 - j : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have h2 : 0 ≤ ((n1 - (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      have h3 : 2 * Real.pi * ((n1 - (j + 1) : ℕ) : ℝ) * a ≤ 2 * Real.pi * ((n1 - j : ℕ) : ℝ) * a := by
        gcongr
      have h4 : 0 ≤ 2 * Real.pi * ((n1 - (j + 1) : ℕ) : ℝ) * a := by positivity
      nlinarith
    have hnn : ∀ j, 0 ≤ g j := fun j => by
      simp only [hg]; exact div_nonneg (by positivity) (le_trans hden0.le (hden j))
    have e : ∑ j ∈ range n1, (-1 : ℝ) ^ (n1 - j) * Ha t ((n1 - j : ℕ) : ℝ) a
        = -((-1 : ℝ) ^ n1 * ∑ j ∈ range n1, (-1 : ℝ) ^ j * g j) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [hHa]
      have : (-1 : ℝ) ^ n1 = (-1 : ℝ) ^ (n1 - j) * (-1 : ℝ) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hj'.le]
      rw [this]
      have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination ((-1 : ℝ) ^ (n1 - j) * g j) * hsq
    rw [e, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    refine (abs_alternating_sum_le hanti hnn _).trans ?_
    simp only [hg]
    rw [div_le_div_iff₀ (lt_of_lt_of_le hden0 (hden 0)) (by positivity)]
    have hsa := Real.sqrt_pos.mpr ha0
    have hsa2 := Real.mul_self_sqrt ha0.le
    have h0 := hden 0
    have : 2 * t * Real.sqrt a * (Real.pi * Real.sqrt a) = 2 * Real.pi * a * t := by
      rw [show 2 * t * Real.sqrt a * (Real.pi * Real.sqrt a) = 2 * Real.pi * t * (Real.sqrt a * Real.sqrt a) by ring, hsa2]; ring
    rw [this]
    have : 2 * Real.pi * a * t ≤ t ^ 2 - (t - 2 * Real.pi * a) ^ 2 := by nlinarith [Real.pi_pos]
    linarith
  linarith

/-! ## Near the stationary point, and the whole Poisson series -/

theorem abs_ampH_neg_eq {t ω u : ℝ} (ht : 0 < t) (hω : 0 ≤ ω) (hu : 0 < u) :
    |ampH t (-ω) u| = Real.sqrt u / (ω * u + t) := by
  unfold ampH
  have : 0 < ω * u + t := by positivity
  rw [show -ω * u - t = -(ω * u + t) by ring, div_neg, abs_neg, abs_of_nonneg (by positivity)]

/-- The bound for one frequency near the stationary point. -/
def remR (t a b : ℝ) : ℝ :=
  24 * Real.sqrt a / Real.sqrt t + 2 * (Real.sqrt (2 * a) / (2 * Real.pi * a))
    + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + Real.sqrt a / t + 1 / (2 * Real.pi * Real.sqrt b)

theorem norm_Fν_le_remR {t c a b ν : ℝ} (ht : 0 < t) (ha : 0 < a) (hc : t = 2 * Real.pi * a * c)
    (h2ab : 2 * a ≤ b) (hν1 : 1 ≤ ν) (hνc : c + 1 ≤ 2 * ν) :
    ‖Fν t ν a b‖ ≤ remR t a b := by
  have hν0 : 0 < ν := by linarith
  have hb0 : 0 < b := by linarith
  have hpi := Real.pi_pos
  have hω : 0 < 2 * Real.pi * ν := by positivity
  have hpa : 0 < 2 * Real.pi * a := by positivity
  have h2a : t + 2 * Real.pi * a ≤ 2 * Real.pi * ν * (2 * a) := by
    have := mul_le_mul_of_nonneg_left hνc hpa.le
    rw [hc]; linarith
  have h := norm_Fν_le_of_near ht hν0 ha h2ab (by linarith)
  refine h.trans ?_
  unfold remR
  have h1 : ampH t (2 * Real.pi * ν) (2 * a) ≤ Real.sqrt (2 * a) / (2 * Real.pi * a) := by
    unfold ampH
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    linarith
  have h4pi : 4 * Real.pi ^ 2 ≤ (2 * Real.pi * ν) ^ 2 := by
    have h1 : 1 ≤ ν ^ 2 := by nlinarith
    have h2 : (2 * Real.pi * ν) ^ 2 = 4 * Real.pi ^ 2 * ν ^ 2 := by ring
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)
    linarith
  have h2 : 2 / ((2 * Real.pi * ν) ^ 2 * (a * Real.sqrt a)) ≤ 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have h3 : |ampH t (-(2 * Real.pi * ν)) a| ≤ Real.sqrt a / t := by
    rw [abs_ampH_neg_eq ht hω.le ha]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) ht
    have : 0 ≤ 2 * Real.pi * ν * a := by positivity
    linarith
  have h4 : |ampH t (-(2 * Real.pi * ν)) b| ≤ 1 / (2 * Real.pi * Real.sqrt b) := by
    rw [abs_ampH_neg_eq ht hω.le hb0]
    have hsb := Real.sqrt_pos.mpr hb0
    have hsb2 := Real.mul_self_sqrt hb0.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * Real.pi * b ≤ 2 * Real.pi * ν * b + t := by nlinarith
    calc Real.sqrt b * (2 * Real.pi * Real.sqrt b) = 2 * Real.pi * (Real.sqrt b * Real.sqrt b) := by ring
      _ = 2 * Real.pi * b := by rw [hsb2]
      _ ≤ 2 * Real.pi * ν * b + t := this
      _ = 1 * (2 * Real.pi * ν * b + t) := by ring
  linarith

theorem sum_Ico_one_eq_sum_range_reflect (f : ℕ → ℂ) (n : ℕ) :
    ∑ ν ∈ Finset.Ico 1 (n + 1), f ν = ∑ j ∈ range n, f (n - j) := by
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  congr 1; omega

theorem zetaSumDual_split {N : ℕ} (hN : 2 ≤ N) (s : ℂ) :
    zetaSumDual N s = ∑ j ∈ range (N - 2), ((N - 2 - j : ℕ) : ℂ) ^ (s - 1)
      + ((N - 1 : ℕ) : ℂ) ^ (s - 1) + (N : ℂ) ^ (s - 1) := by
  unfold zetaSumDual
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega),
    show N = (N - 1) + 1 by omega, Finset.sum_Ico_succ_top (by omega),
    show N - 1 = (N - 2) + 1 by omega, sum_Ico_one_eq_sum_range_reflect (fun ν => (ν : ℂ) ^ (s - 1))]
  congr 2

/-- **The Poisson series minus the main terms.** -/
theorem norm_poisson_sub_main_le {t c : ℝ} {N B : ℕ} (ht : 0 < t) (hN : 5 ≤ N) (hNB : N ≤ B)
    (hc : t = 2 * Real.pi * ((N : ℝ) + 1 / 2) * c) (hcl : (N : ℝ) - 1 ≤ c) (hcu : c ≤ N + 2)
    (hb1 : 1 ≤ (B : ℝ) + 1 / 2) (hbt : 2 * t ≤ 2 * Real.pi * ((B : ℝ) + 1 / 2))
    (h2ab : 2 * ((N : ℝ) + 1 / 2) ≤ (B : ℝ) + 1 / 2) {S : ℂ}
    (hS : HasSum (fun n : ℕ => Fν t ((n + 1 : ℕ) : ℝ) ((N : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)) S) :
    ‖S - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual N (1 / 2 + (t : ℂ) * I)‖
      ≤ (1 / (Real.pi * Real.sqrt ((N : ℝ) + 1 / 2))
          + 2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (((N : ℝ) + 1 / 2) * Real.sqrt ((N : ℝ) + 1 / 2))))
          + ((N - 2 : ℕ) : ℝ) * remK t ((N : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))
        + 4 * remR t ((N : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)
        + 2 / Real.sqrt ((N : ℝ) - 1)
        + (1 / (2 * Real.pi * Real.sqrt ((N : ℝ) + 1 / 2))
          + 2 * remQ t c ((N : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2)) := by
  set a : ℝ := (N : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  set χ := zetaChi s with hχ
  have ha0 : 0 < a := by positivity
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
  set F : ℕ → ℂ := fun ν => Fν t ν a b with hF
  set bound := (1 / (Real.pi * Real.sqrt a) + 2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)))
          + ((N - 2 : ℕ) : ℝ) * remK t a b) + 4 * remR t a b + 2 / Real.sqrt ((N : ℝ) - 1)
        + (1 / (2 * Real.pi * Real.sqrt a) + 2 * remQ t c a b) with hbound
  have hlim := (hS.tendsto_sum_nat.sub_const (χ * zetaSumDual N s)).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (N + 2)] with M hM
  -- the partial sum as a sum over `ν ∈ [1, M]`
  have hP : ∑ n ∈ range M, Fν t ((n + 1 : ℕ) : ℝ) a b = ∑ ν ∈ Finset.Ico 1 (M + 1), F ν := by
    rw [Finset.sum_Ico_eq_sum_range, show M + 1 - 1 = M by omega]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hF]; congr 2; ring
  rw [hP]
  have hsplit : ∑ ν ∈ Finset.Ico 1 (M + 1), F ν
      = ∑ j ∈ range (N - 2), F (N - 2 - j) + ∑ ν ∈ Finset.Ico (N - 1) (N + 3), F ν
        + ∑ ν ∈ Finset.Ico (N + 3) (M + 1), F ν := by
    rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ N + 3 by omega) (show N + 3 ≤ M + 1 by omega),
      ← Finset.sum_Ico_consecutive _ (show 1 ≤ N - 1 by omega) (show N - 1 ≤ N + 3 by omega),
      show N - 1 = (N - 2) + 1 by omega, sum_Ico_one_eq_sum_range_reflect]
  rw [hsplit, zetaSumDual_split (by omega)]
  have hid : ∑ j ∈ range (N - 2), F (N - 2 - j) + ∑ ν ∈ Finset.Ico (N - 1) (N + 3), F ν
        + ∑ ν ∈ Finset.Ico (N + 3) (M + 1), F ν
        - χ * (∑ j ∈ range (N - 2), ((N - 2 - j : ℕ) : ℂ) ^ (s - 1) + ((N - 1 : ℕ) : ℂ) ^ (s - 1)
          + (N : ℂ) ^ (s - 1))
      = ∑ j ∈ range (N - 2), (F (N - 2 - j) - χ * ((N - 2 - j : ℕ) : ℂ) ^ (s - 1))
        + ∑ ν ∈ Finset.Ico (N - 1) (N + 3), F ν
        - χ * (((N - 1 : ℕ) : ℂ) ^ (s - 1) + (N : ℂ) ^ (s - 1))
        + ∑ ν ∈ Finset.Ico (N + 3) (M + 1), F ν := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [hid]
  -- the four pieces
  have h1 := norm_sum_lower_le (A := N) (B := B) (n1 := N - 2) (c := c) ht hNB hc hb1 hbt
    (by push_cast [Nat.cast_sub (show 2 ≤ N by omega)]; linarith)
  have h2 : ‖∑ ν ∈ Finset.Ico (N - 1) (N + 3), F ν‖ ≤ 4 * remR t a b := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ ν ∈ Finset.Ico (N - 1) (N + 3), ‖F ν‖ ≤ remR t a b := by
      intro ν hν
      have hν' := Finset.mem_Ico.mp hν
      have h1ν : (N : ℝ) - 1 ≤ ν := by
        have : N - 1 ≤ ν := hν'.1
        have : ((N - 1 : ℕ) : ℝ) ≤ ν := by exact_mod_cast this
        push_cast [Nat.cast_sub (show 1 ≤ N by omega)] at this; linarith
      exact norm_Fν_le_remR ht ha0 hc h2ab (by linarith) (by linarith)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [show N + 3 - (N - 1) = 4 by omega]; norm_num
  have h3 : ‖χ * (((N - 1 : ℕ) : ℂ) ^ (s - 1) + (N : ℂ) ^ (s - 1))‖ ≤ 2 / Real.sqrt ((N : ℝ) - 1) := by
    rw [norm_mul, hχ, hs, norm_zetaChi_criticalLine, one_mul]
    have hre : ((1 / 2 + (t : ℂ) * I) - 1).re = -(1 / 2) := by simp; norm_num
    have hpow : ∀ m : ℕ, 1 ≤ m → ‖(m : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)‖ = 1 / Real.sqrt m := by
      intro m hm
      rw [Complex.norm_natCast_cpow_of_pos (by omega), hre, Real.rpow_neg (Nat.cast_nonneg _),
        ← Real.sqrt_eq_rpow, one_div]
    refine (norm_add_le _ _).trans ?_
    rw [hpow _ (by omega), hpow _ (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
    have hs1 : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
    have : 1 / Real.sqrt (N : ℝ) ≤ 1 / Real.sqrt ((N : ℝ) - 1) :=
      one_div_le_one_div_of_le hs1 (Real.sqrt_le_sqrt (by linarith))
    have e : 2 / Real.sqrt ((N : ℝ) - 1) = 1 / Real.sqrt ((N : ℝ) - 1) + 1 / Real.sqrt ((N : ℝ) - 1) := by
      ring
    rw [e]; linarith
  have h4 := norm_sum_upper_le (A := N) (B := B) (n2 := N + 3) (c := c) (M + 1) ht hNB hc hb1 hbt
    (by push_cast; linarith)
  simp only [hF] at h2 ⊢
  rw [hbound]
  calc _ ≤ ‖∑ j ∈ range (N - 2), (Fν t ((N - 2 - j : ℕ) : ℝ) a b - χ * ((N - 2 - j : ℕ) : ℂ) ^ (s - 1))‖
        + ‖∑ ν ∈ Finset.Ico (N - 1) (N + 3), Fν t ν a b‖
        + ‖χ * (((N - 1 : ℕ) : ℂ) ^ (s - 1) + (N : ℂ) ^ (s - 1))‖
        + ‖∑ ν ∈ Finset.Ico (N + 3) (M + 1), Fν t ν a b‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by
        gcongr

/-! ## The numerical bookkeeping -/

theorem div_le_inv_sqrt {K D a : ℝ} (ha : 0 < a) (hD : 0 < D) (h : K * Real.sqrt a ≤ D) :
    K / D ≤ 1 / Real.sqrt a := by
  rw [div_le_div_iff₀ hD (Real.sqrt_pos.mpr ha)]; linarith

theorem sqrt_le_self' {a : ℝ} (ha : 1 ≤ a) : Real.sqrt a ≤ a := by
  have h0 : 0 ≤ a := by linarith
  rw [Real.sqrt_le_left h0]; nlinarith

theorem num_T1 {a b t : ℝ} (ha : 5 ≤ a) (ht : 4 * a ^ 2 ≤ t) (hsb : t ≤ Real.sqrt b) :
    11 * b ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by nlinarith
  have hb0 : 0 < Real.sqrt b := lt_of_lt_of_le ht0 hsb
  have hb : 0 < b := Real.sqrt_pos.mp hb0
  rw [Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  refine div_le_inv_sqrt ha0 hb0 ?_
  have := sqrt_le_self' (show 1 ≤ a by linarith)
  nlinarith

theorem num_T2 {a t : ℝ} (ha : 5 ≤ a) (ht : 4 * a ^ 2 ≤ t) : Real.sqrt a / t ≤ 1 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  refine div_le_inv_sqrt ha0 (by nlinarith) ?_
  rw [Real.mul_self_sqrt ha0.le]; nlinarith

theorem num_T4 {a c : ℝ} (ha : 5 ≤ a) (hc : c ≤ 2 * a) :
    2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a))) ≤ 1 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_gt_three
  have hs := Real.sqrt_pos.mpr ha0
  rw [← mul_div_assoc]
  refine div_le_inv_sqrt ha0 (by positivity) ?_
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have h0 : 36 * a ≤ 4 * Real.pi ^ 2 * a := by nlinarith
  have h1 : 2 * (2 * (1 / 2 + c)) ≤ 4 * Real.pi ^ 2 * a := by linarith
  calc 2 * (2 * (1 / 2 + c)) * Real.sqrt a ≤ 4 * Real.pi ^ 2 * a * Real.sqrt a := by gcongr
    _ = _ := by ring

theorem num_T5 {a b t : ℝ} {n : ℝ} (ha : 5 ≤ a) (ht : 4 * a ^ 2 ≤ t) (hsb : t ≤ Real.sqrt b)
    (hn : n ≤ a) : n * remK t a b ≤ 4 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by nlinarith
  have hsb0 : 0 < Real.sqrt b := lt_of_lt_of_le ht0 hsb
  have hb : 0 < b := Real.sqrt_pos.mp hsb0
  have hpi := Real.pi_gt_three
  have hy := sqrt_le_self' (show 1 ≤ a by linarith)
  have hy0 := Real.sqrt_pos.mpr ha0
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have hK0 : 0 ≤ remK t a b := by unfold remK; positivity
  refine (mul_le_mul_of_nonneg_right hn hK0).trans ?_
  unfold remK
  have hbsb : t ^ 3 ≤ b * Real.sqrt b := by
    have hb2 : t ^ 2 ≤ b := by
      have := mul_le_mul hsb hsb ht0.le hsb0.le
      rw [Real.mul_self_sqrt hb.le] at this; nlinarith
    have := mul_le_mul hb2 hsb ht0.le hb.le
    nlinarith
  have e1 : a * (12 / (4 * Real.pi ^ 2 * Real.sqrt b)) ≤ 1 / Real.sqrt a := by
    rw [← mul_div_assoc]; refine div_le_inv_sqrt ha0 (by positivity) ?_
    have h1 : a * 12 * Real.sqrt a ≤ 12 * a ^ 2 := by nlinarith
    have h2 : 12 * a ^ 2 ≤ 4 * t := by nlinarith
    have h3 : 4 * t ≤ 4 * Real.pi ^ 2 * Real.sqrt b := by
      have : 4 * Real.sqrt b ≤ 4 * Real.pi ^ 2 * Real.sqrt b := by nlinarith
      linarith
    linarith
  have hexp : Real.exp (-(Real.pi * t)) ≤ 1 / (Real.pi * t) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have := Real.add_one_le_exp (Real.pi * t); linarith
  have e2 : a * Real.exp (-(Real.pi * t)) ≤ 1 / Real.sqrt a := by
    refine (mul_le_mul_of_nonneg_left hexp ha0.le).trans ?_
    rw [← mul_div_assoc, mul_one]; refine div_le_inv_sqrt ha0 (by positivity) ?_
    have h1 : a * Real.sqrt a ≤ a ^ 2 := by nlinarith
    nlinarith
  have e3 : a * (2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a))) ≤ 1 / Real.sqrt a := by
    rw [← mul_div_assoc]; refine div_le_inv_sqrt ha0 (by positivity) ?_
    have : a * 2 * Real.sqrt a ≤ 4 * Real.pi ^ 2 * (a * Real.sqrt a) := by
      have hP : 0 < a * Real.sqrt a := by positivity
      have := mul_le_mul_of_nonneg_right hpi2 hP.le
      nlinarith
    linarith
  have e4 : a * (3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))) ≤ 1 / Real.sqrt a := by
    rw [← mul_div_assoc]; refine div_le_inv_sqrt ha0 (by positivity) ?_
    have h1 : a * (3 * t) * Real.sqrt a ≤ 3 * t * a ^ 2 := by
      have := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ 3 * t * a)
      nlinarith
    have h2 : 3 * t * a ^ 2 ≤ t * t := by nlinarith
    have h3 : t * t ≤ t ^ 3 := by
      have : 1 ≤ t := by nlinarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ t * t)
      nlinarith
    have h4 : t ^ 3 ≤ 4 * Real.pi ^ 2 * (b * Real.sqrt b) := by
      have hP : 0 < b * Real.sqrt b := by positivity
      have := mul_le_mul_of_nonneg_right hpi2 hP.le
      nlinarith
    linarith
  have : a * (12 / (4 * Real.pi ^ 2 * Real.sqrt b) + Real.exp (-(Real.pi * t))
      + 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) + 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)))
      = a * (12 / (4 * Real.pi ^ 2 * Real.sqrt b)) + a * Real.exp (-(Real.pi * t))
        + a * (2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)))
        + a * (3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b))) := by ring
  rw [this]
  have : 4 / Real.sqrt a = 1 / Real.sqrt a + 1 / Real.sqrt a + 1 / Real.sqrt a + 1 / Real.sqrt a := by
    ring
  rw [this]; linarith

theorem div_le_const_div_sqrt {K D a m : ℝ} (ha : 0 < a) (hD : 0 < D)
    (h : K * Real.sqrt a ≤ m * D) : K / D ≤ m / Real.sqrt a := by
  rw [div_le_div_iff₀ hD (Real.sqrt_pos.mpr ha)]; linarith

theorem num_T6 {a b t : ℝ} (ha : 5 ≤ a) (ht : 4 * a ^ 2 ≤ t) (hsb : t ≤ Real.sqrt b) :
    4 * remR t a b ≤ 64 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by nlinarith
  have hsb0 : 0 < Real.sqrt b := lt_of_lt_of_le ht0 hsb
  have hpi := Real.pi_gt_three
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have hy := sqrt_le_self' (show 1 ≤ a by linarith)
  have hy0 := Real.sqrt_pos.mpr ha0
  have hya := Real.mul_self_sqrt ha0.le
  unfold remR
  have hst : 2 * a ≤ Real.sqrt t := by
    have : Real.sqrt ((2 * a) ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  have e1 : 24 * Real.sqrt a / Real.sqrt t ≤ 12 / Real.sqrt a := by
    refine div_le_const_div_sqrt ha0 (by positivity) ?_
    rw [mul_assoc, hya]; nlinarith
  have e2 : 2 * (Real.sqrt (2 * a) / (2 * Real.pi * a)) ≤ 1 / Real.sqrt a := by
    rw [← mul_div_assoc]; refine div_le_inv_sqrt ha0 (by positivity) ?_
    rw [Real.sqrt_mul (by norm_num), mul_assoc, mul_assoc, hya]
    have hs2 : Real.sqrt 2 ≤ 1.5 := by
      rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have e3 : 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) ≤ 1 / Real.sqrt a := by
    refine div_le_inv_sqrt ha0 (by positivity) ?_
    have hP : 0 < a * Real.sqrt a := by positivity
    have := mul_le_mul_of_nonneg_right hpi2 hP.le
    nlinarith
  have e4 := num_T2 ha (by nlinarith : 4 * a ^ 2 ≤ t)
  have e5 : 1 / (2 * Real.pi * Real.sqrt b) ≤ 1 / Real.sqrt a := by
    apply one_div_le_one_div_of_le hy0
    nlinarith
  have : 64 / Real.sqrt a = 4 * (12 / Real.sqrt a + 1 / Real.sqrt a + 1 / Real.sqrt a
      + 1 / Real.sqrt a + 1 / Real.sqrt a) := by ring
  rw [this]
  gcongr

theorem num_T7 {N : ℕ} (hN : 5 ≤ N) :
    2 / Real.sqrt ((N : ℝ) - 1) ≤ 3 / Real.sqrt ((N : ℝ) + 1 / 2) := by
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.sqrt ((N : ℝ) + 1 / 2) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_div_iff₀ h1 h2]
  -- `4 (N + 1/2) ≤ 9 (N − 1)`
  have h3 : Real.sqrt (4 * ((N : ℝ) + 1 / 2)) ≤ Real.sqrt (9 * ((N : ℝ) - 1)) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
  linarith

theorem num_T8 {a b c t : ℝ} (ha : 5 ≤ a) (ht : 4 * a ^ 2 ≤ t) (hsb : t ≤ Real.sqrt b)
    (hc : c ≤ 2 * a) :
    1 / (2 * Real.pi * Real.sqrt a) + 2 * remQ t c a b ≤ 3 / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by nlinarith
  have hsb0 : 0 < Real.sqrt b := lt_of_lt_of_le ht0 hsb
  have hb : 0 < b := Real.sqrt_pos.mp hsb0
  have hpi := Real.pi_gt_three
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have hy := sqrt_le_self' (show 1 ≤ a by linarith)
  have hy0 := Real.sqrt_pos.mpr ha0
  unfold remQ
  have e0 : 1 / (2 * Real.pi * Real.sqrt a) ≤ 1 / Real.sqrt a :=
    one_div_le_one_div_of_le hy0 (by nlinarith)
  have hP : 0 < a * Real.sqrt a := by positivity
  have hPpi := mul_le_mul_of_nonneg_right hpi2 hP.le
  have e1 : 2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) ≤ (1 / 4) / Real.sqrt a := by
    refine div_le_const_div_sqrt ha0 (by positivity) ?_
    have : 0 ≤ Real.sqrt a := hy0.le
    nlinarith
  have e2 : 12 / (4 * Real.pi ^ 2 * Real.sqrt b) ≤ (1 / 4) / Real.sqrt a := by
    refine div_le_const_div_sqrt ha0 (by positivity) ?_
    have := mul_le_mul_of_nonneg_right hpi2 hsb0.le
    nlinarith
  have e3 : 2 / (4 * Real.pi ^ 2 * (a * Real.sqrt a)) ≤ (1 / 4) / Real.sqrt a := by
    refine div_le_const_div_sqrt ha0 (by positivity) ?_
    nlinarith
  have hbsb : t ^ 3 ≤ b * Real.sqrt b := by
    have hb2 : t ^ 2 ≤ b := by
      have := mul_le_mul hsb hsb ht0.le hsb0.le
      rw [Real.mul_self_sqrt hb.le] at this; nlinarith
    have := mul_le_mul hb2 hsb ht0.le hb.le
    nlinarith
  have e4 : 3 * t / (4 * Real.pi ^ 2 * (b * Real.sqrt b)) ≤ (1 / 4) / Real.sqrt a := by
    refine div_le_const_div_sqrt ha0 (by positivity) ?_
    have hQ : 0 < b * Real.sqrt b := by positivity
    have := mul_le_mul_of_nonneg_right hpi2 hQ.le
    have h1 : 3 * t * Real.sqrt a ≤ 3 * t * a := by gcongr
    have h2a : 3 * a ≤ t * t := by
      have h1t : 1 ≤ t := by nlinarith
      have h3a : 3 * a ≤ t := by nlinarith
      have := mul_le_mul_of_nonneg_left h1t ht0.le
      linarith
    have h2 : 3 * t * a ≤ t ^ 3 := by
      have := mul_le_mul_of_nonneg_left h2a ht0.le
      nlinarith
    nlinarith
  have : 3 / Real.sqrt a = 1 / Real.sqrt a + 2 * ((1 / 4) / Real.sqrt a + (1 / 4) / Real.sqrt a
      + (1 / 4) / Real.sqrt a + (1 / 4) / Real.sqrt a) := by ring
  rw [this]
  gcongr

theorem afe_bound_numeric {t a b c : ℝ} {N : ℕ} (hN : 5 ≤ N) (ha : a = N + 1 / 2)
    (ht : 4 * a ^ 2 ≤ t) (hc2 : c ≤ 2 * a) (hsb : t ≤ Real.sqrt b) :
    11 * b ^ (-(1 / 2 : ℝ)) + Real.sqrt a / t
      + ((1 / (Real.pi * Real.sqrt a) + 2 * (2 * (1 / 2 + c) / (4 * Real.pi ^ 2 * (a * Real.sqrt a)))
          + ((N - 2 : ℕ) : ℝ) * remK t a b) + 4 * remR t a b + 2 / Real.sqrt ((N : ℝ) - 1)
        + (1 / (2 * Real.pi * Real.sqrt a) + 2 * remQ t c a b))
      ≤ 80 / Real.sqrt a := by
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have ha5 : 5 ≤ a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  have hy0 := Real.sqrt_pos.mpr ha0
  have hpi := Real.pi_gt_three
  have T1 := num_T1 ha5 ht hsb
  have T2 := num_T2 ha5 ht
  have T3 : 1 / (Real.pi * Real.sqrt a) ≤ 1 / Real.sqrt a :=
    one_div_le_one_div_of_le hy0 (by nlinarith)
  have T4 := num_T4 ha5 hc2
  have hN2 : ((N - 2 : ℕ) : ℝ) ≤ a := by
    push_cast [Nat.cast_sub (show 2 ≤ N by omega)]; rw [ha]; linarith
  have T5 := num_T5 ha5 ht hsb hN2
  have T6 := num_T6 ha5 ht hsb
  have T7 := num_T7 hN
  rw [← ha] at T7
  have T8 := num_T8 ha5 ht hsb hc2
  have : 80 / Real.sqrt a = 1 / Real.sqrt a + 1 / Real.sqrt a + ((1 / Real.sqrt a + 1 / Real.sqrt a
      + 4 / Real.sqrt a) + 64 / Real.sqrt a + 3 / Real.sqrt a + 3 / Real.sqrt a) + 2 / Real.sqrt a := by
    ring
  rw [this]
  have : 0 ≤ 2 / Real.sqrt a := by positivity
  linarith

end AFEProof

end RiemannHypothesis
