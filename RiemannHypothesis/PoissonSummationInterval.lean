/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.OscillatoryIntegral

/-!
# Poisson summation on an interval (the exact form behind Titchmarsh, Lemma 4.10)

For `0 ≤ a ≤ b` and a twice continuously differentiable `G : ℝ → ℂ` on `[a, b]`,

  `∑_{a < n ≤ b} G(n) = ∫_a^b G + ψ(a) G(a) − ψ(b) G(b) + ∑_{n ≥ 1} S_n`,
  `S_n = −(1/(π n)) ∫_a^b sin(2π n x) G'(x) dx`,

where `ψ(x) = {x} − 1/2` is the sawtooth (`sawtooth`) and the series **converges**
(`hasSum_sum_Ioc_sub_integral`).  This is the Euler–Maclaurin formula of first order with the
Fourier series `ψ(x) = −∑ sin(2πnx)/(πn)` inserted, the conditionally convergent sawtooth series
being handled through the absolutely convergent series of the periodic Bernoulli function
`P₂(x) = B₂({x})/2 = ∑_{n ≥ 1} cos(2πnx)/(2π²n²)` (`hasSum_bernP2`, from Mathlib's Fourier series
of the Bernoulli polynomials) and one integration by parts (`P₂' = ψ`).

At **half-integer endpoints** `a = A + 1/2`, `b = B + 1/2` the boundary terms vanish and one
gets the Poisson summation formula on an interval
(`hasSum_sum_Ioc_halfInt`):

  `∑_{A < n ≤ B} G(n) = ∫_a^b G + ∑_{ν ≥ 1} ∫_a^b G(x) (e(νx) + e(−νx)) dx`,

a convergent series of Fourier integrals.  This is the identity from which the approximate
functional equation (`RiemannHypothesis.AFEProof`) is derived.  The truncated Poisson formula
(Titchmarsh, Lemma 4.10) for arbitrary real endpoints, and its weighted forms, are not derived
here (task-board row `M1-VDC-B-PROCESS`).  Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RiemannHypothesis

namespace PoissonInterval

/-- The sawtooth `ψ(x) = {x} − 1/2`. -/
def sawtooth (x : ℝ) : ℝ := Int.fract x - 1 / 2

/-- The periodic Bernoulli function `P₂(x) = B₂({x})/2 = ({x}² − {x} + 1/6)/2`. -/
def bernP2 (x : ℝ) : ℝ := (Int.fract x ^ 2 - Int.fract x + 1 / 6) / 2

theorem continuous_bernP2 : Continuous bernP2 := by
  have h := ContinuousOn.comp_fract (s := fun x : ℝ => x)
    (f := fun (_ : ℝ) (y : ℝ) => (y ^ 2 - y + 1 / 6) / 2)
    ((by fun_prop : Continuous (fun p : ℝ × ℝ => (p.2 ^ 2 - p.2 + 1 / 6) / 2)).continuousOn)
    continuous_id (fun _ => by norm_num)
  exact h

theorem abs_sawtooth_le (x : ℝ) : |sawtooth x| ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [sawtooth, abs_le]
  constructor <;> linarith

theorem abs_bernP2_le (x : ℝ) : |bernP2 x| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [bernP2, abs_le]
  constructor <;> nlinarith

theorem measurable_sawtooth : Measurable sawtooth :=
  (measurable_fract).sub measurable_const

/-- The right derivative of `P₂` is the sawtooth, everywhere. -/
theorem hasDerivWithinAt_bernP2 (x : ℝ) : HasDerivWithinAt bernP2 (sawtooth x) (Ioi x) x := by
  set m : ℝ := (⌊x⌋ : ℝ) with hm
  set q : ℝ → ℝ := fun y => ((y - m) ^ 2 - (y - m) + 1 / 6) / 2 with hq
  have hqd : HasDerivAt q (sawtooth x) x := by
    have h := ((((hasDerivAt_id x).sub_const m).pow 2).sub ((hasDerivAt_id x).sub_const m)).add_const
      (1 / 6 : ℝ) |>.div_const 2
    refine h.congr_deriv ?_
    simp only [id, sawtooth, Int.fract, hm]
    push_cast
    ring
  have hfr : ∀ y ∈ Icc x (m + 1), y < m + 1 → Int.fract y = y - m := by
    intro y hy hy1
    have hfl : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      exact ⟨le_trans (Int.floor_le x) hy.1, by rw [← hm]; exact hy1⟩
    rw [Int.fract, hfl]
  have hx1 : x < m + 1 := Int.lt_floor_add_one x
  have hev : bernP2 =ᶠ[𝓝[>] x] q := by
    filter_upwards [Ioo_mem_nhdsGT hx1] with y hy
    rw [bernP2, hfr y ⟨hy.1.le, hy.2.le⟩ hy.2]
  have hxe : bernP2 x = q x := by
    rw [bernP2, hfr x ⟨le_rfl, hx1.le⟩ hx1]
  exact hqd.hasDerivWithinAt.congr_of_eventuallyEq hev hxe

/-- The Fourier series of `P₂`: `P₂(x) = ∑_{n} cos(2πnx)/(2π²n²)` (the `n = 0` term is `0`). -/
theorem hasSum_bernP2 (x : ℝ) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x) / (2 * Real.pi ^ 2))
      (bernP2 x) := by
  have hfx : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hfx
  have hB : Polynomial.eval (Int.fract x)
      (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1)))
      = Int.fract x ^ 2 - Int.fract x + 1 / 6 := by
    simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_two]
    ring
  rw [hB] at h
  have hcos : ∀ n : ℕ, Real.cos (2 * Real.pi * n * Int.fract x) = Real.cos (2 * Real.pi * n * x) := by
    intro n
    have : 2 * Real.pi * n * x = 2 * Real.pi * n * Int.fract x + ((n * ⌊x⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  simp_rw [hcos] at h
  have hpi : (2 * Real.pi ^ 2) ≠ 0 := by positivity
  have h2 := h.div_const (2 * Real.pi ^ 2)
  have hval : bernP2 x = (-1) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)
      * (Int.fract x ^ 2 - Int.fract x + 1 / 6) / (2 * Real.pi ^ 2) := by
    unfold bernP2
    field_simp
    norm_num [Nat.factorial]
    ring
  rw [hval]
  exact h2

/-- The sawtooth is interval integrable (as a complex function). -/
theorem intervalIntegrable_sawtooth (a b : ℝ) :
    IntervalIntegrable (fun x => (sawtooth x : ℂ)) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℂ))).mono_fun ?_ ?_
  · exact (continuous_ofReal.measurable.comp measurable_sawtooth).aestronglyMeasurable
  · filter_upwards with x
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_one]
    linarith [abs_sawtooth_le x]

/-- **Euler–Maclaurin of first order**: `∑_{a<n≤b} G(n) = ∫_a^b G + ψ(a)G(a) − ψ(b)G(b) +
∫_a^b ψ G'`. -/
theorem sum_Ioc_eq_integral_add_sawtooth {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {G G' : ℝ → ℂ}
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (G' x) x) (hG'c : ContinuousOn G' (Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, G k
      = (∫ x in a..b, G x) + (sawtooth a : ℂ) * G a - (sawtooth b : ℂ) * G b
        + ∫ x in a..b, (sawtooth x : ℂ) * G' x := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hderiv : ∀ t ∈ Icc a b, deriv G t = G' t := fun t ht => (hG t ht).deriv
  have hint : IntegrableOn (deriv G) (Icc a b) :=
    (hG'c.integrableOn_Icc).congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (fun _ => (1 : ℂ)) ha hab
    (fun t ht => (hG t ht).differentiableAt) hint
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul] at h
  rw [h, ← intervalIntegral.integral_of_le hab]
  have hGc : ContinuousOn G (Icc a b) := HasDerivAt.continuousOn fun x hx => hG x hx
  -- rewrite the integrand
  have hcongr : ∫ t in a..b, deriv G t * ((⌊t⌋₊ + 1 : ℕ) : ℂ)
      = ∫ t in a..b, (G' t * ((t : ℂ) + 1 / 2) - (sawtooth t : ℂ) * G' t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [huIcc] at ht
    have ht0 : 0 ≤ t := le_trans ha ht.1
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor ht0]; push_cast; ring
    rw [hderiv t ht, sawtooth]
    push_cast
    rw [show ((⌊t⌋₊ : ℕ) : ℂ) = ((t - Int.fract t : ℝ) : ℂ) by rw [← hfl, Complex.ofReal_natCast]]
    push_cast
    ring
  rw [hcongr]
  have hint1 : IntervalIntegrable (fun t => G' t * ((t : ℂ) + 1 / 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]
    exact hG'c.mul (by fun_prop)
  have hint2 : IntervalIntegrable (fun t => (sawtooth t : ℂ) * G' t) volume a b := by
    refine (intervalIntegrable_sawtooth a b).mul_continuousOn ?_
    rw [huIcc]; exact hG'c
  rw [intervalIntegral.integral_sub hint1 hint2]
  -- integrate `G' (t + 1/2)` by parts
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := G) (v := fun t : ℝ => (t : ℂ) + 1 / 2) (u' := G') (v' := fun _ => (1 : ℂ))
    (fun x hx => hG x (huIcc ▸ hx))
    (fun x _ => ((hasDerivAt_id x).ofReal_comp).add_const (1 / 2 : ℂ) |>.congr_deriv (by simp))
    (by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hG'c)
    intervalIntegrable_const
  simp only [mul_one] at hparts
  rw [hparts]
  have hfa : (⌊a⌋₊ : ℝ) = a - Int.fract a := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor ha]; push_cast; ring
  have hfb : (⌊b⌋₊ : ℝ) = b - Int.fract b := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (le_trans ha hab)]; push_cast; ring
  simp only [sawtooth]
  push_cast
  rw [show ((⌊a⌋₊ : ℕ) : ℂ) = ((a - Int.fract a : ℝ) : ℂ) by rw [← hfa, Complex.ofReal_natCast],
    show ((⌊b⌋₊ : ℕ) : ℂ) = ((b - Int.fract b : ℝ) : ℂ) by rw [← hfb, Complex.ofReal_natCast]]
  push_cast
  ring

/-- The Fourier coefficient `c_n = 1/(2π²n²)` of `P₂` (`c_0 = 0`). -/
def p2Coeff (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2 / (2 * Real.pi ^ 2)

theorem p2Coeff_nonneg (n : ℕ) : 0 ≤ p2Coeff n := by
  unfold p2Coeff; positivity

theorem summable_p2Coeff : Summable p2Coeff := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr one_lt_two
  exact h.div_const _

theorem hasSum_bernP2' (x : ℝ) :
    HasSum (fun n : ℕ => p2Coeff n * Real.cos (2 * Real.pi * n * x)) (bernP2 x) := by
  refine (hasSum_bernP2 x).congr_fun ?_
  intro n
  unfold p2Coeff
  ring

/-- **The sawtooth integral as a convergent Fourier series**:
`∫_a^b ψ G' = ∑_{n} −(1/(πn)) ∫_a^b sin(2πnx) G'(x) dx` (the `n = 0` term is `0`). -/
theorem hasSum_integral_sawtooth {a b : ℝ} (hab : a ≤ b) {G' G'' : ℝ → ℂ}
    (hG' : ∀ x ∈ Icc a b, HasDerivAt G' (G'' x) x) (hG''c : ContinuousOn G'' (Icc a b)) :
    HasSum (fun n : ℕ => ((-(1 / (Real.pi * n)) : ℝ) : ℂ)
        * ∫ x in a..b, (Real.sin (2 * Real.pi * n * x) : ℂ) * G' x)
      (∫ x in a..b, (sawtooth x : ℂ) * G' x) := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hG'c : ContinuousOn G' (Icc a b) := HasDerivAt.continuousOn fun x hx => hG' x hx
  have hmin : Ioo (min a b) (max a b) = Ioo a b := by rw [min_eq_left hab, max_eq_right hab]
  -- step 1: integrate by parts against `P₂`
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right (a := a) (b := b)
    (u := fun x => (bernP2 x : ℂ)) (v := G') (u' := fun x => (sawtooth x : ℂ)) (v' := G'')
    ((continuous_ofReal.comp continuous_bernP2).continuousOn) (by rw [huIcc]; exact hG'c)
    (fun x _ => (hasDerivWithinAt_bernP2 x).ofReal_comp)
    (fun x hx => by
      rw [hmin] at hx
      exact (hG' x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    (intervalIntegrable_sawtooth a b)
    (by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hG''c)
  have hsaw : ∫ x in a..b, (sawtooth x : ℂ) * G' x
      = (bernP2 b : ℂ) * G' b - (bernP2 a : ℂ) * G' a - ∫ x in a..b, (bernP2 x : ℂ) * G'' x := by
    rw [hparts]; ring
  -- step 2: expand `P₂` in its Fourier series at the endpoints and under the integral
  have hb := (Complex.hasSum_ofReal.mpr (hasSum_bernP2' b)).mul_right (G' b)
  have ha := (Complex.hasSum_ofReal.mpr (hasSum_bernP2' a)).mul_right (G' a)
  set M : ℝ → ℝ := fun x => ‖G'' x‖ with hM
  have hint : HasSum (fun n : ℕ => ∫ x in a..b,
        ((p2Coeff n * Real.cos (2 * Real.pi * n * x) : ℝ) : ℂ) * G'' x)
      (∫ x in a..b, (bernP2 x : ℂ) * G'' x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n x => p2Coeff n * M x) ?_ ?_ ?_ ?_ ?_
    · intro n
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      refine ContinuousOn.mono ?_ uIoc_subset_uIcc
      rw [huIcc]
      exact (continuous_ofReal.comp (by fun_prop)).continuousOn.mul hG''c
    · intro n
      filter_upwards with x _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (p2Coeff_nonneg n)]
      have := Real.abs_cos_le_one (2 * Real.pi * n * x)
      have h0 := p2Coeff_nonneg n
      calc p2Coeff n * |Real.cos (2 * Real.pi * n * x)| * ‖G'' x‖ ≤ p2Coeff n * 1 * ‖G'' x‖ := by
            gcongr
        _ = p2Coeff n * M x := by rw [mul_one]
    · filter_upwards with x _
      exact summable_p2Coeff.mul_right _
    · have : (fun x => ∑' n, p2Coeff n * M x) = fun x => (∑' n, p2Coeff n) * M x := by
        funext x; exact tsum_mul_right
      rw [this]
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact continuousOn_const.mul (continuous_norm.comp_continuousOn hG''c)
    · filter_upwards with x _
      have := (Complex.hasSum_ofReal.mpr (hasSum_bernP2' x)).mul_right (G'' x)
      exact this
  have htot := (hb.sub ha).sub hint
  rw [← hsaw] at htot
  refine htot.congr_fun ?_
  intro n
  -- step 3: integrate `cos · G''` back by parts
  have hcos : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (Real.cos (2 * Real.pi * n * y) : ℂ))
      ((-(2 * Real.pi * n) * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ) x := by
    intro x
    have h := ((hasDerivAt_id x).const_mul (2 * Real.pi * n)).cos
    refine (h.ofReal_comp).congr_deriv ?_
    simp only [id, mul_one]
    push_cast
    ring
  have hparts2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun y : ℝ => (Real.cos (2 * Real.pi * n * y) : ℂ)) (v := G')
    (u' := fun x => ((-(2 * Real.pi * n) * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ)) (v' := G'')
    (fun x _ => hcos x) (fun x hx => hG' x (huIcc ▸ hx))
    ((by fun_prop : Continuous fun x : ℝ =>
      ((-(2 * Real.pi * n) * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ)).intervalIntegrable _ _)
    (by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hG''c)
  have hpull : ∫ x in a..b, ((p2Coeff n * Real.cos (2 * Real.pi * n * x) : ℝ) : ℂ) * G'' x
      = (p2Coeff n : ℂ) * ∫ x in a..b, (Real.cos (2 * Real.pi * n * x) : ℂ) * G'' x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast; ring
  have hpull2 : ∫ x in a..b, ((-(2 * Real.pi * n) * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ) * G' x
      = ((-(2 * Real.pi * n)) : ℂ) * ∫ x in a..b, (Real.sin (2 * Real.pi * n * x) : ℂ) * G' x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast; ring
  rw [hpull, hparts2, hpull2]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [p2Coeff]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    unfold p2Coeff
    push_cast
    field_simp
    ring

/-- **Poisson summation on an interval** (exact, with a convergent series): for `0 ≤ a ≤ b` and
`G` twice continuously differentiable on `[a, b]`,
`∑_{a<n≤b} G(n) − ∫_a^b G − ψ(a)G(a) + ψ(b)G(b) = ∑_{n} −(1/(πn)) ∫_a^b sin(2πnx) G'(x) dx`. -/
theorem hasSum_sum_Ioc_sub_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {G G' G'' : ℝ → ℂ}
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (G' x) x) (hG' : ∀ x ∈ Icc a b, HasDerivAt G' (G'' x) x)
    (hG''c : ContinuousOn G'' (Icc a b)) :
    HasSum (fun n : ℕ => ((-(1 / (Real.pi * n)) : ℝ) : ℂ)
        * ∫ x in a..b, (Real.sin (2 * Real.pi * n * x) : ℂ) * G' x)
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, G k - (∫ x in a..b, G x)
        - (sawtooth a : ℂ) * G a + (sawtooth b : ℂ) * G b) := by
  have hG'c : ContinuousOn G' (Icc a b) := HasDerivAt.continuousOn fun x hx => hG' x hx
  rw [sum_Ioc_eq_integral_add_sawtooth ha hab hG hG'c]
  convert hasSum_integral_sawtooth hab hG' hG''c using 1
  ring

theorem sawtooth_halfInt (A : ℕ) : sawtooth ((A : ℝ) + 1 / 2) = 0 := by
  have : Int.fract ((A : ℝ) + 1 / 2) = 1 / 2 := by
    rw [Int.fract_eq_iff]
    refine ⟨by norm_num, by norm_num, A, by push_cast; ring⟩
  rw [sawtooth, this]; ring

theorem floor_halfInt (A : ℕ) : ⌊(A : ℝ) + 1 / 2⌋₊ = A := by
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> linarith

theorem sin_halfInt (n A : ℕ) : Real.sin (2 * Real.pi * n * ((A : ℝ) + 1 / 2)) = 0 := by
  have : 2 * Real.pi * n * ((A : ℝ) + 1 / 2) = ((n * (2 * A + 1) : ℕ) : ℝ) * Real.pi := by
    push_cast; ring
  rw [this, Real.sin_nat_mul_pi]

/-- Integration by parts at half-integer endpoints: for `m ≥ 1`,
`2 ∫_{A+1/2}^{B+1/2} G(x) cos(2πmx) dx = −(1/(πm)) ∫_{A+1/2}^{B+1/2} sin(2πmx) G'(x) dx`
(the boundary terms vanish because `sin(2πm(A + 1/2)) = 0`). -/
theorem two_integral_mul_cos_halfInt {A B : ℕ} (hAB : A ≤ B) {G G' : ℝ → ℂ}
    (hG : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt G (G' x) x)
    (hG'c : ContinuousOn G' (Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))) {m : ℕ} (hm : 0 < m) :
    2 * ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2), G x * (Real.cos (2 * Real.pi * m * x) : ℂ)
      = ((-(1 / (Real.pi * m)) : ℝ) : ℂ)
        * ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2), (Real.sin (2 * Real.pi * m * x) : ℂ) * G' x := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hsin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (Real.sin (2 * Real.pi * m * y) : ℂ))
      (((2 * Real.pi * m) * Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ) x := by
    intro x
    have h := ((hasDerivAt_id x).const_mul (2 * Real.pi * m)).sin
    refine (h.ofReal_comp).congr_deriv ?_
    simp only [id, mul_one]
    push_cast
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun y : ℝ => (Real.sin (2 * Real.pi * m * y) : ℂ)) (v := G)
    (u' := fun x => (((2 * Real.pi * m) * Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ)) (v' := G')
    (fun x _ => hsin x) (fun x hx => hG x (huIcc ▸ hx))
    ((by fun_prop : Continuous fun x : ℝ =>
      (((2 * Real.pi * m) * Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ)).intervalIntegrable _ _)
    (by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hG'c)
  have hsa : Real.sin (2 * Real.pi * m * a) = 0 := by rw [ha]; exact sin_halfInt _ _
  have hsb : Real.sin (2 * Real.pi * m * b) = 0 := by rw [hb]; exact sin_halfInt _ _
  have hpull : ∫ x in a..b, (((2 * Real.pi * m) * Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ) * G x
      = ((2 * Real.pi * m : ℝ) : ℂ) * ∫ x in a..b, G x * (Real.cos (2 * Real.pi * m * x) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast; ring
  rw [hparts, hsa, hsb, hpull]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **Poisson summation at half-integer endpoints**: for naturals `A ≤ B` and `G` twice
continuously differentiable on `[A + 1/2, B + 1/2]`,
`∑_{A<n≤B} G(n) = ∫_{A+1/2}^{B+1/2} G + ∑_{ν ≥ 1} 2 ∫_{A+1/2}^{B+1/2} G(x) cos(2πνx) dx`,
the series being convergent. -/
theorem hasSum_sum_Ioc_halfInt {A B : ℕ} (hAB : A ≤ B) {G G' G'' : ℝ → ℂ}
    (hG : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt G' (G'' x) x)
    (hG''c : ContinuousOn G'' (Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))) :
    HasSum (fun n : ℕ => 2 * ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2),
        G x * (Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) : ℂ))
      (∑ k ∈ Finset.Ioc A B, G k - ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2), G x) := by
  set a : ℝ := (A : ℝ) + 1 / 2 with ha
  set b : ℝ := (B : ℝ) + 1 / 2 with hb
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hG'c : ContinuousOn G' (Icc a b) := HasDerivAt.continuousOn fun x hx => hG' x hx
  have h := hasSum_sum_Ioc_sub_integral (by positivity) hab hG hG' hG''c
  rw [ha, hb, floor_halfInt, floor_halfInt, sawtooth_halfInt, sawtooth_halfInt] at h
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at h
  rw [← ha, ← hb] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, div_zero,
    neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at h1
  refine h1.congr_fun ?_
  intro n
  exact two_integral_mul_cos_halfInt (m := n + 1) hAB hG hG'c (Nat.succ_pos n)

end PoissonInterval

end RiemannHypothesis
