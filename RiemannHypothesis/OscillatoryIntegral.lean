/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.VanDerCorput

/-!
# Oscillatory integrals: integration by parts to first and second order

For a real phase `Φ` and a real amplitude `g`, write `g = h Φ'`.  Then
`(h e^{iΦ})' = h' e^{iΦ} + i g e^{iΦ}`, so

  `∫_p^q g e^{iΦ} = -i [h e^{iΦ}]_p^q + i ∫_p^q h' e^{iΦ}`        (`integral_eq_first_order`),

and, writing in turn `h' = k Φ'`,

  `∫_p^q g e^{iΦ} = -i [h e^{iΦ}]_p^q + [k e^{iΦ}]_p^q - ∫_p^q k' e^{iΦ}`
                                                                  (`integral_eq_second_order`).

These exact identities give the *first-derivative test with a monotone ratio*
(`norm_integral_le_of_monotone_ratio`: if `h = g/Φ'` is monotone, then
`‖∫ g e^{iΦ}‖ ≤ |h(p)| + |h(q)| + |h(q) − h(p)|`) and its second-order refinement
(`norm_integral_add_boundary_le_of_monotone`: if `k = h'/Φ'` is monotone, the first-order
boundary term `-i [h e^{iΦ}]` approximates the integral to within `2 (|k(p)| + |k(q)|)`).

These are the integration-by-parts estimates used by the B process
(`RiemannHypothesis.ZetaMellinPhase`, `RiemannHypothesis.ZetaStationaryPhase`,
`RiemannHypothesis.AFEProof`).  Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set intervalIntegral

namespace RiemannHypothesis

namespace Oscillatory

open VanDerCorput

/-- The first-order identity `∫ g e^{iΦ} = -i [h e^{iΦ}] + i ∫ h' e^{iΦ}` for `g = h Φ'`. -/
theorem integral_eq_first_order {p q : ℝ} (hpq : p ≤ q) {g h h' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hh'c : ContinuousOn h' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x) :
    ∫ x in p..q, (g x : ℂ) * expI Φ x
      = -I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)
        + I * ∫ x in p..q, (h' x : ℂ) * expI Φ x := by
  have huIcc : uIcc p q = Icc p q := uIcc_of_le hpq
  have hEc : ContinuousOn (expI Φ) (Icc p q) := continuous_expI_of hΦ
  have hderiv : ∀ x ∈ uIcc p q, HasDerivAt (fun y => (h y : ℂ) * expI Φ y)
      ((h' x : ℂ) * expI Φ x + I * ((g x : ℂ) * expI Φ x)) x := by
    intro x hx
    rw [huIcc] at hx
    have h1 := (hh x hx).ofReal_comp
    have h2 := hasDerivAt_expI (hΦ x hx)
    refine (h1.mul h2).congr_deriv ?_
    rw [hg x hx]
    push_cast
    ring
  have hint1 : IntervalIntegrable (fun x => (h' x : ℂ) * expI Φ x) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (continuous_ofReal.comp_continuousOn hh'c).mul hEc
  have hgc : ContinuousOn g (Icc p q) := by
    have : ContinuousOn (fun x => h x * Φ' x) (Icc p q) :=
      (HasDerivAt.continuousOn (fun x hx => hh x hx) |>.mono le_rfl).mul hΦ'c
    exact this.congr hg
  have hint2 : IntervalIntegrable (fun x => (g x : ℂ) * expI Φ x) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (continuous_ofReal.comp_continuousOn hgc).mul hEc
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv (hint1.add (hint2.const_mul I))
  rw [intervalIntegral.integral_add hint1 (hint2.const_mul I),
    intervalIntegral.integral_const_mul] at hFTC
  linear_combination (-I) * hFTC + (∫ x in p..q, (g x : ℂ) * expI Φ x) * I_sq

/-- `‖∫_p^q F e^{iΦ}‖ ≤ ∫_p^q |F|` for real `F`. -/
theorem norm_integral_mul_expI_le {p q : ℝ} (hpq : p ≤ q) (F Φ : ℝ → ℝ) :
    ‖∫ x in p..q, (F x : ℂ) * expI Φ x‖ ≤ ∫ x in p..q, |F x| := by
  refine (intervalIntegral.norm_integral_le_integral_norm hpq).trans (le_of_eq ?_)
  refine integral_congr fun x _ => ?_
  simp only [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- For a function with derivative of constant sign, `∫_p^q |k'| = |k q − k p|`. -/
theorem integral_abs_deriv_eq_of_sign {p q : ℝ} (hpq : p ≤ q) {k k' : ℝ → ℝ}
    (hk : ∀ x ∈ Icc p q, HasDerivAt k (k' x) x) (hk'c : ContinuousOn k' (Icc p q))
    (hsign : (∀ x ∈ Icc p q, 0 ≤ k' x) ∨ (∀ x ∈ Icc p q, k' x ≤ 0)) :
    ∫ x in p..q, |k' x| = |k q - k p| := by
  have huIcc : uIcc p q = Icc p q := uIcc_of_le hpq
  have hint : IntervalIntegrable k' volume p q := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hk'c
  have hFTC : ∫ x in p..q, k' x = k q - k p :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hk x (huIcc ▸ hx)) hint
  rcases hsign with h | h
  · have : ∫ x in p..q, |k' x| = ∫ x in p..q, k' x :=
      integral_congr fun x hx => abs_of_nonneg (h x (huIcc ▸ hx))
    have hnn : 0 ≤ ∫ x in p..q, k' x := intervalIntegral.integral_nonneg hpq fun x hx => h x hx
    rw [this, hFTC]
    rw [hFTC] at hnn
    rw [abs_of_nonneg hnn]
  · have : ∫ x in p..q, |k' x| = ∫ x in p..q, -k' x :=
      integral_congr fun x hx => abs_of_nonpos (h x (huIcc ▸ hx))
    have hnn : 0 ≤ ∫ x in p..q, -k' x :=
      intervalIntegral.integral_nonneg hpq fun x hx => by linarith [h x hx]
    rw [this]
    rw [intervalIntegral.integral_neg, hFTC] at hnn ⊢
    rw [abs_of_nonpos (by linarith)]

/-- The general first-order bound: `‖∫ g e^{iΦ}‖ ≤ |h p| + |h q| + ∫ |h'|`. -/
theorem norm_integral_le_first_order {p q : ℝ} (hpq : p ≤ q) {g h h' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hh'c : ContinuousOn h' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x) :
    ‖∫ x in p..q, (g x : ℂ) * expI Φ x‖ ≤ |h p| + |h q| + ∫ x in p..q, |h' x| := by
  rw [integral_eq_first_order hpq hΦ hh hΦ'c hh'c hg]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖-I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)‖ ≤ |h p| + |h q| := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    ring
  have h2 : ‖I * ∫ x in p..q, (h' x : ℂ) * expI Φ x‖ ≤ ∫ x in p..q, |h' x| := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact norm_integral_mul_expI_le hpq h' Φ
  linarith

/-- **First-derivative test with a monotone ratio.**  If `g = h Φ'` with `h' ` of constant sign
(i.e. `h = g/Φ'` monotone), then `‖∫_p^q g e^{iΦ}‖ ≤ |h p| + |h q| + |h q − h p|`. -/
theorem norm_integral_le_of_monotone_ratio {p q : ℝ} (hpq : p ≤ q) {g h h' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hh'c : ContinuousOn h' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x)
    (hsign : (∀ x ∈ Icc p q, 0 ≤ h' x) ∨ (∀ x ∈ Icc p q, h' x ≤ 0)) :
    ‖∫ x in p..q, (g x : ℂ) * expI Φ x‖ ≤ |h p| + |h q| + |h q - h p| := by
  have := norm_integral_le_first_order hpq hΦ hh hΦ'c hh'c hg
  rwa [integral_abs_deriv_eq_of_sign hpq hh hh'c hsign] at this

/-- The second-order identity: with `g = h Φ'` and `h' = k Φ'`,
`∫ g e^{iΦ} = -i [h e^{iΦ}] + [k e^{iΦ}] − ∫ k' e^{iΦ}`. -/
theorem integral_eq_second_order {p q : ℝ} (hpq : p ≤ q) {g h h' k k' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hk : ∀ x ∈ Icc p q, HasDerivAt k (k' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hk'c : ContinuousOn k' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x) (hh' : ∀ x ∈ Icc p q, h' x = k x * Φ' x) :
    ∫ x in p..q, (g x : ℂ) * expI Φ x
      = -I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)
        + ((k q : ℂ) * expI Φ q - (k p : ℂ) * expI Φ p)
        - ∫ x in p..q, (k' x : ℂ) * expI Φ x := by
  have hkc : ContinuousOn k (Icc p q) := HasDerivAt.continuousOn fun x hx => hk x hx
  have hh'c : ContinuousOn h' (Icc p q) := (hkc.mul hΦ'c).congr hh'
  rw [integral_eq_first_order hpq hΦ hh hΦ'c hh'c hg,
    integral_eq_first_order hpq hΦ hk hΦ'c hk'c hh']
  ring_nf
  simp only [I_sq]
  ring

/-- **Second-order bound.**  With `g = h Φ'`, `h' = k Φ'`:
`‖∫ g e^{iΦ} + i [h e^{iΦ}]‖ ≤ |k p| + |k q| + ∫ |k'|`. -/
theorem norm_integral_add_boundary_le {p q : ℝ} (hpq : p ≤ q) {g h h' k k' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hk : ∀ x ∈ Icc p q, HasDerivAt k (k' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hk'c : ContinuousOn k' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x) (hh' : ∀ x ∈ Icc p q, h' x = k x * Φ' x) :
    ‖(∫ x in p..q, (g x : ℂ) * expI Φ x)
        + I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)‖
      ≤ |k p| + |k q| + ∫ x in p..q, |k' x| := by
  rw [integral_eq_second_order hpq hΦ hh hk hΦ'c hk'c hg hh']
  have e : -I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)
        + ((k q : ℂ) * expI Φ q - (k p : ℂ) * expI Φ p)
        - (∫ x in p..q, (k' x : ℂ) * expI Φ x)
        + I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)
      = ((k q : ℂ) * expI Φ q - (k p : ℂ) * expI Φ p)
        - ∫ x in p..q, (k' x : ℂ) * expI Φ x := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(k q : ℂ) * expI Φ q - (k p : ℂ) * expI Φ p‖ ≤ |k p| + |k q| := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    ring
  have h2 := norm_integral_mul_expI_le hpq k' Φ
  linarith

/-- **Second-order bound, monotone case**: if moreover `k'` has constant sign, then
`‖∫ g e^{iΦ} + i [h e^{iΦ}]‖ ≤ |k p| + |k q| + |k q − k p| ≤ 2 (|k p| + |k q|)`. -/
theorem norm_integral_add_boundary_le_of_monotone {p q : ℝ} (hpq : p ≤ q)
    {g h h' k k' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hk : ∀ x ∈ Icc p q, HasDerivAt k (k' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hk'c : ContinuousOn k' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x) (hh' : ∀ x ∈ Icc p q, h' x = k x * Φ' x)
    (hsign : (∀ x ∈ Icc p q, 0 ≤ k' x) ∨ (∀ x ∈ Icc p q, k' x ≤ 0)) :
    ‖(∫ x in p..q, (g x : ℂ) * expI Φ x)
        + I * ((h q : ℂ) * expI Φ q - (h p : ℂ) * expI Φ p)‖
      ≤ 2 * (|k p| + |k q|) := by
  have := norm_integral_add_boundary_le hpq hΦ hh hk hΦ'c hk'c hg hh'
  rw [integral_abs_deriv_eq_of_sign hpq hk hk'c hsign] at this
  have : |k q - k p| ≤ |k p| + |k q| := by
    have := abs_sub (k q) (k p); linarith
  linarith

/-- Second mean value form of the weighted integral: if `g ≥ 0` is decreasing with derivative
`g'`, and every partial integral `∫_p^y e^{iΦ}` is at most `M` in norm, then
`‖∫_p^q g e^{iΦ}‖ ≤ g(p) M`. -/
theorem norm_integral_weight_le {p q M : ℝ} (hpq : p ≤ q) {g g' Φ : ℝ → ℝ}
    (hg : ∀ x ∈ Icc p q, HasDerivAt g (g' x) x) (hg'c : ContinuousOn g' (Icc p q))
    (hg'neg : ∀ x ∈ Icc p q, g' x ≤ 0) (hgq : 0 ≤ g q) (hΦc : Continuous Φ)
    (hM : ∀ y ∈ Icc p q, ‖∫ x in p..y, expI Φ x‖ ≤ M) :
    ‖∫ x in p..q, (g x : ℂ) * expI Φ x‖ ≤ g p * M := by
  have huIcc : uIcc p q = Icc p q := uIcc_of_le hpq
  have hEc : Continuous (expI Φ) := by
    unfold expI; fun_prop
  set E : ℝ → ℂ := fun y => ∫ x in p..y, expI Φ x with hE
  have hEd : ∀ x, HasDerivAt E (expI Φ x) x := fun x =>
    integral_hasDerivAt_right (hEc.intervalIntegrable _ _) hEc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hEc.continuousAt
  have hparts := integral_mul_deriv_eq_deriv_mul (a := p) (b := q)
    (u := fun x => (g x : ℂ)) (v := E) (u' := fun x => (g' x : ℂ)) (v' := expI Φ)
    (fun x hx => (hg x (huIcc ▸ hx)).ofReal_comp) (fun x _ => hEd x)
    (by apply ContinuousOn.intervalIntegrable; rw [huIcc];
        exact continuous_ofReal.comp_continuousOn hg'c)
    (hEc.intervalIntegrable _ _)
  rw [hparts]
  have hEp : E p = 0 := by simp [hE]
  rw [hEp, mul_zero, sub_zero]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p ⟨le_rfl, hpq⟩)
  have h1 : ‖(g q : ℂ) * E q‖ ≤ g q * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgq]
    exact mul_le_mul_of_nonneg_left (hM q ⟨hpq, le_rfl⟩) hgq
  have hgc : ContinuousOn g (Icc p q) := HasDerivAt.continuousOn fun x hx => hg x hx
  have h2 : ‖∫ x in p..q, (g' x : ℂ) * E x‖ ≤ ∫ x in p..q, -g' x * M := by
    refine norm_integral_le_of_norm_le hpq ?_ ?_
    · filter_upwards with x hx
      have hx' : x ∈ Icc p q := ⟨hx.1.le, hx.2⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hg'neg x hx')]
      exact mul_le_mul_of_nonneg_left (hM x hx') (by linarith [hg'neg x hx'])
    · apply ContinuousOn.intervalIntegrable; rw [huIcc]
      exact (hg'c.neg).mul continuousOn_const
  have h3 : ∫ x in p..q, -g' x * M = (g p - g q) * M := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
      integral_eq_sub_of_hasDerivAt (fun x hx => hg x (huIcc ▸ hx))
        (by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'c)]
    ring
  calc ‖(g q : ℂ) * E q - ∫ x in p..q, (g' x : ℂ) * E x‖
      ≤ ‖(g q : ℂ) * E q‖ + ‖∫ x in p..q, (g' x : ℂ) * E x‖ := norm_sub_le _ _
    _ ≤ g q * M + (g p - g q) * M := by rw [← h3]; linarith
    _ = g p * M := by ring

/-- First-derivative test, packaged: if `h = g/Φ'` is monotone and `h(p)`, `h(q)` have the same
sign and are both at most `M` in absolute value, then `‖∫_p^q g e^{iΦ}‖ ≤ 2M`. -/
theorem norm_integral_le_two_mul_of_monotone_ratio {p q M : ℝ} (hpq : p ≤ q)
    {g h h' Φ Φ' : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc p q, HasDerivAt Φ (Φ' x) x)
    (hh : ∀ x ∈ Icc p q, HasDerivAt h (h' x) x)
    (hΦ'c : ContinuousOn Φ' (Icc p q)) (hh'c : ContinuousOn h' (Icc p q))
    (hg : ∀ x ∈ Icc p q, g x = h x * Φ' x)
    (hsign : (∀ x ∈ Icc p q, 0 ≤ h' x) ∨ (∀ x ∈ Icc p q, h' x ≤ 0))
    (hsame : 0 ≤ h p * h q) (hp : |h p| ≤ M) (hq : |h q| ≤ M) :
    ‖∫ x in p..q, (g x : ℂ) * expI Φ x‖ ≤ 2 * M := by
  refine (norm_integral_le_of_monotone_ratio hpq hΦ hh hΦ'c hh'c hg hsign).trans ?_
  rcases le_total 0 (h p) with h0 | h0
  · rcases le_total 0 (h q) with h1 | h1
    · rw [abs_of_nonneg h0, abs_of_nonneg h1] at *
      rcases le_total (h p) (h q) with h2 | h2
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    · have : h p * h q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 h1
      have hz : h p * h q = 0 := le_antisymm this hsame
      rcases mul_eq_zero.mp hz with hz | hz
      · rw [hz] at hp ⊢; simp only [abs_zero, zero_add, sub_zero]; linarith [abs_nonneg (h q)]
      · rw [hz] at hq ⊢; simp only [abs_zero, add_zero, zero_sub, abs_neg]; linarith
  · rcases le_total 0 (h q) with h1 | h1
    · have : h p * h q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 h1
      have hz : h p * h q = 0 := le_antisymm this hsame
      rcases mul_eq_zero.mp hz with hz | hz
      · rw [hz] at hp ⊢; simp only [abs_zero, zero_add, sub_zero]; linarith [abs_nonneg (h q)]
      · rw [hz] at hq ⊢; simp only [abs_zero, add_zero, zero_sub, abs_neg]; linarith
    · rw [abs_of_nonpos h0, abs_of_nonpos h1] at *
      rcases le_total (h p) (h q) with h2 | h2
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith

end Oscillatory

end RiemannHypothesis
