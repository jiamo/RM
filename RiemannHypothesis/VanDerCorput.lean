/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib

/-!
# van der Corput's derivative tests for exponential integrals

An *exponential integral* is `∫_a^b e^{i F(x)} dx` with `F` real.  The trivial bound is `b − a`;
the whole point of van der Corput's method is that when the phase `F` moves fast enough the
oscillation cancels and the integral is bounded **independently of the length of the range**.

This file proves the two basic tests.

* `norm_integral_expI_le_of_abs_deriv_ge` — the **first-derivative test**: if `F'` is monotone
  (equivalently, `F''` has a constant sign) and `|F'| ≥ m > 0` throughout, then
  `‖∫_a^b e^{iF}‖ ≤ 4/m`.
* `norm_integral_expI_le_of_deriv_two_ge` — the **second-derivative test**: if `F'' ≥ r > 0`
  throughout, then `‖∫_a^b e^{iF}‖ ≤ 12/√r`, again with no dependence on `b − a`.

Both are the standard statements; the constants `4` and `12` are the ones this proof gives,
and no attempt is made to optimize them (the classical write-ups have `4` and `8`).

## Why these are here

They are the analytic engine shared by the two routes that the repository is missing:

* the **approximate functional equation** for `ζ` on the critical line is obtained by evaluating
  exponential integrals `∫ x^{-s} e(±x u) dx` by stationary phase, and the error terms in that
  evaluation are exactly first- and second-derivative-test bounds; and
* the **Weyl bound** `ζ(1/2+it) ≪ t^{1/6+ε}` is the second-derivative test for *sums*, whose
  proof (Poisson summation, then van der Corput's lemma) converts sums into precisely the
  integrals bounded here.

Neither test is in Mathlib.

## Implementation

The first-derivative test is integration by parts against `1/F'`:
`e^{iF} = (1/(iF')) · (e^{iF})'`, so

`i ∫_a^b e^{iF} = [e^{iF}/F']_a^b − ∫_a^b (1/F')' e^{iF}`,

and the two boundary terms contribute `≤ 1/m` each while, `1/F'` being monotone, the last
integral is at most the total variation `|1/F'(b) − 1/F'(a)| ≤ 2/m`.  The hypotheses are stated
with an explicit second derivative `F''` rather than with `MonotoneOn F'`, because that is the
form in which the applications arrive (`F(x) = −t log x` has `F''(x) = t/x² > 0`), and because
the constant sign of `F''` is what the argument uses.

The second-derivative test splits the range at the (unique, if any) zero of `F'`: outside a
window of length `2/√r` around it one has `|F'| ≥ √r`, so the first-derivative test applies,
and the window is estimated trivially.
-/

noncomputable section

open Complex MeasureTheory Set intervalIntegral

namespace RiemannHypothesis

namespace VanDerCorput

/-- The oscillating integrand `x ↦ e^{i F(x)}` of an exponential integral. -/
def expI (F : ℝ → ℝ) (x : ℝ) : ℂ := Complex.exp (Complex.I * (F x : ℂ))

@[simp] theorem norm_expI (F : ℝ → ℝ) (x : ℝ) : ‖expI F x‖ = 1 := by
  simp [expI, Complex.norm_exp]

theorem hasDerivAt_expI {F F' : ℝ → ℝ} {x : ℝ} (h : HasDerivAt F (F' x) x) :
    HasDerivAt (expI F) (expI F x * (Complex.I * (F' x : ℂ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * ((F y : ℝ) : ℂ))
      (Complex.I * (F' x : ℂ)) x := by
    simpa using (h.ofReal_comp.const_mul Complex.I)
  exact h1.cexp

theorem continuous_expI_of {F F' : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ x ∈ s, HasDerivAt F (F' x) x) : ContinuousOn (expI F) s := fun x hx =>
  (((hasDerivAt_expI (F' := F') (h x hx)).continuousAt).continuousWithinAt)

/-! ## The first-derivative test -/

/-- **van der Corput's first-derivative test for integrals.**  If on `[a,b]` the phase `F` is
twice differentiable with a second derivative of constant sign (so that `F'` is monotone) and
`|F'| ≥ m > 0`, then

`‖∫_a^b e^{i F(x)} dx‖ ≤ 4/m`,

a bound with no dependence whatsoever on the length `b − a` of the range. -/
theorem norm_integral_expI_le_of_abs_deriv_ge {a b m : ℝ} {F F' F'' : ℝ → ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc a b, HasDerivAt F' (F'' x) x)
    (hF''c : ContinuousOn F'' (Icc a b))
    (hsign : (∀ x ∈ Icc a b, 0 ≤ F'' x) ∨ (∀ x ∈ Icc a b, F'' x ≤ 0))
    (hlb : ∀ x ∈ Icc a b, m ≤ |F' x|) :
    ‖∫ x in a..b, expI F x‖ ≤ 4 / m := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hFne : ∀ x ∈ Icc a b, F' x ≠ 0 := by
    intro x hx h0
    have := hlb x hx
    rw [h0] at this
    simp at this
    linarith
  -- the amplitude `G = 1/F'`
  set G : ℝ → ℝ := fun x => (F' x)⁻¹ with hG
  set G' : ℝ → ℝ := fun x => -F'' x / (F' x) ^ 2 with hG'
  have hGderiv : ∀ x ∈ Icc a b, HasDerivAt G (G' x) x := by
    intro x hx
    exact (hF' x hx).inv (hFne x hx)
  have hGbd : ∀ x ∈ Icc a b, |G x| ≤ 1 / m := by
    intro x hx
    have h1 : m ≤ |F' x| := hlb x hx
    have hpos : 0 < |F' x| := lt_of_lt_of_le hm h1
    rw [hG]
    simp only [abs_inv, one_div]
    exact inv_anti₀ hm h1
  have hF'c : ContinuousOn F' (Icc a b) := fun x hx =>
    ((hF' x hx).continuousAt).continuousWithinAt
  have hG'c : ContinuousOn G' (Icc a b) := by
    apply ContinuousOn.div (hF''c.neg) (hF'c.pow 2)
    intro x hx
    exact pow_ne_zero 2 (hFne x hx)
  have hG'int : IntervalIntegrable G' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [huIcc]
  -- integration by parts
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun y : ℝ => ((G y : ℝ) : ℂ)) ((G' x : ℝ) : ℂ) x := by
    intro x hx
    rw [huIcc] at hx
    exact (hGderiv x hx).ofReal_comp
  have hv : ∀ x ∈ uIcc a b,
      HasDerivAt (expI F) (expI F x * (Complex.I * (F' x : ℂ))) x := by
    intro x hx
    rw [huIcc] at hx
    exact hasDerivAt_expI (F' := F') (hF x hx)
  have hu'int : IntervalIntegrable (fun x : ℝ => ((G' x : ℝ) : ℂ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact Complex.continuous_ofReal.comp_continuousOn hG'c
  have hv'int : IntervalIntegrable
      (fun x : ℝ => expI F x * (Complex.I * (F' x : ℂ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (continuous_expI_of (F' := F') hF).mul
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF'c))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  -- the left-hand side is `I` times the integral we are bounding
  have hlhs : (∫ x in a..b, ((G x : ℝ) : ℂ) * (expI F x * (Complex.I * (F' x : ℂ))))
      = Complex.I * ∫ x in a..b, expI F x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [huIcc] at hx
    have : ((G x : ℝ) : ℂ) * ((F' x : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      rw [hG]
      simp [inv_mul_cancel₀ (hFne x hx)]
    calc ((G x : ℝ) : ℂ) * (expI F x * (Complex.I * (F' x : ℂ)))
        = (((G x : ℝ) : ℂ) * ((F' x : ℝ) : ℂ)) * (Complex.I * expI F x) := by ring
      _ = Complex.I * expI F x := by rw [this]; ring
  rw [hlhs] at hparts
  -- bound the three terms on the right
  have hnormI : ‖Complex.I * ∫ x in a..b, expI F x‖ = ‖∫ x in a..b, expI F x‖ := by
    simp
  have hbd1 : ‖((G b : ℝ) : ℂ) * expI F b‖ ≤ 1 / m := by
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hGbd b ⟨hab, le_rfl⟩
  have hbd2 : ‖((G a : ℝ) : ℂ) * expI F a‖ ≤ 1 / m := by
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hGbd a ⟨le_rfl, hab⟩
  -- the variation term
  have hvar : (∫ x in a..b, |G' x|) ≤ 2 / m := by
    have hGa := hGbd a ⟨le_rfl, hab⟩
    have hGb := hGbd b ⟨hab, le_rfl⟩
    have habsG : |G a| ≤ 1 / m := hGa
    have habsG' : |G b| ≤ 1 / m := hGb
    rcases hsign with hpos | hneg
    · -- `G' ≤ 0`, so `∫ |G'| = G a − G b`
      have hle : ∀ x ∈ uIcc a b, G' x ≤ 0 := by
        intro x hx
        rw [huIcc] at hx
        have h1 : 0 ≤ F'' x := hpos x hx
        have h2 : 0 < (F' x) ^ 2 := by
          have := hFne x hx
          positivity
        rw [hG']
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h2)
      have hcongr : (∫ x in a..b, |G' x|) = ∫ x in a..b, -G' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact abs_of_nonpos (hle x hx)
      have hsub : (∫ x in a..b, -G' x) = -G b - -G a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x hx
          rw [huIcc] at hx
          exact (hGderiv x hx).neg
        · exact hG'int.neg
      rw [hcongr, hsub]
      have : G a - G b ≤ 1 / m + 1 / m := by
        have h1 : G a ≤ 1 / m := le_trans (le_abs_self _) habsG
        have h2 : -(1 / m) ≤ G b := neg_le_of_neg_le (le_trans (neg_le_abs _) habsG')
        linarith
      have h2m : (2 : ℝ) / m = 1 / m + 1 / m := by ring
      rw [h2m]
      linarith
    · -- `G' ≥ 0`, so `∫ |G'| = G b − G a`
      have hle : ∀ x ∈ uIcc a b, 0 ≤ G' x := by
        intro x hx
        rw [huIcc] at hx
        have h1 : F'' x ≤ 0 := hneg x hx
        have h2 : 0 < (F' x) ^ 2 := by
          have := hFne x hx
          positivity
        rw [hG']
        exact div_nonneg (by linarith) (le_of_lt h2)
      have hcongr : (∫ x in a..b, |G' x|) = ∫ x in a..b, G' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact abs_of_nonneg (hle x hx)
      have hsub : (∫ x in a..b, G' x) = G b - G a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x hx
          rw [huIcc] at hx
          exact hGderiv x hx
        · exact hG'int
      rw [hcongr, hsub]
      have h1 : G b ≤ 1 / m := le_trans (le_abs_self _) habsG'
      have h2 : -(1 / m) ≤ G a := neg_le_of_neg_le (le_trans (neg_le_abs _) habsG)
      have h2m : (2 : ℝ) / m = 1 / m + 1 / m := by ring
      rw [h2m]
      linarith
  have hbd3 : ‖∫ x in a..b, ((G' x : ℝ) : ℂ) * expI F x‖ ≤ 2 / m := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    have : (∫ x in a..b, ‖((G' x : ℝ) : ℂ) * expI F x‖) = ∫ x in a..b, |G' x| := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [this]
    exact hvar
  -- combine
  have : ‖∫ x in a..b, expI F x‖ ≤ 1 / m + 1 / m + 2 / m := by
    rw [← hnormI, hparts]
    calc ‖((G b : ℝ) : ℂ) * expI F b - ((G a : ℝ) : ℂ) * expI F a
            - ∫ x in a..b, ((G' x : ℝ) : ℂ) * expI F x‖
        ≤ ‖((G b : ℝ) : ℂ) * expI F b - ((G a : ℝ) : ℂ) * expI F a‖
            + ‖∫ x in a..b, ((G' x : ℝ) : ℂ) * expI F x‖ := norm_sub_le _ _
      _ ≤ (‖((G b : ℝ) : ℂ) * expI F b‖ + ‖((G a : ℝ) : ℂ) * expI F a‖)
            + ‖∫ x in a..b, ((G' x : ℝ) : ℂ) * expI F x‖ := by
            gcongr; exact norm_sub_le _ _
      _ ≤ (1 / m + 1 / m) + 2 / m := by gcongr
      _ = 1 / m + 1 / m + 2 / m := by ring
  have h4 : (1 : ℝ) / m + 1 / m + 2 / m = 4 / m := by ring
  linarith [this, h4.ge, h4.le]

/-! ## The second-derivative test -/

/-- The trivial bound for an exponential integral: the modulus of the integrand is `1`. -/
theorem norm_integral_expI_le_length {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ) :
    ‖∫ x in a..b, expI F x‖ ≤ b - a := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := expI F) (fun x _ => le_of_eq (norm_expI F x))
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using this

/-- **van der Corput's second-derivative test for integrals.**  If the phase has
`F'' ≥ r > 0` throughout `[a,b]` then

`‖∫_a^b e^{i F(x)} dx‖ ≤ 12/√r`,

again independently of the length of the range.  The point is that no lower bound on `|F'|` is
assumed: `F'` may vanish, and the estimate survives because it can vanish only once. -/
theorem norm_integral_expI_le_of_deriv_two_ge {a b r : ℝ} {F F' F'' : ℝ → ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc a b, HasDerivAt F' (F'' x) x)
    (hF''c : ContinuousOn F'' (Icc a b))
    (hlb : ∀ x ∈ Icc a b, r ≤ F'' x) :
    ‖∫ x in a..b, expI F x‖ ≤ 12 / Real.sqrt r := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  set d : ℝ := 1 / Real.sqrt r with hd
  have hdpos : 0 < d := by positivity
  have hrd : r * d = Real.sqrt r := by
    rw [hd, mul_one_div, div_eq_iff (ne_of_gt hsr)]
    exact (Real.mul_self_sqrt hr.le).symm
  -- `F'` grows at rate at least `r`
  have hgrow : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → r * (y - x) ≤ F' y - F' x := by
    have hH : MonotoneOn (fun x => F' x - r * x) (Icc a b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := fun x => F'' x - r)
      · intro x hx
        have h1 : HasDerivAt (fun y : ℝ => F' y - r * y) (F'' x - r) x := by
          have h2 : HasDerivAt (fun y : ℝ => r * y) r x := by
            simpa using (hasDerivAt_id x).const_mul r
          exact (hF' x hx).sub h2
        exact h1.continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
        have h2 : HasDerivAt (fun y : ℝ => r * y) r x := by
          simpa using (hasDerivAt_id x).const_mul r
        exact (((hF' x hx').sub h2)).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have := hlb x (Ioo_subset_Icc_self hx)
        linarith
    intro x hx y hy hxy
    have := hH hx hy hxy
    simp only at this
    linarith
  have hmono : MonotoneOn F' (Icc a b) := by
    intro x hx y hy hxy
    have := hgrow x hx y hy hxy
    nlinarith [hr.le, sub_nonneg.mpr hxy]
  -- the last point at which `F'` is still nonpositive
  set S : Set ℝ := insert a {x | x ∈ Icc a b ∧ F' x ≤ 0} with hS
  have hSsub : S ⊆ Icc a b := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨le_rfl, hab⟩
    · exact hx.1
  have hSne : S.Nonempty := ⟨a, Set.mem_insert _ _⟩
  have hSbdd : BddAbove S := ⟨b, fun x hx => (hSsub hx).2⟩
  set u : ℝ := sSup S with hu
  have hua : a ≤ u := le_csSup hSbdd (Set.mem_insert _ _)
  have hub : u ≤ b := csSup_le hSne fun x hx => (hSsub hx).2
  have hleft : ∀ z : ℝ, a ≤ z → z < u → F' z ≤ 0 := by
    intro z haz hzu
    obtain ⟨s, hs, hzs⟩ := exists_lt_of_lt_csSup hSne hzu
    have hzb : z ≤ b := le_trans hzu.le hub
    rcases hs with rfl | hs
    · exact absurd haz (not_le.mpr hzs)
    · exact le_trans (hmono ⟨haz, hzb⟩ hs.1 hzs.le) hs.2
  have hright : ∀ y ∈ Icc a b, u < y → 0 < F' y := by
    intro y hy huy
    rcases lt_or_ge 0 (F' y) with h | h
    · exact h
    · exact absurd (le_csSup hSbdd (Set.mem_insert_of_mem _ ⟨hy, h⟩)) (not_le.mpr huy)
  -- the three-piece split
  set m₁ : ℝ := max a (min b (u - 2 * d)) with hm₁
  set m₂ : ℝ := max m₁ (min b (u + 2 * d)) with hm₂
  have ham₁ : a ≤ m₁ := le_max_left _ _
  have hm₁b : m₁ ≤ b := max_le hab (min_le_left _ _)
  have hm₁m₂ : m₁ ≤ m₂ := le_max_left _ _
  have hm₂b : m₂ ≤ b := max_le hm₁b (min_le_left _ _)
  have hmiddle : m₂ - m₁ ≤ 4 * d := by
    simp only [hm₂, hm₁, max_def, min_def]
    split_ifs <;> linarith
  -- integrability
  have hcont : ContinuousOn (expI F) (Icc a b) := continuous_expI_of (F' := F') hF
  have hint : ∀ p q : ℝ, a ≤ p → p ≤ q → q ≤ b →
      IntervalIntegrable (expI F) volume p q := by
    intro p q hap hpq hqb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    exact hcont.mono (Icc_subset_Icc hap hqb)
  -- left piece
  have hleftbd : ‖∫ x in a..m₁, expI F x‖ ≤ 4 / Real.sqrt r := by
    rcases eq_or_lt_of_le ham₁ with heq | hlt
    · rw [← heq]
      simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · have hm₁le : m₁ ≤ u - 2 * d := by
        rcases max_cases a (min b (u - 2 * d)) with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 (by rw [← hm₁]; exact ne_of_gt hlt)
        · rw [hm₁, h1]; exact min_le_right _ _
      have hsub : Icc a m₁ ⊆ Icc a b := Icc_subset_Icc le_rfl hm₁b
      apply norm_integral_expI_le_of_abs_deriv_ge (m := Real.sqrt r) hlt.le hsr
        (fun x hx => hF x (hsub hx)) (fun x hx => hF' x (hsub hx))
        (hF''c.mono hsub) (Or.inl fun x hx => le_trans hr.le (hlb x (hsub hx)))
      intro x hx
      have hxIcc : x ∈ Icc a b := hsub hx
      have hxle : x ≤ u - 2 * d := le_trans hx.2 hm₁le
      have hzIcc : x + d ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hub]⟩
      have hzu : x + d < u := by linarith
      have hFz : F' (x + d) ≤ 0 := hleft _ (by linarith [hx.1]) hzu
      have hg := hgrow x hxIcc (x + d) hzIcc (by linarith)
      have : F' x ≤ -Real.sqrt r := by
        have : r * d ≤ F' (x + d) - F' x := by simpa using hg
        rw [hrd] at this
        linarith
      rw [abs_of_nonpos (by linarith [hsr])]
      linarith
  -- right piece
  have hrightbd : ‖∫ x in m₂..b, expI F x‖ ≤ 4 / Real.sqrt r := by
    rcases eq_or_lt_of_le hm₂b with heq | hlt
    · rw [heq]
      simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · have hm₂ge : u + 2 * d ≤ m₂ := by
        have h1 : min b (u + 2 * d) ≤ m₂ := le_max_right _ _
        rcases min_cases b (u + 2 * d) with ⟨h2, _⟩ | ⟨h2, _⟩
        · rw [h2] at h1; linarith
        · rw [h2] at h1; exact h1
      have hsub : Icc m₂ b ⊆ Icc a b := Icc_subset_Icc (le_trans ham₁ hm₁m₂) le_rfl
      apply norm_integral_expI_le_of_abs_deriv_ge (m := Real.sqrt r) hlt.le hsr
        (fun x hx => hF x (hsub hx)) (fun x hx => hF' x (hsub hx))
        (hF''c.mono hsub) (Or.inl fun x hx => le_trans hr.le (hlb x (hsub hx)))
      intro y hy
      have hyIcc : y ∈ Icc a b := hsub hy
      have hyge : u + 2 * d ≤ y := le_trans hm₂ge hy.1
      have hzIcc : y - d ∈ Icc a b := ⟨by linarith [hua], by linarith [hy.2]⟩
      have hzu : u < y - d := by linarith
      have hFz : 0 < F' (y - d) := hright _ hzIcc hzu
      have hg := hgrow (y - d) hzIcc y hyIcc (by linarith)
      have hfin : Real.sqrt r ≤ F' y := by
        have : r * d ≤ F' y - F' (y - d) := by
          have := hg
          have hsimp : y - (y - d) = d := by ring
          rw [hsimp] at this
          exact this
        rw [hrd] at this
        linarith
      rw [abs_of_nonneg (by linarith [hsr])]
      exact hfin
  -- middle piece
  have hmidbd : ‖∫ x in m₁..m₂, expI F x‖ ≤ 4 / Real.sqrt r := by
    refine le_trans (norm_integral_expI_le_length hm₁m₂ F) ?_
    have : (4 : ℝ) * d = 4 / Real.sqrt r := by rw [hd]; ring
    linarith [hmiddle, this.ge, this.le]
  -- glue
  have hsplit1 : (∫ x in a..m₁, expI F x) + (∫ x in m₁..m₂, expI F x)
      = ∫ x in a..m₂, expI F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint a m₁ le_rfl ham₁ hm₁b) (hint m₁ m₂ ham₁ hm₁m₂ hm₂b)
  have hsplit2 : (∫ x in a..m₂, expI F x) + (∫ x in m₂..b, expI F x)
      = ∫ x in a..b, expI F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint a m₂ le_rfl (le_trans ham₁ hm₁m₂) hm₂b)
      (hint m₂ b (le_trans ham₁ hm₁m₂) hm₂b le_rfl)
  have hfinal : (∫ x in a..b, expI F x)
      = ((∫ x in a..m₁, expI F x) + (∫ x in m₁..m₂, expI F x)) + ∫ x in m₂..b, expI F x := by
    rw [hsplit1, hsplit2]
  rw [hfinal]
  calc ‖((∫ x in a..m₁, expI F x) + (∫ x in m₁..m₂, expI F x)) + ∫ x in m₂..b, expI F x‖
      ≤ ‖(∫ x in a..m₁, expI F x) + (∫ x in m₁..m₂, expI F x)‖
        + ‖∫ x in m₂..b, expI F x‖ := norm_add_le _ _
    _ ≤ (‖∫ x in a..m₁, expI F x‖ + ‖∫ x in m₁..m₂, expI F x‖)
        + ‖∫ x in m₂..b, expI F x‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (4 / Real.sqrt r + 4 / Real.sqrt r) + 4 / Real.sqrt r := by gcongr
    _ = 12 / Real.sqrt r := by ring

/-! ## A worked instance

The exponential integrals of `ζ`-theory have the phase `F(x) = −t log x`, coming from
`x^{-it} = e^{-i t log x}`.  Then `F'(x) = −t/x` and `F''(x) = t/x² > 0`, so both tests apply,
and both beat the trivial bound `B − A` once `t` is large. -/

theorem hasDerivAt_negMulLog {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(t * Real.log y)) (-(t / x)) x := by
  have h0 := (Real.hasDerivAt_log (ne_of_gt hx)).const_mul t
  rw [show t * x⁻¹ = t / x from (div_eq_mul_inv t x).symm] at h0
  exact h0.neg

theorem hasDerivAt_negDiv {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(t / y)) (t / x ^ 2) x := by
  have h0 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv (ne_of_gt hx)
  have h2 := (h0.const_mul t).neg
  have h3 : -(t * -(x ^ 2)⁻¹) = t / x ^ 2 := by field_simp
  rw [h3] at h2
  have h4 : (-fun y : ℝ => t * y⁻¹) = fun y : ℝ => -(t / y) := by
    funext y
    simp [div_eq_mul_inv]
  rwa [h4] at h2

/-- **The first-derivative test for `∫_A^B x^{-it} dx`.**  The bound `4B/t` is independent of
the length of the range, and beats the trivial bound as soon as `t` exceeds `4B/(B−A)`. -/
theorem norm_integral_expI_logPhase_le {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B) (ht : 0 < t) :
    ‖∫ x in A..B, expI (fun y => -(t * Real.log y)) x‖ ≤ 4 * B / t := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hpos : ∀ x ∈ Icc A B, 0 < x := fun x hx => lt_of_lt_of_le hA hx.1
  have hm : 0 < t / B := by positivity
  have key := norm_integral_expI_le_of_abs_deriv_ge (a := A) (b := B) (m := t / B)
    (F := fun y => -(t * Real.log y)) (F' := fun y => -(t / y)) (F'' := fun y => t / y ^ 2)
    hAB hm
    (fun x hx => hasDerivAt_negMulLog (hpos x hx))
    (fun x hx => hasDerivAt_negDiv (hpos x hx))
    (by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hpos x hx)))
    (Or.inl fun x hx => by positivity)
    (fun x hx => by
      have hx0 : 0 < x := hpos x hx
      have : t / B ≤ t / x := by
        apply div_le_div_of_nonneg_left ht.le hx0 hx.2
      rw [abs_neg, abs_of_nonneg (by positivity)]
      exact this)
  have hrw : 4 / (t / B) = 4 * B / t := by field_simp
  rwa [hrw] at key

/-- **The second-derivative test for `∫_A^B x^{-it} dx`**: the bound is `12B/√t`, again
independent of the length of the range, and the better of the two once `t ≥ 9`. -/
theorem norm_integral_expI_logPhase_le_sqrt {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B) (ht : 0 < t) :
    ‖∫ x in A..B, expI (fun y => -(t * Real.log y)) x‖ ≤ 12 * B / Real.sqrt t := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hpos : ∀ x ∈ Icc A B, 0 < x := fun x hx => lt_of_lt_of_le hA hx.1
  have hr : 0 < t / B ^ 2 := by positivity
  have key := norm_integral_expI_le_of_deriv_two_ge (a := A) (b := B) (r := t / B ^ 2)
    (F := fun y => -(t * Real.log y)) (F' := fun y => -(t / y)) (F'' := fun y => t / y ^ 2)
    hAB hr
    (fun x hx => hasDerivAt_negMulLog (hpos x hx))
    (fun x hx => hasDerivAt_negDiv (hpos x hx))
    (by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hpos x hx)))
    (fun x hx => by
      have hx0 : 0 < x := hpos x hx
      apply div_le_div_of_nonneg_left ht.le (by positivity)
      exact pow_le_pow_left₀ hx0.le hx.2 2)
  have hsqrt : Real.sqrt (t / B ^ 2) = Real.sqrt t / B := by
    rw [Real.sqrt_div ht.le, Real.sqrt_sq hB.le]
  rw [hsqrt] at key
  have hrw : 12 / (Real.sqrt t / B) = 12 * B / Real.sqrt t := div_div_eq_mul_div _ _ _
  rwa [hrw] at key

end VanDerCorput

end RiemannHypothesis
