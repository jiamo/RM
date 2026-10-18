/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.KusminLandau

/-!
# van der Corput's sum-versus-integral lemma

For real `f` on `[a, a + N]` whose derivative is monotone with `|f'| ≤ θ < 1`, an exponential
sum is its integral up to a bounded error (Titchmarsh, *The Theory of the Riemann
Zeta-Function*, Lemma 4.8):

  `‖∑_{n < N} e(f(a+n)) − ∫_a^{a+N} e(f(u)) du‖ ≤ 5/2 + 4πθ + 5κ(θ)/2`
  (`norm_sum_e2pi_sub_integral_le`, `f'` increasing or decreasing),

where `e(x) = exp(2πix)` (`KusminLandau.e2pi`) and `κ(θ) = 1/(πθ) − cot(πθ)` (`vdcKappa`;
`κ(0) = 0`).  With a nonnegative decreasing continuous weight `g` (Titchmarsh, Lemma 4.10, the
form needed for `ζ`), the error is `(5/2 + 4πθ + 5κ(θ)/2) g(a)`
(`norm_sum_mul_e2pi_sub_integral_le`, `norm_sum_mul_e2pi_sub_integral_le_of_antitone`).

## The argument

This is not Titchmarsh's proof (Euler–Maclaurin, the Fourier series of the sawtooth and the
first-derivative test for each frequency); it is a direct discrete argument in the style of
Kusmin–Landau.  On each unit interval `[p, p + 1]`, with increment `Δ = f(p+1) − f(p)`:

* replacing `f` by its linear interpolant costs at most `2π (f'(p+1) − f'(p))`
  (`norm_unit_sub_integral_le`), and these costs telescope to at most `4πθ`;
* for the linear interpolant, `e(f(p)) − ∫_p^{p+1} e = G(Δ) (e(f(p+1)) − e(f(p)))` exactly,
  where `G(Δ) = 1/(e(Δ) − 1) − 1/(2πiΔ) = −1/2 − (i/2) k(Δ)` with
  `k(Δ) = cot(πΔ) − 1/(πΔ)` (`ampDefect_mul_e2pi_sub_one`, `integral_e2pi_linear`);
* `k` is decreasing on `(−1, 1)` (`antitoneOn_cotDefect`) and the increments `Δ` are monotone
  in `p` (`increment_mem_unit`), so Abel summation (`norm_sum_mul_sub_le`) bounds
  `∑ G(Δ_n)(e(f(n+1)) − e(f(n)))` by `|G|` at the two ends plus the total variation of `G`
  along the increments, which telescopes to at most `κ(θ)`.

No hypothesis is assumed.
-/

noncomputable section

open Complex Real Finset MeasureTheory intervalIntegral

namespace RiemannHypothesis

namespace VdcSumIntegral

open KusminLandau

/-- `k(Δ) = cot(πΔ) − 1/(πΔ)`; at `Δ = 0` both terms are `0` by Lean's convention `1/0 = 0`. -/
def cotDefect (Δ : ℝ) : ℝ := cotpi Δ - 1 / (Real.pi * Δ)

/-- `G(Δ) = −1/2 − (i/2) k(Δ) = 1/(e(Δ) − 1) − 1/(2πiΔ)`. -/
def ampDefect (Δ : ℝ) : ℂ := -(1 / 2 : ℂ) - (Complex.I / 2) * (cotDefect Δ : ℂ)

/-- The constant `κ(θ) = 1/(πθ) − cot(πθ) = −k(θ) ≥ 0`. -/
def vdcKappa (θ : ℝ) : ℝ := -cotDefect θ

/-- The identity `G(Δ) (e(Δ) − 1) = 1 − (e(Δ) − 1)/(2πiΔ)` for `sin πΔ ≠ 0`, `Δ ≠ 0`. -/
theorem ampDefect_mul_e2pi_sub_one {Δ : ℝ} (hΔ : Δ ≠ 0) (hs : Real.sin (Real.pi * Δ) ≠ 0) :
    ampDefect Δ * (e2pi Δ - 1)
      = 1 - (e2pi Δ - 1) / (2 * (Real.pi : ℂ) * Complex.I * (Δ : ℂ)) := by
  set S : ℂ := ((Real.sin (Real.pi * Δ) : ℝ) : ℂ) with hS
  set C : ℂ := ((Real.cos (Real.pi * Δ) : ℝ) : ℂ) with hC
  have hSne : S ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΔc : (Δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ
  have hpyth : S ^ 2 + C ^ 2 = 1 := by
    rw [hS, hC, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.sin_sq_add_cos_sq]
    norm_num
  have hk : ((cotDefect Δ : ℝ) : ℂ) = C / S - 1 / ((Real.pi : ℂ) * Δ) := by
    rw [hS, hC, cotDefect, cotpi]
    push_cast
    ring
  have hfac : e2pi Δ - 1 = 2 * S * (-S + C * Complex.I) := by
    rw [e2pi_sub_one_eq, hS, hC]
    push_cast
    ring
  rw [ampDefect, hk, hfac]
  field_simp
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  simp only [hI3, Complex.I_sq]
  linear_combination (Complex.I * Real.pi * Δ) * hpyth

theorem cotDefect_neg (Δ : ℝ) : cotDefect (-Δ) = -cotDefect Δ := by
  simp only [cotDefect, cotpi, mul_neg, Real.cos_neg, Real.sin_neg, div_neg]
  ring

theorem cotDefect_zero : cotDefect 0 = 0 := by
  simp [cotDefect, cotpi]

/-- `cot x ≤ 1/x` on `(0, π)`, i.e. `k ≤ 0` on `(0, 1)`. -/
theorem cotDefect_nonpos {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) : cotDefect Δ ≤ 0 := by
  have hx : 0 < Real.pi * Δ := mul_pos Real.pi_pos h0
  have hs : 0 < Real.sin (Real.pi * Δ) := sin_pi_mul_pos h0 h1
  have key : Real.pi * Δ * Real.cos (Real.pi * Δ) ≤ Real.sin (Real.pi * Δ) := by
    rcases lt_or_ge (Real.pi * Δ) (Real.pi / 2) with h | h
    · have hc : 0 < Real.cos (Real.pi * Δ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
      have ht := Real.lt_tan hx h
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
      linarith
    · have hc : Real.cos (Real.pi * Δ) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le h (by nlinarith [Real.pi_pos])
      nlinarith
  rw [cotDefect, cotpi, sub_nonpos, div_le_div_iff₀ hs hx]
  linarith

/-- The derivative of `k` on `(0, 1)`. -/
theorem hasDerivAt_cotDefect {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) :
    HasDerivAt cotDefect
      (-Real.pi / Real.sin (Real.pi * Δ) ^ 2 + Real.pi / (Real.pi * Δ) ^ 2) Δ := by
  have hs : Real.sin (Real.pi * Δ) ≠ 0 := (sin_pi_mul_pos h0 h1).ne'
  have hx : Real.pi * Δ ≠ 0 := (mul_pos Real.pi_pos h0).ne'
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi Δ := by
    simpa using (hasDerivAt_id Δ).const_mul Real.pi
  have hcos := (Real.hasDerivAt_cos (Real.pi * Δ)).comp Δ hlin
  have hsin := (Real.hasDerivAt_sin (Real.pi * Δ)).comp Δ hlin
  have hq := hcos.div hsin hs
  have hinv := hlin.inv hx
  have h := hq.sub hinv
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · have hp := Real.sin_sq_add_cos_sq (Real.pi * Δ)
    simp only [Function.comp]
    field_simp
    linear_combination (-(Real.pi * Δ) ^ 2) * hp
  · simp [cotDefect, cotpi, one_div, Function.comp]

/-- `k` is antitone on `(0, 1)`: `k' = π (1/(πΔ)² − 1/sin² πΔ) ≤ 0` since `sin x ≤ x`. -/
theorem antitoneOn_cotDefect_pos : AntitoneOn cotDefect (Set.Ioo 0 1) := by
  have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1) := convex_Ioo 0 1
  refine antitoneOn_of_hasDerivWithinAt_nonpos hconv ?_ (f' := fun Δ =>
      -Real.pi / Real.sin (Real.pi * Δ) ^ 2 + Real.pi / (Real.pi * Δ) ^ 2) ?_ ?_
  · intro Δ hΔ
    exact (hasDerivAt_cotDefect hΔ.1 hΔ.2).continuousAt.continuousWithinAt
  · intro Δ hΔ
    rw [interior_Ioo] at hΔ
    exact (hasDerivAt_cotDefect hΔ.1 hΔ.2).hasDerivWithinAt
  · intro Δ hΔ
    rw [interior_Ioo] at hΔ
    have hs : 0 < Real.sin (Real.pi * Δ) := sin_pi_mul_pos hΔ.1 hΔ.2
    have hx : 0 < Real.pi * Δ := mul_pos Real.pi_pos hΔ.1
    have hle : Real.sin (Real.pi * Δ) ≤ Real.pi * Δ := Real.sin_le hx.le
    have hsq : Real.sin (Real.pi * Δ) ^ 2 ≤ (Real.pi * Δ) ^ 2 := by
      exact pow_le_pow_left₀ hs.le hle 2
    have : Real.pi / (Real.pi * Δ) ^ 2 ≤ Real.pi / Real.sin (Real.pi * Δ) ^ 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hsq
    rw [neg_div]
    linarith

/-- `k` is antitone on `(−1, 1)`. -/
theorem antitoneOn_cotDefect : AntitoneOn cotDefect (Set.Ioo (-1) 1) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · rcases lt_or_ge y 0 with hy0 | hy0
    · have h := antitoneOn_cotDefect_pos (a := -y) (b := -x) ⟨by linarith, by linarith [hy.1]⟩
        ⟨by linarith, by linarith [hx.1]⟩ (by linarith)
      rw [cotDefect_neg, cotDefect_neg] at h
      linarith
    · have h1 : cotDefect (-x) ≤ 0 := cotDefect_nonpos (by linarith) (by linarith [hx.1])
      rw [cotDefect_neg] at h1
      rcases hy0.lt_or_eq with hy0 | hy0
      · have h2 := cotDefect_nonpos hy0 hy.2
        linarith
      · rw [← hy0, cotDefect_zero]
        linarith
  · subst hx0
    rcases hxy.lt_or_eq with hy0 | hy0
    · rw [cotDefect_zero]
      exact cotDefect_nonpos hy0 hy.2
    · rw [← hy0]
  · exact antitoneOn_cotDefect_pos ⟨hx0, hx.2⟩ ⟨by linarith, hy.2⟩ hxy

theorem vdcKappa_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ vdcKappa θ := by
  rcases h0.lt_or_eq with h0 | h0
  · have := cotDefect_nonpos h0 h1
    rw [vdcKappa]
    linarith
  · rw [← h0, vdcKappa, cotDefect_zero, neg_zero]

/-- `|k(Δ)| ≤ κ(θ)` for `|Δ| ≤ θ < 1`. -/
theorem abs_cotDefect_le {Δ θ : ℝ} (h1 : θ < 1) (h : |Δ| ≤ θ) : |cotDefect Δ| ≤ vdcKappa θ := by
  have h0 : 0 ≤ θ := (abs_nonneg Δ).trans h
  have hΔ := abs_le.mp h
  have hθmem : θ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, h1⟩
  have hnθmem : -θ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hΔmem : Δ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have ha := antitoneOn_cotDefect hΔmem hθmem hΔ.2
  have hb := antitoneOn_cotDefect hnθmem hΔmem hΔ.1
  rw [cotDefect_neg] at hb
  rw [vdcKappa, abs_le]
  constructor <;> linarith

theorem norm_ampDefect_le (Δ : ℝ) : ‖ampDefect Δ‖ ≤ (1 + |cotDefect Δ|) / 2 := by
  rw [ampDefect]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖Complex.I / 2 * (cotDefect Δ : ℂ)‖ = |cotDefect Δ| / 2 := by
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    ring
  have h2 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h1, h2]
  linarith

theorem norm_ampDefect_sub (Δ Δ' : ℝ) :
    ‖ampDefect Δ - ampDefect Δ'‖ = |cotDefect Δ - cotDefect Δ'| / 2 := by
  rw [ampDefect, ampDefect,
    show (-(1 / 2 : ℂ) - Complex.I / 2 * (cotDefect Δ : ℂ))
      - (-(1 / 2 : ℂ) - Complex.I / 2 * (cotDefect Δ' : ℂ))
      = -(Complex.I / 2) * ((cotDefect Δ - cotDefect Δ' : ℝ) : ℂ) by push_cast; ring,
    norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real]
  norm_num
  ring

/-! ## Abel summation -/

/-- **Abel summation** against differences of unimodular numbers. -/
theorem norm_sum_mul_sub_le (c E : ℕ → ℂ) (hE : ∀ n, ‖E n‖ ≤ 1) (M : ℕ) :
    ‖∑ n ∈ range (M + 1), c n * (E (n + 1) - E n)‖
      ≤ ‖c M‖ + ‖c 0‖ + ∑ n ∈ range M, ‖c (n + 1) - c n‖ := by
  have hid : ∀ M : ℕ, ∑ n ∈ range (M + 1), c n * (E (n + 1) - E n)
      = c M * E (M + 1) - c 0 * E 0 - ∑ n ∈ range M, (c (n + 1) - c n) * E (n + 1) := by
    intro M
    induction M with
    | zero => simp; ring
    | succ M ih => rw [sum_range_succ, ih, sum_range_succ]; ring
  rw [hid]
  have h1 : ‖c M * E (M + 1)‖ ≤ ‖c M‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hE _)
  have h2 : ‖c 0 * E 0‖ ≤ ‖c 0‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hE _)
  have h3 : ‖∑ n ∈ range M, (c (n + 1) - c n) * E (n + 1)‖
      ≤ ∑ n ∈ range M, ‖c (n + 1) - c n‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hE _)
  calc _ ≤ ‖c M * E (M + 1) - c 0 * E 0‖ + ‖∑ n ∈ range M, (c (n + 1) - c n) * E (n + 1)‖ :=
        norm_sub_le _ _
    _ ≤ ‖c M * E (M + 1)‖ + ‖c 0 * E 0‖ + ‖∑ n ∈ range M, (c (n + 1) - c n) * E (n + 1)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-! ## One unit interval -/

theorem continuous_e2pi : Continuous e2pi := by
  unfold e2pi
  fun_prop

theorem norm_e2pi_sub_e2pi_le (x y : ℝ) : ‖e2pi x - e2pi y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : e2pi x - e2pi y
      = e2pi y * (Complex.exp (Complex.I * ((2 * Real.pi * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, e2pi, e2pi, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_e2pi, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- The mean value theorem on `[p, p + 1]`: the increment `f(p+1) − f(p)` lies between the
end values of the monotone derivative. -/
theorem increment_mem_unit {p : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc p (p + 1), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc p (p + 1))) :
    f' p ≤ f (p + 1) - f p ∧ f (p + 1) - f p ≤ f' (p + 1) := by
  have hcont : ContinuousOn f (Set.Icc p (p + 1)) := fun u hu =>
    (hf u hu).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hfc⟩ := exists_hasDerivAt_eq_slope f f' (by linarith : p < p + 1) hcont
    (fun u hu => hf u (Set.Ioo_subset_Icc_self hu))
  rw [show p + 1 - p = (1 : ℝ) by ring, div_one] at hfc
  have hcI : c ∈ Set.Icc p (p + 1) := Set.Ioo_subset_Icc_self hc
  have hp : p ∈ Set.Icc p (p + 1) := ⟨le_rfl, by linarith⟩
  have hp1 : p + 1 ∈ Set.Icc p (p + 1) := ⟨by linarith, le_rfl⟩
  exact ⟨hfc ▸ hmono hp hcI hc.1.le, hfc ▸ hmono hcI hp1 hc.2.le⟩

/-- The integral of `e` of the linear interpolant of `f` on `[p, p + 1]`. -/
theorem integral_e2pi_linear (p F Δ : ℝ) (hΔ : |Δ| < 1) :
    ∫ u in p..p + 1, e2pi (F + Δ * (u - p))
      = e2pi F - ampDefect Δ * (e2pi (F + Δ) - e2pi F) := by
  rcases eq_or_ne Δ 0 with h0 | h0
  · subst h0
    simp
  have hs : Real.sin (Real.pi * Δ) ≠ 0 := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have := sin_pi_mul_pos (θ := -Δ) (by linarith) (by linarith [neg_abs_le Δ, abs_lt.mp hΔ])
      rw [mul_neg, Real.sin_neg] at this
      linarith
    · exact (sin_pi_mul_pos hpos (lt_of_le_of_lt (le_abs_self Δ) hΔ)).ne'
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (Δ : ℂ) with hc
  have hc0 : c ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hΔc : (Δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
    simp [hc, hpi, hΔc, Complex.I_ne_zero]
  set A : ℂ := ((2 * Real.pi * (F - Δ * p) : ℝ) : ℂ) * Complex.I with hA
  have hlin : ∀ u : ℝ, e2pi (F + Δ * (u - p)) = Complex.exp A * Complex.exp (c * u) := by
    intro u
    rw [e2pi, ← Complex.exp_add, hA, hc]
    congr 1
    push_cast
    ring
  have hF : e2pi F = Complex.exp A * Complex.exp (c * p) := by
    have := hlin p
    rwa [sub_self, mul_zero, add_zero] at this
  have hFΔ : e2pi (F + Δ) = e2pi F * e2pi Δ := e2pi_add F Δ
  have hΔe : e2pi Δ = Complex.exp c := by
    rw [e2pi, hc]
    congr 1
    push_cast
    ring
  simp_rw [hlin]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc0]
  have hid := ampDefect_mul_e2pi_sub_one h0 hs
  rw [hFΔ, show e2pi F * e2pi Δ - e2pi F = e2pi F * (e2pi Δ - 1) by ring,
    show ampDefect Δ * (e2pi F * (e2pi Δ - 1)) = e2pi F * (ampDefect Δ * (e2pi Δ - 1)) by ring,
    hid, ← hc, hΔe, hF]
  push_cast
  rw [mul_add, Complex.exp_add, mul_one]
  field_simp
  ring

/-- **The local estimate.**  On `[p, p + 1]`, with `Δ = f(p+1) − f(p)`,
`e(f(p)) − ∫_p^{p+1} e(f) = G(Δ) (e(f(p+1)) − e(f(p))) + O(2π (f'(p+1) − f'(p)))`. -/
theorem norm_unit_sub_integral_le {p : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc p (p + 1), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc p (p + 1)))
    (hΔ : |f (p + 1) - f p| < 1) :
    ‖(e2pi (f p) - ampDefect (f (p + 1) - f p) * (e2pi (f (p + 1)) - e2pi (f p)))
        - ∫ u in p..p + 1, e2pi (f u)‖ ≤ 2 * Real.pi * (f' (p + 1) - f' p) := by
  set Δ := f (p + 1) - f p with hΔdef
  obtain ⟨h1, h2⟩ := increment_mem_unit hf hmono
  have hlinint := integral_e2pi_linear p (f p) Δ hΔ
  rw [show f p + Δ = f (p + 1) by rw [hΔdef]; ring] at hlinint
  rw [← hlinint]
  have hIcc : Set.uIcc p (p + 1) = Set.Icc p (p + 1) := Set.uIcc_of_le (by linarith)
  have hint1 : IntervalIntegrable (fun u => e2pi (f p + Δ * (u - p))) MeasureTheory.volume
      p (p + 1) :=
    (continuous_e2pi.comp (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u => e2pi (f u)) MeasureTheory.volume p (p + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact continuous_e2pi.comp_continuousOn fun u hu => (hf u hu).continuousAt.continuousWithinAt
  rw [← intervalIntegral.integral_sub hint1 hint2]
  -- the distance from `f` to its linear interpolant
  have hdist : ∀ u ∈ Set.Icc p (p + 1), |f p + Δ * (u - p) - f u| ≤ f' (p + 1) - f' p := by
    intro u hu
    have hderiv : ∀ v ∈ Set.Icc p (p + 1), HasDerivWithinAt (fun v => f v - (f p + Δ * (v - p)))
        (f' v - Δ) (Set.Icc p (p + 1)) v := by
      intro v hv
      have hl : HasDerivAt (fun v : ℝ => f p + Δ * (v - p)) Δ v := by
        simpa using ((hasDerivAt_id v).sub_const p).const_mul Δ |>.const_add (f p)
      exact ((hf v hv).sub hl).hasDerivWithinAt
    have hbd : ∀ v ∈ Set.Icc p (p + 1), ‖f' v - Δ‖ ≤ f' (p + 1) - f' p := by
      intro v hv
      have hp : p ∈ Set.Icc p (p + 1) := ⟨le_rfl, by linarith⟩
      have hp1 : p + 1 ∈ Set.Icc p (p + 1) := ⟨by linarith, le_rfl⟩
      have ha := hmono hp hv hv.1
      have hb := hmono hv hp1 hv.2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hp : p ∈ Set.Icc p (p + 1) := ⟨le_rfl, by linarith⟩
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_Icc _ _) hp hu
    have hw : 0 ≤ f' (p + 1) - f' p := by linarith
    simp only [sub_self, mul_zero, add_zero, sub_zero, Real.norm_eq_abs] at h
    rw [abs_sub_comm]
    calc |f u - (f p + Δ * (u - p))| ≤ (f' (p + 1) - f' p) * |u - p| := h
      _ ≤ (f' (p + 1) - f' p) * 1 := by
          gcongr
          rw [abs_le]
          constructor <;> linarith [hu.1, hu.2]
      _ = _ := mul_one _
  have hbound : ∀ u ∈ Set.uIoc p (p + 1),
      ‖e2pi (f p + Δ * (u - p)) - e2pi (f u)‖ ≤ 2 * Real.pi * (f' (p + 1) - f' p) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    refine (norm_e2pi_sub_e2pi_le _ _).trans ?_
    gcongr
    exact hdist u (Set.Ioc_subset_Icc_self hu)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans (le_of_eq ?_)
  rw [show p + 1 - p = (1 : ℝ) by ring, abs_one, mul_one]

/-! ## The sum-versus-integral lemma -/

/-- **van der Corput's sum-versus-integral lemma, with a monotone weight** (Titchmarsh, *The
Theory of the Riemann Zeta-Function*, Lemmas 4.8 and 4.10, in the form needed for `ζ`).

Let `f` be real and differentiable on `[a, a + N]` with `f'` monotone (increasing) and
`|f'| ≤ θ < 1`, and let `g ≥ 0` be continuous and decreasing on `[a, a + N]`.  Then
`‖∑_{n < N} g(a+n) e(f(a+n)) − ∫_a^{a+N} g(u) e(f(u)) du‖ ≤ (5/2 + 4πθ + 5κ(θ)/2) g(a)`,
with `κ(θ) = 1/(πθ) − cot(πθ)` (`vdcKappa`). -/
theorem norm_sum_mul_e2pi_sub_integral_le {a θ : ℝ} {N : ℕ} {f f' g : ℝ → ℝ}
    (hθ : θ < 1)
    (hf : ∀ u ∈ Set.Icc a (a + N), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc a (a + N)))
    (hbd : ∀ u ∈ Set.Icc a (a + N), |f' u| ≤ θ)
    (hg : ContinuousOn g (Set.Icc a (a + N)))
    (hg0 : ∀ u ∈ Set.Icc a (a + N), 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc a (a + N))) :
    ‖∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (f (a + n))
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)‖
      ≤ (5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ) * g a := by
  have haI : a ∈ Set.Icc a (a + N) := ⟨le_rfl, by simp⟩
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hbd a haI)
  have hκ := vdcKappa_nonneg hθ0 hθ
  have hga := hg0 a haI
  have hK : 0 ≤ (5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ) * g a := by positivity
  rcases Nat.eq_zero_or_eq_succ_pred N with hN | hN
  · subst hN
    simpa using hK
  set M := N.pred with hMdef
  set q : ℕ → ℝ := fun n => a + n with hqdef
  have hq : ∀ n, q (n + 1) = q n + 1 := by intro n; simp only [hqdef]; push_cast; ring
  have hqmem : ∀ n, n ≤ N → q n ∈ Set.Icc a (a + N) := by
    intro n hn
    refine ⟨by simp [hqdef], ?_⟩
    simp only [hqdef]
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    linarith
  have hsub : ∀ n, n < N → Set.Icc (q n) (q n + 1) ⊆ Set.Icc a (a + N) := by
    intro n hn u hu
    have h1 := hqmem n hn.le
    have h2 := hqmem (n + 1) hn
    rw [hq] at h2
    exact ⟨h1.1.trans hu.1, hu.2.trans h2.2⟩
  set Δ : ℕ → ℝ := fun n => f (q n + 1) - f (q n) with hΔdef
  set E : ℕ → ℂ := fun n => e2pi (f (q n)) with hEdef
  have hinc : ∀ n, n < N → f' (q n) ≤ Δ n ∧ Δ n ≤ f' (q n + 1) := fun n hn =>
    increment_mem_unit (fun u hu => hf u (hsub n hn hu)) (hmono.mono (hsub n hn))
  have hΔbd : ∀ n, n < N → |Δ n| ≤ θ := by
    intro n hn
    have h1 := abs_le.mp (hbd _ (hqmem n hn.le))
    have h2 := abs_le.mp (hbd _ (hqmem (n + 1) hn))
    rw [hq] at h2
    obtain ⟨i1, i2⟩ := hinc n hn
    rw [abs_le]
    constructor <;> linarith
  have hk : ∀ n, n < N → |cotDefect (Δ n)| ≤ vdcKappa θ := fun n hn =>
    abs_cotDefect_le hθ (hΔbd n hn)
  have hgq : ∀ n, n ≤ N → g (q n) ≤ g a := fun n hn =>
    hganti haI (hqmem n hn) (hqmem n hn).1
  have hgq0 : ∀ n, n ≤ N → 0 ≤ g (q n) := fun n hn => hg0 _ (hqmem n hn)
  have hgstep : ∀ n, n < N → g (q (n + 1)) ≤ g (q n) := by
    intro n hn
    refine hganti (hqmem n hn.le) (hqmem (n + 1) hn) ?_
    rw [hq]; linarith
  -- integrability on each unit interval
  have hIcc : ∀ n, Set.uIcc (q n) (q n + 1) = Set.Icc (q n) (q n + 1) := fun n =>
    Set.uIcc_of_le (by linarith)
  have hcontf : ContinuousOn (fun u => e2pi (f u)) (Set.Icc a (a + N)) :=
    continuous_e2pi.comp_continuousOn fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hcontg : ContinuousOn (fun u => (g u : ℂ) * e2pi (f u)) (Set.Icc a (a + N)) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).mul hcontf
  have hint_e : ∀ n, n < N →
      IntervalIntegrable (fun u => e2pi (f u)) MeasureTheory.volume (q n) (q n + 1) := by
    intro n hn
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact hcontf.mono (hsub n hn)
  have hint_ge : ∀ n, n < N →
      IntervalIntegrable (fun u => (g u : ℂ) * e2pi (f u)) MeasureTheory.volume
        (q n) (q n + 1) := by
    intro n hn
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact hcontg.mono (hsub n hn)
  -- splitting the integral
  have hsplit : ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)
      = ∑ n ∈ range N, ∫ u in q n..q n + 1, (g u : ℂ) * e2pi (f u) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := q) (n := N)
      (f := fun u => (g u : ℂ) * e2pi (f u)) (μ := MeasureTheory.volume)
      (fun k hk => by rw [hq]; exact hint_ge k hk)
    simp only [hq] at h
    rw [h]
    simp [hqdef]
  -- the three pieces
  set X : ℕ → ℂ := fun n => ∫ u in q n..q n + 1, ((g (q n) - g u : ℝ) : ℂ) * e2pi (f u)
    with hXdef
  set R : ℕ → ℂ := fun n => (g (q n) : ℂ) *
    ((E n - ampDefect (Δ n) * (E (n + 1) - E n)) - ∫ u in q n..q n + 1, e2pi (f u)) with hRdef
  set c : ℕ → ℂ := fun n => (g (q n) : ℂ) * ampDefect (Δ n) with hcdef
  have hE1 : ∀ n, E (n + 1) = e2pi (f (q n + 1)) := fun n => by simp only [hEdef, hq]
  have hpiece : ∀ n, n < N →
      (g (q n) : ℂ) * E n - ∫ u in q n..q n + 1, (g u : ℂ) * e2pi (f u)
        = X n + R n + c n * (E (n + 1) - E n) := by
    intro n hn
    have hX : X n = (g (q n) : ℂ) * (∫ u in q n..q n + 1, e2pi (f u))
        - ∫ u in q n..q n + 1, (g u : ℂ) * e2pi (f u) := by
      rw [hXdef, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub ((hint_e n hn).const_mul _) (hint_ge n hn)]
      refine intervalIntegral.integral_congr fun u _ => ?_
      push_cast
      ring
    rw [hX, hRdef, hcdef]
    ring
  have hsum_eq : ∑ n ∈ range N, (g (q n) : ℂ) * E n
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)
      = ∑ n ∈ range N, X n + ∑ n ∈ range N, R n + ∑ n ∈ range N, c n * (E (n + 1) - E n) := by
    rw [hsplit, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n hn => hpiece n (mem_range.mp hn)
  -- bounds on the pieces
  have hXb : ‖∑ n ∈ range N, X n‖ ≤ g a := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ range N, ‖X n‖ ≤ g (q n) - g (q (n + 1)) := by
      intro n hn
      have hn' := mem_range.mp hn
      have hb : ∀ u ∈ Set.uIoc (q n) (q n + 1),
          ‖((g (q n) - g u : ℝ) : ℂ) * e2pi (f u)‖ ≤ g (q n) - g (q (n + 1)) := by
        intro u hu
        rw [Set.uIoc_of_le (by linarith)] at hu
        have huI := hsub n hn' (Set.Ioc_subset_Icc_self hu)
        have h1 := hganti (hqmem n hn'.le) huI hu.1.le
        have h2 := hganti huI (hqmem (n + 1) hn') (by rw [hq]; exact hu.2)
        rw [norm_mul, norm_e2pi, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
        linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
      rw [show q n + 1 - q n = (1 : ℝ) by ring, abs_one, mul_one]
    refine (sum_le_sum hterm).trans ?_
    rw [sum_range_sub' (fun n => g (q n)) N]
    have := hgq0 N le_rfl
    have h0 : q 0 = a := by simp [hqdef]
    rw [h0]
    linarith
  have hRb : ‖∑ n ∈ range N, R n‖ ≤ 4 * Real.pi * θ * g a := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ range N, ‖R n‖ ≤ g a * (2 * Real.pi * (f' (q (n + 1)) - f' (q n))) := by
      intro n hn
      have hn' := mem_range.mp hn
      have hloc := norm_unit_sub_integral_le (p := q n) (f := f) (f' := f')
        (fun u hu => hf u (hsub n hn' hu)) (hmono.mono (hsub n hn'))
        (lt_of_le_of_lt (hΔbd n hn') hθ)
      have hw : 0 ≤ f' (q (n + 1)) - f' (q n) := by
        rw [hq]; obtain ⟨i1, i2⟩ := hinc n hn'; linarith
      rw [hRdef]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgq0 n hn'.le), hE1, hq]
      exact mul_le_mul (hgq n hn'.le) hloc (norm_nonneg _) hga
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum, ← mul_sum, sum_range_sub (fun n => f' (q n)) N]
    have h1 := abs_le.mp (hbd _ (hqmem N le_rfl))
    have h2 := abs_le.mp (hbd _ (hqmem 0 (Nat.zero_le _)))
    have hpi := Real.pi_pos
    have : f' (q N) - f' (q 0) ≤ 2 * θ := by linarith
    calc g a * (2 * Real.pi * (f' (q N) - f' (q 0))) ≤ g a * (2 * Real.pi * (2 * θ)) := by
          gcongr
      _ = 4 * Real.pi * θ * g a := by ring
  have hCb : ‖∑ n ∈ range N, c n * (E (n + 1) - E n)‖
      ≤ (3 / 2 * (1 + vdcKappa θ) + vdcKappa θ) * g a := by
    have hEn : ∀ n, ‖E n‖ ≤ 1 := fun n => by simp [hEdef]
    rw [hN]
    refine (norm_sum_mul_sub_le c E hEn M).trans ?_
    have hMN : M < N := by omega
    have hcn : ∀ n, n < N → ‖c n‖ ≤ g a * ((1 + vdcKappa θ) / 2) := by
      intro n hn
      rw [hcdef]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgq0 n hn.le)]
      refine mul_le_mul (hgq n hn.le) ((norm_ampDefect_le _).trans ?_) (norm_nonneg _) hga
      have := hk n hn
      linarith
    have hstep : ∀ n ∈ range M, ‖c (n + 1) - c n‖
        ≤ g a * ((cotDefect (Δ n) - cotDefect (Δ (n + 1))) / 2)
          + (1 + vdcKappa θ) / 2 * (g (q n) - g (q (n + 1))) := by
      intro n hn
      have hn' : n + 1 < N := by have := mem_range.mp hn; omega
      have hn'' : n < N := by omega
      -- monotonicity of the increments and of `k`
      have hmon : Δ n ≤ Δ (n + 1) := by
        have i1 := (hinc n hn'').2
        have i2 := (hinc (n + 1) hn').1
        rw [hq] at i2
        linarith
      have hmem : ∀ m, m < N → Δ m ∈ Set.Ioo (-1 : ℝ) 1 := by
        intro m hm
        have := abs_le.mp (hΔbd m hm)
        exact ⟨by linarith, by linarith⟩
      have hkmon := antitoneOn_cotDefect (hmem n hn'') (hmem (n + 1) hn') hmon
      have hdecomp : c (n + 1) - c n
          = (g (q (n + 1)) : ℂ) * (ampDefect (Δ (n + 1)) - ampDefect (Δ n))
          - ((g (q n) - g (q (n + 1)) : ℝ) : ℂ) * ampDefect (Δ n) := by
        rw [hcdef]; push_cast; ring
      rw [hdecomp]
      refine (norm_sub_le _ _).trans ?_
      have a1 : |cotDefect (Δ (n + 1)) - cotDefect (Δ n)|
          = cotDefect (Δ n) - cotDefect (Δ (n + 1)) := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have a2 : |g (q n) - g (q (n + 1))| = g (q n) - g (q (n + 1)) :=
        abs_of_nonneg (by linarith [hgstep n hn''])
      have a3 : |g (q (n + 1))| = g (q (n + 1)) := abs_of_nonneg (hgq0 _ hn'.le)
      rw [norm_mul, norm_mul, norm_ampDefect_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, a1, a2, a3]
      have hG := (norm_ampDefect_le (Δ n)).trans
        (show (1 + |cotDefect (Δ n)|) / 2 ≤ (1 + vdcKappa θ) / 2 by linarith [hk n hn''])
      have hgs := hgstep n hn''
      have hkd : 0 ≤ (cotDefect (Δ n) - cotDefect (Δ (n + 1))) / 2 := by linarith
      have e1 : g (q (n + 1)) * ((cotDefect (Δ n) - cotDefect (Δ (n + 1))) / 2)
          ≤ g a * ((cotDefect (Δ n) - cotDefect (Δ (n + 1))) / 2) :=
        mul_le_mul_of_nonneg_right (hgq _ hn'.le) hkd
      have e2 : (g (q n) - g (q (n + 1))) * ‖ampDefect (Δ n)‖
          ≤ (1 + vdcKappa θ) / 2 * (g (q n) - g (q (n + 1))) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hG (by linarith)
      linarith
    refine add_le_add (add_le_add (hcn M hMN) (hcn 0 (by omega))) (sum_le_sum hstep)
      |>.trans ?_
    have t1 : ∑ i ∈ range M, (cotDefect (Δ i) - cotDefect (Δ (i + 1)))
        = cotDefect (Δ 0) - cotDefect (Δ M) := sum_range_sub' (fun i => cotDefect (Δ i)) M
    have t2 : ∑ i ∈ range M, (g (q i) - g (q (i + 1))) = g (q 0) - g (q M) :=
      sum_range_sub' (fun i => g (q i)) M
    have hs : ∑ i ∈ range M, (g a * ((cotDefect (Δ i) - cotDefect (Δ (i + 1))) / 2)
        + (1 + vdcKappa θ) / 2 * (g (q i) - g (q (i + 1))))
        = g a * ((cotDefect (Δ 0) - cotDefect (Δ M)) / 2)
          + (1 + vdcKappa θ) / 2 * (g (q 0) - g (q M)) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_div, t1, t2]
    rw [hs]
    have k0 := abs_le.mp (hk 0 (by omega))
    have kM := abs_le.mp (hk M hMN)
    have g0 : g (q 0) ≤ g a := hgq 0 (by omega)
    have gM := hgq0 M hMN.le
    have hkd : (cotDefect (Δ 0) - cotDefect (Δ M)) / 2 ≤ vdcKappa θ := by linarith
    have e1 : g a * ((cotDefect (Δ 0) - cotDefect (Δ M)) / 2) ≤ g a * vdcKappa θ :=
      mul_le_mul_of_nonneg_left hkd hga
    have e2 : (1 + vdcKappa θ) / 2 * (g (q 0) - g (q M)) ≤ (1 + vdcKappa θ) / 2 * g a :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  -- assembling
  have hsum_q : ∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (f (a + n))
      = ∑ n ∈ range N, (g (q n) : ℂ) * E n := rfl
  rw [hsum_q, hsum_eq]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) hCb).trans ?_)
  nlinarith [hXb, hRb]

theorem e2pi_neg (x : ℝ) : e2pi (-x) = (starRingEnd ℂ) (e2pi x) := by
  rw [e2pi, e2pi, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The same lemma when `f'` is decreasing instead of increasing (apply the first form to `−f`;
`e(−x)` is the complex conjugate of `e(x)`). -/
theorem norm_sum_mul_e2pi_sub_integral_le_of_antitone {a θ : ℝ} {N : ℕ} {f f' g : ℝ → ℝ}
    (hθ : θ < 1)
    (hf : ∀ u ∈ Set.Icc a (a + N), HasDerivAt f (f' u) u)
    (hanti : AntitoneOn f' (Set.Icc a (a + N)))
    (hbd : ∀ u ∈ Set.Icc a (a + N), |f' u| ≤ θ)
    (hg : ContinuousOn g (Set.Icc a (a + N)))
    (hg0 : ∀ u ∈ Set.Icc a (a + N), 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc a (a + N))) :
    ‖∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (f (a + n))
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)‖
      ≤ (5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ) * g a := by
  have h := norm_sum_mul_e2pi_sub_integral_le (f := fun u => -f u) (f' := fun u => -f' u)
    hθ (fun u hu => (hf u hu).neg) (fun x hx y hy hxy => neg_le_neg (hanti hx hy hxy))
    (fun u hu => by rw [abs_neg]; exact hbd u hu) hg hg0 hganti
  have hN : (a : ℝ) ≤ a + N := by simp
  have hconj : (∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (-f (a + n))
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (-f u))
      = (starRingEnd ℂ) (∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (f (a + n))
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)) := by
    rw [map_sub, map_sum, intervalIntegral.integral_of_le hN, intervalIntegral.integral_of_le hN,
      ← integral_conj]
    congr 1
    · refine sum_congr rfl fun n _ => ?_
      rw [map_mul, Complex.conj_ofReal, e2pi_neg]
    · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [map_mul, Complex.conj_ofReal, e2pi_neg]
  rw [hconj, Complex.norm_conj] at h
  exact h

/-- **van der Corput's sum-versus-integral lemma** (Titchmarsh, Lemma 4.8): for real `f` on
`[a, a + N]` with `f'` monotone and `|f'| ≤ θ < 1`,
`‖∑_{n < N} e(f(a+n)) − ∫_a^{a+N} e(f(u)) du‖ ≤ 5/2 + 4πθ + 5κ(θ)/2`. -/
theorem norm_sum_e2pi_sub_integral_le {a θ : ℝ} {N : ℕ} {f f' : ℝ → ℝ}
    (hθ : θ < 1)
    (hf : ∀ u ∈ Set.Icc a (a + N), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc a (a + N)) ∨ AntitoneOn f' (Set.Icc a (a + N)))
    (hbd : ∀ u ∈ Set.Icc a (a + N), |f' u| ≤ θ) :
    ‖∑ n ∈ range N, e2pi (f (a + n)) - ∫ u in a..a + N, e2pi (f u)‖
      ≤ 5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ := by
  have hg : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a (a + N)) := continuousOn_const
  have hg0 : ∀ u ∈ Set.Icc a (a + N), (0 : ℝ) ≤ (fun _ : ℝ => (1 : ℝ)) u :=
    fun _ _ => zero_le_one
  have hganti : AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a (a + N)) :=
    fun _ _ _ _ _ => le_rfl
  rcases hmono with hmono | hmono
  · simpa using norm_sum_mul_e2pi_sub_integral_le hθ hf hmono hbd hg hg0 hganti
  · simpa using norm_sum_mul_e2pi_sub_integral_le_of_antitone hθ hf hmono hbd hg hg0 hganti

end VdcSumIntegral

end RiemannHypothesis
