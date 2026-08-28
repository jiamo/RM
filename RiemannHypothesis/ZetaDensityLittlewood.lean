/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BacklundZeta

/-!
# The Littlewood route to a zero-density estimate

`RiemannHypothesis.LittlewoodZetaBound` bounds every term of Littlewood's lemma for `ζ` on a
rectangle `[σ, 3] × [T₁, T₂]` except the two horizontal argument terms, and
`RiemannHypothesis.BacklundZeta` bounds those by `O(log T)`.  Putting the two together closes the
circle: for `σ` bounded away from `1/2`,

`2π ∑_ρ m_ρ (re ρ − σ) ≤ C T₂`,

and, by the layer-cake identity `integral_rectZeroCount_eq_finsum`, the number of zeroes of `ζ`
in `[σ, 3] × [T₁, T₂]` is `O(T₂)` for every fixed `σ > 1/2` — the Bohr–Landau density estimate,
here obtained along the classical Littlewood route.

Both statements keep the hypothesis that `ζ` does not vanish on the border of the rectangle; it
is what makes Littlewood's lemma applicable, and it holds for all but countably many choices of
the three parameters.

## Main results

* `exists_zeta_littlewood_bound_total` — `2π ∑_ρ m_ρ (re ρ − σ) ≤ C T₂`, with *no* unbounded
  term left on the right-hand side.
* `exists_rectZeroCount_riemannZeta_le` — the zero-density consequence:
  `N(σ; T₁, T₂) ≤ C T₂` for `1/2 < σ₀ < σ < 1`.
-/

noncomputable section

open Complex Real MeasureTheory Set Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

/-- **Littlewood's lemma for `ζ`, with every term bounded.**  For `σ₀ > 1/2` there is a constant
`C` such that, for every `σ ∈ [σ₀, 1)` and every rectangle `[σ, 3] × [T₁, T₂]` with `T₁ ≥ 6` on
whose border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − σ) ≤ C T₂`.

The horizontal argument terms left open by `exists_zeta_littlewood_bound` are bounded here by
Backlund's estimate `exists_abs_im_HIntegral_logDeriv_riemannZeta_le`. -/
theorem exists_zeta_littlewood_bound_total {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → ∀ T₁ T₂ : ℝ, 6 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I), riemannZeta s ≠ 0) →
      2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ) ≤ C * T₂ := by
  obtain ⟨C₁, hC₁, hbound⟩ := exists_zeta_littlewood_bound h0 h1
  obtain ⟨C₂, hC₂, harg⟩ := exists_abs_im_HIntegral_logDeriv_riemannZeta_le
  refine ⟨C₁ + 5 * C₂, by positivity, fun σ hσ hσ1 T₁ T₂ hT1 hT hborder => ?_⟩
  have hT2 : (6 : ℝ) ≤ T₂ := le_trans hT1 hT
  have hσ0 : 1 / 2 < σ := lt_of_lt_of_le h0 hσ
  have hσ3 : σ ≤ 3 := by linarith
  have hmain := hbound σ hσ hσ1 T₁ T₂ (by linarith) hT hborder
  -- the two horizontal terms
  have hz : ((σ : ℂ) + T₁ * I).re = σ := by simp
  have hzim : ((σ : ℂ) + T₁ * I).im = T₁ := by simp
  have hwre : (((3 : ℝ) : ℂ) + T₂ * I).re = 3 := by simp
  have hwim : (((3 : ℝ) : ℂ) + T₂ * I).im = T₂ := by simp
  have hseg : ∀ T : ℝ, (∀ x ∈ [[σ, (3 : ℝ)]], riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      6 ≤ T → |∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T).im|
        ≤ C₂ * Real.log T * |3 - σ| := by
    intro T hTne hTge
    have hkey : ‖∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T).im‖
        ≤ C₂ * Real.log T * |3 - σ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro u hu
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hσ3] at hu
      have hu1 : 1 / 2 ≤ u := by linarith [hu.1]
      have hsub : [[u, (3 : ℝ)]] ⊆ [[σ, (3 : ℝ)]] := by
        rw [uIcc_of_le hu.2, uIcc_of_le hσ3]
        exact Icc_subset_Icc (le_of_lt hu.1) le_rfl
      exact harg T hTge u hu1 hu.2 fun x hx => hTne x (hsub hx)
    rwa [Real.norm_eq_abs] at hkey
  have hne1 : ∀ x ∈ [[σ, (3 : ℝ)]], riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    have := hborder _ (mem_rectangleBorder_bottom (z := (σ : ℂ) + T₁ * I)
      (w := ((3 : ℝ) : ℂ) + T₂ * I) (by rw [hz, hwre]; exact hx))
    rwa [hzim] at this
  have hne2 : ∀ x ∈ [[σ, (3 : ℝ)]], riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    have := hborder _ (mem_rectangleBorder_top (z := (σ : ℂ) + T₁ * I)
      (w := ((3 : ℝ) : ℂ) + T₂ * I) (by rw [hz, hwre]; exact hx))
    rwa [hwim] at this
  have hb1 := hseg T₁ hne1 hT1
  have hb2 := hseg T₂ hne2 hT2
  -- `log T ≤ T` and `|3 - σ| ≤ 5/2`
  have hwidth : |3 - σ| ≤ 5 / 2 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hlog1 : Real.log T₁ ≤ T₁ := Real.log_le_self (by linarith)
  have hlog2 : Real.log T₂ ≤ T₂ := Real.log_le_self (by linarith)
  have hlog1' : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith)
  have hlog2' : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hle1 : |∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₁).im|
      ≤ 5 / 2 * C₂ * T₂ := by
    calc |∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₁).im|
        ≤ C₂ * Real.log T₁ * |3 - σ| := hb1
      _ ≤ C₂ * T₂ * (5 / 2) :=
          mul_le_mul (by nlinarith) hwidth (abs_nonneg _) (by positivity)
      _ = 5 / 2 * C₂ * T₂ := by ring
  have hle2 : |∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₂).im|
      ≤ 5 / 2 * C₂ * T₂ := by
    calc |∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₂).im|
        ≤ C₂ * Real.log T₂ * |3 - σ| := hb2
      _ ≤ C₂ * T₂ * (5 / 2) :=
          mul_le_mul (by nlinarith) hwidth (abs_nonneg _) (by positivity)
      _ = 5 / 2 * C₂ * T₂ := by ring
  have habs1 := abs_le.1 hle1
  have habs2 := abs_le.1 hle2
  nlinarith [hmain, habs1.1, habs1.2, habs2.1, habs2.2]

/-- **The Bohr–Landau density bound along the Littlewood route.**  For `1/2 < σ₀ < σ < 1` there
is a constant `C` such that the number of zeroes of `ζ`, with multiplicity, in the rectangle
`[σ, 3] × [T₁, T₂]` is at most `C T₂`, whenever `T₁ ≥ 6` and `ζ` does not vanish on the border of
the wider rectangle `[σ₀, 3] × [T₁, T₂]`. -/
theorem exists_rectZeroCount_riemannZeta_le {σ₀ σ : ℝ} (h0 : 1 / 2 < σ₀) (hσ : σ₀ < σ)
    (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₁ T₂ : ℝ, 6 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ₀ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I), riemannZeta s ≠ 0) →
      (rectZeroCount riemannZeta ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I) : ℝ) ≤ C * T₂ := by
  obtain ⟨C, hC, hbound⟩ := exists_zeta_littlewood_bound_total h0 (by linarith : σ₀ < 1)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hσ₀ : 0 < σ - σ₀ := by linarith
  refine ⟨C / (2 * Real.pi * (σ - σ₀)), div_pos hC (mul_pos (by positivity) hσ₀),
    fun T₁ T₂ hT1 hT hborder => ?_⟩
  set z : ℂ := (σ₀ : ℂ) + T₁ * I with hzdef
  set w : ℂ := ((3 : ℝ) : ℂ) + T₂ * I with hwdef
  have hzre : z.re = σ₀ := by rw [hzdef]; simp
  have hzim : z.im = T₁ := by rw [hzdef]; simp
  have hwre : w.re = 3 := by rw [hwdef]; simp
  have hσ3 : σ₀ ≤ 3 := by linarith
  -- the zeroes in the rectangle form a finite set
  have hcorner : w ∈ Rectangle z w := by
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [hzre, hwre]; exact right_mem_uIcc
    · exact right_mem_uIcc
  have hwzeta : riemannZeta w ≠ 0 := by
    intro hzero
    have h := half_le_norm_riemannZeta_of_three_le_re (s := w) (by rw [hwre])
    rw [hzero] at h
    simp at h
    linarith
  have hanal : AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
    refine analyticOnNhd_riemannZeta_rectangle_of_im_pos (z := z) (w := w) ?_ ?_
    · rw [hzim]; linarith
    · rw [hzim, hwdef]; simp; linarith
  have hfin : (rectZeros riemannZeta z w).Finite := rectZeros_finite hanal hcorner hwzeta
  -- the layer-cake identity
  have hlayer := integral_rectZeroCount_eq_finsum (f := riemannZeta) (z := z) (w := w)
    (by rw [hzre, hwre]; linarith) hfin
  rw [hzre, hwre] at hlayer
  -- the counting function is antitone and nonnegative
  set N : ℝ → ℝ := fun a => (rectZeroCount riemannZeta (leftCorner a z) w : ℝ) with hN
  have hNnonneg : ∀ a, 0 ≤ N a := fun a => by positivity
  have hanti : AntitoneOn N (Icc σ₀ 3) := by
    intro a ha b hb hab
    have := rectZeroCount_leftCorner_antitone (f := riemannZeta) (z := z) (w := w)
      (by rw [hzre, hwre]; linarith) hfin (σ := a) (τ := b) (by rwa [hzre, hwre])
      (by rwa [hzre, hwre]) hab
    simp only [hN]
    exact_mod_cast this
  have hint1 : IntervalIntegrable N volume σ₀ σ := by
    refine AntitoneOn.intervalIntegrable (hanti.mono ?_)
    rw [uIcc_of_le (le_of_lt hσ)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hint2 : IntervalIntegrable N volume σ 3 := by
    refine AntitoneOn.intervalIntegrable (hanti.mono ?_)
    rw [uIcc_of_le (by linarith : σ ≤ (3 : ℝ))]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hsplit : (∫ a in σ₀..(3 : ℝ), N a) = (∫ a in σ₀..σ, N a) + ∫ a in σ..(3 : ℝ), N a :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hpos2 : 0 ≤ ∫ a in σ..(3 : ℝ), N a :=
    intervalIntegral.integral_nonneg (by linarith) fun a _ => hNnonneg a
  have hlow : (σ - σ₀) * N σ ≤ ∫ a in σ₀..σ, N a := by
    have hconst : (∫ _a in σ₀..σ, N σ) ≤ ∫ a in σ₀..σ, N a := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint1 ?_
      intro a ha
      exact hanti ⟨ha.1, by linarith [ha.2]⟩ ⟨by linarith [ha.1], by linarith⟩ ha.2
    simpa [mul_comm] using hconst
  -- assemble
  have hmain := hbound σ₀ le_rfl (by linarith) T₁ T₂ hT1 hT (by rw [← hzdef, ← hwdef]; exact
    hborder)
  rw [← hzdef, ← hwdef] at hmain
  rw [← hlayer] at hmain
  have hlc : leftCorner σ z = (σ : ℂ) + (T₁ : ℂ) * I := by
    apply Complex.ext <;> simp [hzim]
  have hNσ : N σ = (rectZeroCount riemannZeta ((σ : ℂ) + T₁ * I) (((3 : ℝ) : ℂ) + T₂ * I) : ℝ) := by
    simp only [hN, hlc, hwdef]
  have hfinal : 2 * Real.pi * ((σ - σ₀) * N σ) ≤ C * T₂ := by
    have h2 : 2 * Real.pi * (∫ a in σ₀..(3 : ℝ), N a) ≤ C * T₂ := hmain
    nlinarith [hlow, hpos2, hsplit]
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by positivity : (0:ℝ) < 2 * Real.pi) hσ₀)]
  rw [← hNσ]
  nlinarith [hfinal]

end RiemannHypothesis
