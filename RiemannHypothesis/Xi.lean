/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Main
import RiemannHypothesis.Symmetry
import RiemannHypothesis.DeBruijnNewman

/-!
# The Riemann `Ξ` function, and the hypothesis as a reality statement

This file defines the Riemann `Ξ` function

`Ξ(z) = ½ s(s − 1) Λ(s)`,  `s = ½ + i z`,  `Λ(s) = π^{−s/2} Γ(s/2) ζ(s)`,

and proves that the Riemann hypothesis is equivalent to the statement that **every zero of
`Ξ` is real**.

`Λ` has simple poles at `s = 0` and `s = 1`, which the factor `s(s − 1)` removes; in Lean the
cleanest way to say this is to use Mathlib's entire function `Λ₀` with
`Λ(s) = Λ₀(s) − 1/s − 1/(1 − s)`, so that

`s(s − 1) Λ(s) = s(s − 1) Λ₀(s) + 1`

as an identity of entire functions.  `riemannXi` is *defined* by the right-hand side, so it is
manifestly entire (`differentiable_riemannXi`), and it agrees with `½ s(s−1)Λ(s)` away from
`s ∈ {0, 1}` (`riemannXi_eq_completed`).

## Main results

* `differentiable_riemannXi` : `Ξ` is entire.
* `riemannXi_eq_completed` : `Ξ(z) = ½ s(s−1) Λ(s)` for `s = ½ + iz ∉ {0, 1}`.
* `completedRiemannZeta_ne_zero_of_re_nonpos`, `completedRiemannZeta_ne_zero_of_one_le_re` :
  `Λ` has no zeroes outside the open critical strip.
* `riemannXi_eq_zero_iff` : `Ξ(z) = 0` if and only if `s = ½ + iz` lies in the open critical
  strip and is a zero of `ζ`.
* `XiForm` : the statement "every zero of `Ξ` is real".
* `zeta_strip_iff_xi`, `zeta_iff_xi` : the Riemann hypothesis is equivalent to `XiForm`.

The `Ξ` function is also the object at the origin of the de Bruijn–Newman family of
`RiemannHypothesis.DeBruijnNewman`; the identification of `H₀` with `Ξ` is *not* proved in this
repository.
-/

noncomputable section

open Complex

namespace RiemannHypothesis

/-- The point `s = ½ + i z` of the `s`-plane corresponding to the `Ξ`-variable `z`.  The
critical line `re s = ½` is the image of the real axis. -/
def xiPoint (z : ℂ) : ℂ := 1 / 2 + z * I

/-- **The Riemann `Ξ` function**, `Ξ(z) = ½ s(s − 1) Λ(s)` with `s = ½ + i z`, written in the
manifestly entire form `Ξ(z) = ½ (s(s − 1) Λ₀(s) + 1)`. -/
def riemannXi (z : ℂ) : ℂ :=
  (xiPoint z * (xiPoint z - 1) * completedRiemannZeta₀ (xiPoint z) + 1) / 2

/-- The Riemann hypothesis as a reality statement: every zero of `Ξ` is real. -/
def XiForm : Prop :=
  ∀ z : ℂ, riemannXi z = 0 → z.im = 0

@[simp] lemma xiPoint_re (z : ℂ) : (xiPoint z).re = 1 / 2 - z.im := by
  simp [xiPoint]
  ring

@[simp] lemma xiPoint_im (z : ℂ) : (xiPoint z).im = z.re := by
  simp [xiPoint]

/-- The inverse of `z ↦ ½ + i z`. -/
lemma xiPoint_neg_I_mul_sub (s : ℂ) : xiPoint (-I * (s - 1 / 2)) = s := by
  have hI : (-I * (s - 1 / 2)) * I = s - 1 / 2 := by
    have : I * I = -1 := Complex.I_mul_I
    linear_combination (1 / 2 - s) * this
  simp only [xiPoint, hI]
  ring

lemma differentiable_xiPoint : Differentiable ℂ xiPoint := by
  unfold xiPoint
  fun_prop

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact ((((differentiable_xiPoint.mul (differentiable_xiPoint.sub_const 1)).mul
    (differentiable_completedZeta₀.comp differentiable_xiPoint)).add_const 1).div_const 2)

/-- Away from the two poles of `Λ`, the definition agrees with `½ s(s − 1) Λ(s)`. -/
theorem riemannXi_eq_completed {z : ℂ} (h0 : xiPoint z ≠ 0) (h1 : xiPoint z ≠ 1) :
    riemannXi z = xiPoint z * (xiPoint z - 1) / 2 * completedRiemannZeta (xiPoint z) := by
  set s := xiPoint z with hs
  have h1' : (1 : ℂ) - s ≠ 0 := fun h => h1 (by linear_combination -h)
  rw [riemannXi, ← hs, completedRiemannZeta_eq s]
  field_simp
  ring

/-- `Λ(s) = Γ_ℝ(s) ζ(s)` on the right half-plane. -/
theorem completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

/-- `Λ` does not vanish on `re s ≥ 1`. -/
theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [completedRiemannZeta_eq_Gammaℝ_mul (by linarith)]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_le_re hs)

/-- `Λ` does not vanish on `re s ≤ 0`; this is the functional equation together with the
previous lemma. -/
theorem completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  have h := completedRiemannZeta_ne_zero_of_one_le_re (s := 1 - s) (by simp; linarith)
  rwa [completedRiemannZeta_one_sub] at h

/-- `xiPoint (-z) = 1 - xiPoint z`: the functional-equation involution `s ↦ 1 - s` is
`z ↦ -z` in the `Ξ`-variable. -/
lemma xiPoint_neg (z : ℂ) : xiPoint (-z) = 1 - xiPoint z := by
  simp only [xiPoint]
  ring

/-- **The functional equation for `Ξ`**: `Ξ` is an even function.  This is `Λ(1 - s) = Λ(s)`
transported by `s = ½ + i z`. -/
theorem riemannXi_neg (z : ℂ) : riemannXi (-z) = riemannXi z := by
  rw [riemannXi, riemannXi, xiPoint_neg, completedRiemannZeta₀_one_sub]
  ring

/-- `Γ_ℝ` commutes with complex conjugation. -/
lemma Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have harg : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact fun h => absurd h.symm Real.pi_ne_zero
  have hc2 : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  have h1 : (Real.pi : ℂ) ^ (-(starRingEnd ℂ) s / 2)
      = (starRingEnd ℂ) ((Real.pi : ℂ) ^ (-s / 2)) := by
    have h := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) harg
    rw [Complex.conj_ofReal] at h
    rw [← h, map_div₀, map_neg, hc2]
  rw [h1, map_div₀, hc2]

/-- Inside the critical strip, `Λ` commutes with complex conjugation.  The zeta part is the
repository's `riemannZeta_conj_of_mem_strip`. -/
lemma completedRiemannZeta_conj_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  have hre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  rw [completedRiemannZeta_eq_Gammaℝ_mul (by rw [hre]; exact hs0),
    completedRiemannZeta_eq_Gammaℝ_mul hs0, Gammaℝ_conj,
    riemannZeta_conj_of_mem_strip hs0 hs1, map_mul]

/-- Inside the critical strip, `Λ₀` commutes with complex conjugation. -/
lemma completedRiemannZeta₀_conj_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs0
  have hs' : (1 : ℂ) - s ≠ 0 := fun h => by
    have : s = 1 := by linear_combination -h
    rw [this] at hs1
    norm_num at hs1
  have hΛ := completedRiemannZeta_conj_of_mem_strip hs0 hs1
  have e1 : completedRiemannZeta₀ ((starRingEnd ℂ) s)
      = completedRiemannZeta ((starRingEnd ℂ) s) + 1 / (starRingEnd ℂ) s
        + 1 / (1 - (starRingEnd ℂ) s) := by
    rw [completedRiemannZeta_eq ((starRingEnd ℂ) s)]
    ring
  have e2 : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [completedRiemannZeta_eq s]
    ring
  rw [e1, e2, hΛ, map_add, map_add, map_div₀, map_div₀]
  simp [map_sub]

/-- **`Ξ` is real on the real axis.**  For real `x`, `s = ½ + i x` satisfies
`conj s = 1 - s`, so the conjugation symmetry of `Λ₀` in the strip and its functional
equation combine to make `Λ₀(s)` real; the factor `s(s-1) = -(x² + ¼)` is real too. -/
theorem riemannXi_ofReal_im (x : ℝ) : (riemannXi (x : ℂ)).im = 0 := by
  set s := xiPoint (x : ℂ) with hsdef
  have hs : s = 1 / 2 + (x : ℂ) * I := rfl
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    rw [hs]
    simp [Complex.ext_iff]
    ring
  have hre : s.re = 1 / 2 := by simp [hs]
  have hΛ₀ : (starRingEnd ℂ) (completedRiemannZeta₀ s) = completedRiemannZeta₀ s := by
    have h := completedRiemannZeta₀_conj_of_mem_strip (s := s) (by rw [hre]; norm_num)
      (by rw [hre]; norm_num)
    rw [hconj, completedRiemannZeta₀_one_sub] at h
    exact h.symm
  have hprod : (starRingEnd ℂ) (s * (s - 1)) = s * (s - 1) := by
    rw [map_mul, map_sub, map_one, hconj]
    ring
  refine Complex.conj_eq_iff_im.mp ?_
  have hc2 : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl
  rw [riemannXi, ← hsdef, map_div₀, map_add, map_one, map_mul, hprod, hΛ₀, hc2]

/-- The zeroes of `Ξ` are exactly the zeroes of `ζ` inside the critical strip. -/
theorem riemannXi_eq_zero_iff {z : ℂ} :
    riemannXi z = 0 ↔
      0 < (xiPoint z).re ∧ (xiPoint z).re < 1 ∧ riemannZeta (xiPoint z) = 0 := by
  constructor
  · intro hz
    -- the two poles are not zeroes of `Ξ`
    have hs0 : xiPoint z ≠ 0 := by
      intro h
      rw [riemannXi, h] at hz
      norm_num at hz
    have hs1 : xiPoint z ≠ 1 := by
      intro h
      rw [riemannXi, h] at hz
      norm_num at hz
    have hΛ : completedRiemannZeta (xiPoint z) = 0 := by
      rw [riemannXi_eq_completed hs0 hs1] at hz
      rcases mul_eq_zero.mp hz with h | h
      · exfalso
        have h' : xiPoint z * (xiPoint z - 1) = 0 := by
          field_simp at h
          linear_combination h
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact hs0 h''
        · exact hs1 (by linear_combination h'')
      · exact h
    have hlt : (xiPoint z).re < 1 := by
      by_contra hc
      exact completedRiemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hΛ
    have hgt : 0 < (xiPoint z).re := by
      by_contra hc
      exact completedRiemannZeta_ne_zero_of_re_nonpos (not_lt.mp hc) hΛ
    refine ⟨hgt, hlt, ?_⟩
    rw [completedRiemannZeta_eq_Gammaℝ_mul hgt] at hΛ
    rcases mul_eq_zero.mp hΛ with h | h
    · exact absurd h (Gammaℝ_ne_zero_of_re_pos hgt)
    · exact h
  · rintro ⟨hgt, hlt, hzero⟩
    have hs0 : xiPoint z ≠ 0 := by
      intro h
      rw [h] at hgt
      simp at hgt
    have hs1 : xiPoint z ≠ 1 := by
      intro h
      rw [h] at hlt
      simp at hlt
    rw [riemannXi_eq_completed hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul hgt, hzero]
    ring

/-- **The Riemann hypothesis is the statement that every zero of `Ξ` is real.** -/
theorem zeta_strip_iff_xi : ZetaStripForm ↔ XiForm := by
  constructor
  · intro h z hz
    obtain ⟨hgt, hlt, hzero⟩ := riemannXi_eq_zero_iff.mp hz
    have := h (xiPoint z) hgt hlt hzero
    rw [xiPoint_re] at this
    linarith
  · intro h s hgt hlt hzero
    set z : ℂ := -I * (s - 1 / 2) with hzdef
    have hsz : xiPoint z = s := xiPoint_neg_I_mul_sub s
    have hxi : riemannXi z = 0 := by
      refine riemannXi_eq_zero_iff.mpr ⟨?_, ?_, ?_⟩ <;> rw [hsz] <;> assumption
    have him := h z hxi
    have : z.im = 1 / 2 - s.re := by
      simp [hzdef]
    rw [this] at him
    linarith

/-- The same, in the Mathlib formulation of the hypothesis. -/
theorem zeta_iff_xi : ZetaForm ↔ XiForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_xi

/-- **The bridge to the de Bruijn–Newman family, stated conditionally.**  The Riemann
hypothesis is exactly the assertion that all the zeroes of `H₀` are real, which is the `t = 0`
case of the definition of the de Bruijn–Newman constant.

**Caveat on the hypothesis `h`.**  As stated, `h : ∀ z, H₀(z) = Ξ(z)` is *false*, so this
theorem — although correctly proved — is vacuous.  The correct normalisation, proved
unconditionally in `RiemannHypothesis/FourierXi.lean`, is
`RiemannHypothesis.dbnH_zero_eq_riemannXi : H₀(z) = Ξ(z/2)/8`; the weight `Φ` of
`DeBruijnNewman.lean` is `(W'' − W)/8` with `W(u) = e^u ω(e^{4u})`, and the cosine kernel
there is `cos(uz)` rather than `cos(2uz)`, which produces both the halving of the variable
and the factor `8`.  The statement below is kept for the record; the unconditional
replacement is `RiemannHypothesis.zeta_iff_dbnH_zero`. -/
theorem zeta_iff_dbnH_zero_of_eq (h : ∀ z : ℂ, dbnH 0 z = riemannXi z) :
    ZetaForm ↔ ∀ z : ℂ, dbnH 0 z = 0 → z.im = 0 := by
  rw [zeta_iff_xi]
  constructor
  · intro hx z hz
    exact hx z (by rw [← h z]; exact hz)
  · intro hx z hz
    exact hx z (by rw [h z]; exact hz)

end RiemannHypothesis

end
