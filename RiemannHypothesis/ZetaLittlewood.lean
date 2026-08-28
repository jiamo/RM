/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Littlewood
import RiemannHypothesis.ZetaRectangleCount

/-!
# Littlewood's lemma for `ζ`

`RiemannHypothesis.Littlewood` proves Littlewood's lemma for an arbitrary function of a complex
variable, and `RiemannHypothesis.ZetaRectangleCount` supplies the dictionary that discharges its
hypotheses for `ζ` on a rectangle inside the open critical strip: `ζ` is analytic there (the
rectangle avoids the pole at `s = 1`), and the zeroes it counts are exactly the nontrivial
zeroes of `ζ`.  This file combines the two.

## Main results

* `zeta_littlewood_lemma` — Littlewood's lemma for `ζ` on a rectangle inside the strip.
* `zeta_littlewood_lemma_arg` — the same with the two horizontal terms written as increments of
  genuine continuous arguments of `ζ` along the bottom and the top side.
* `zeta_littlewood_lemma_nontrivialZeros` — the sum on the left rewritten as a sum over the
  nontrivial zeroes of `ζ` lying in the rectangle.

Every statement is unconditional; the hypotheses are geometric (the rectangle lies in the open
strip, `ζ` does not vanish on its border).  Like the general lemma, these are identities and not
bounds: extracting a zero-density estimate needs upper and lower bounds for `log ‖ζ‖` on the two
vertical sides.
-/

noncomputable section

open Complex Set MeasureTheory Zeta23.Analytic

open scoped Interval

namespace RiemannHypothesis

variable {z w : ℂ}

/-- **Littlewood's lemma for `ζ`.**  For a rectangle inside the open critical strip on whose
border `ζ` does not vanish,

`2π ∑_ρ m_ρ (re ρ − z.re)`
  `= ∫ (log ‖ζ‖ on the left side − log ‖ζ‖ on the right side) dt`
  `+ ∫ (argument increment along the bottom side from σ to w.re) dσ`
  `− ∫ (argument increment along the top side from σ to w.re) dσ`
  `+ (w.re − z.re) · (argument increment along the right side)`,

the sum being over the nontrivial zeroes of `ζ` in the rectangle, with multiplicity. -/
theorem zeta_littlewood_lemma (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  littlewood_lemma hre him (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) hborder

/-- **Littlewood's lemma for `ζ`, with a genuine argument.**  The two horizontal terms are the
increments of continuous branches `θb`, `θt` of the argument of `ζ` along the bottom and the top
side; no branch cut is chosen, the branches are produced by integrating `ζ′/ζ`. -/
theorem zeta_littlewood_lemma_arg (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    ∃ θb θt : ℝ → ℝ, ContinuousOn θb [[z.re, w.re]] ∧ ContinuousOn θt [[z.re, w.re]] ∧
      (∀ σ ∈ [[z.re, w.re]], riemannZeta ((σ : ℂ) + z.im * I)
        = (‖riemannZeta ((σ : ℂ) + z.im * I)‖ : ℂ) * Complex.exp (θb σ * I)) ∧
      (∀ σ ∈ [[z.re, w.re]], riemannZeta ((σ : ℂ) + w.im * I)
        = (‖riemannZeta ((σ : ℂ) + w.im * I)‖ : ℂ) * Complex.exp (θt σ * I)) ∧
      2 * Real.pi * ∑ᶠ ρ ∈ rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
        = (∫ t in z.im..w.im,
              (Real.log ‖riemannZeta ((z.re : ℂ) + t * I)‖
                - Real.log ‖riemannZeta ((w.re : ℂ) + t * I)‖))
          + (∫ σ in z.re..w.re, (θb w.re - θb σ))
          - (∫ σ in z.re..w.re, (θt w.re - θt σ))
          + (w.re - z.re) * (VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  littlewood_lemma_arg hre him (analyticOnNhd_riemannZeta_rectangle hz0 hw1 hre) hborder

/-- The set summed over in `zeta_littlewood_lemma` is exactly the set of nontrivial zeroes of
`ζ` lying in the rectangle. -/
theorem rectZeros_riemannZeta_eq_inter (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    rectZeros riemannZeta z w = Rectangle z w ∩ nontrivialZeroSet := by
  rw [rectZeros_riemannZeta_eq_xiFn hz0 hw1 hre, rectZeros_xiFn_eq]

/-- **Littlewood's lemma for `ζ`**, with the sum written over the nontrivial zeroes of `ζ` in
the rectangle. -/
theorem zeta_littlewood_lemma_nontrivialZeros (hz0 : 0 < z.re) (hw1 : w.re < 1)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ Rectangle z w ∩ nontrivialZeroSet,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv riemannZeta) w.re z.im w.im).im := by
  rw [← rectZeros_riemannZeta_eq_inter hz0 hw1 hre]
  exact zeta_littlewood_lemma hz0 hw1 hre him hborder

end RiemannHypothesis
