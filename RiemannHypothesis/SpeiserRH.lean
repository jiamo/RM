/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SpeiserEquivalence

/-!
# The easy half of Speiser's theorem, quantitatively

Speiser's theorem says that the Riemann hypothesis is equivalent to `ξ′` having no zero with
`re s < 1/2`.  Its *hard* half — from `ξ′` back to `ζ` — needs the argument principle for `ξ′/ξ`
and is not available here; it is what the unproved `RiemannHypothesis.SpeiserOffLineTransfer`
would supply.

Its *easy* half, on the other hand, is within reach of the material already proved: Rolle's
theorem on the critical line, in the counting form
`RiemannHypothesis.windowCountOnLineMult_le_xiDerivWindowCountOnLineMult`, together with the
Riemann–von Mangoldt comparison of the counting functions of `ζ` and of `ξ′`.
If every nontrivial zero of `ζ` lies on the critical line then, in a dyadic window, `ξ′` has at
least `N(T,2T) − 1` zeroes on the line, while it has only `N(T,2T) + O(log T)` zeroes in total;
so it has at most `O(log T)` zeroes off the line:

* `xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm` — the hypothesis implies that `ξ′` has
  `O(log T)` zeroes off the critical line in each dyadic window, counted with multiplicity.

This is weaker than Speiser's conclusion (which is that there are *none*, and in the whole left
half of the strip), the loss being exactly the `O(log T)` error term of the two Riemann–von
Mangoldt formulas; but it is unconditional apart from the hypothesis itself, and it is real
analysis only.  Its contrapositive, `not_zetaStripForm_of_xiDeriv_offLine_gt`, is a criterion for
*disproving* the hypothesis: enough off-line zeroes of `ξ′` in a single dyadic window would do it.

Along the way, `speiserOffLineTransfer_of_zetaStripForm` records that the hypothesis of the
conditional route of `RiemannHypothesis.EightyPercentRoute` is itself implied by the Riemann
hypothesis — trivially, since then `ζ` has no off-line zeroes at all.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## Under the hypothesis, `ζ` has no off-line zeroes -/

/-- Under `ZetaStripForm` the window has no off-line zeroes at all. -/
lemma windowZerosOffLine_eq_empty_of_zetaStripForm (h : ZetaStripForm) (T₁ T₂ : ℝ) :
    windowZerosOffLine T₁ T₂ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => ?_
  obtain ⟨⟨⟨hz, h0, h1⟩, -⟩, hne⟩ := hρ
  exact hne (h ρ h0 h1 hz)

/-- Under `ZetaStripForm` the off-line count, with multiplicity, vanishes. -/
lemma windowCountOffLineMult_eq_zero_of_zetaStripForm (h : ZetaStripForm) (T₁ T₂ : ℝ) :
    windowCountOffLineMult T₁ T₂ = 0 := by
  rw [windowCountOffLineMult, windowZerosOffLine_eq_empty_of_zetaStripForm h T₁ T₂]
  simp

/-- Under `ZetaStripForm` every zero of the window is on the critical line, so the on-line count
with multiplicity is the whole count. -/
lemma windowCountOnLineMult_eq_of_zetaStripForm (h : ZetaStripForm) (T₁ T₂ : ℝ) :
    windowCountOnLineMult T₁ T₂ = windowCount T₁ T₂ := by
  have := windowCountOffLineMult_add_windowCountOnLineMult T₁ T₂
  rw [windowCountOffLineMult_eq_zero_of_zetaStripForm h T₁ T₂] at this
  omega

/-- **The Riemann hypothesis implies the transfer hypothesis of the conditional route.**  Under
`ZetaStripForm` the left-hand side of `SpeiserOffLineTransfer` is `0`, so the inequality is
trivial.  Together with `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` this
places `SpeiserOffLineTransfer` strictly between the two: implied by the hypothesis, and itself
implying `86.864 %` of the zeroes on the critical line. -/
theorem speiserOffLineTransfer_of_zetaStripForm (h : ZetaStripForm) : SpeiserOffLineTransfer := by
  refine ⟨0, 0, fun T _ => ?_⟩
  rw [windowCountOffLineMult_eq_zero_of_zetaStripForm h T (2 * T)]
  simp

/-! ## The quantitative easy half of Speiser's theorem -/

/-- **The easy half of Speiser's theorem, quantitatively.**  If every nontrivial zero of `ζ` lies
on the critical line, then in each dyadic window `ξ′` has at most `O(log T)` zeroes off the
critical line, counted with multiplicity.

Speiser's theorem asserts the stronger conclusion that `ξ′` has no zero at all with `re s < 1/2`;
the `O(log T)` here is exactly the error term of the two Riemann–von Mangoldt formulas, and the
proof uses nothing beyond Rolle's theorem for Hardy's `Ξ` on the critical line. -/
theorem xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm (h : ZetaStripForm) :
    ∃ C S : ℝ, ∀ T ≥ S,
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤ C * Real.log T := by
  obtain ⟨C, S, hCS⟩ := xiDerivWindowCountOffLineMult_le_windowCountOffLineMult
  refine ⟨C, S, fun T hT => ?_⟩
  have h1 := hCS T hT
  rwa [windowCountOffLineMult_eq_zero_of_zetaStripForm h T (2 * T), Nat.cast_zero,
    zero_add] at h1

/-- **A criterion for disproving the hypothesis**: the contrapositive of the previous theorem.
If, for every constant `C` and every threshold `S`, some dyadic window beyond `S` contains more
than `C · log T` zeroes of `ξ′` off the critical line, then `ZetaStripForm` fails. -/
theorem not_zetaStripForm_of_xiDeriv_offLine_gt
    (h : ∀ C S : ℝ, ∃ T ≥ S,
      C * Real.log T < (xiDerivWindowCountOffLineMult T (2 * T) : ℝ)) :
    ¬ ZetaStripForm := by
  intro hRH
  obtain ⟨C, S, hCS⟩ := xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm hRH
  obtain ⟨T, hTS, hT⟩ := h C S
  exact absurd (hCS T hTS) (not_le.2 hT)

end RiemannHypothesis

end
