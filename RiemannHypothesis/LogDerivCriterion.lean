/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Criteria
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The logarithmic-derivative form of the Riemann hypothesis

This file adds one more reformulation of the Riemann hypothesis, of a rather different
character from those in `RiemannHypothesis.Criteria`: the hypothesis is equivalent to the
existence of a *holomorphic logarithmic derivative* of `ζ` on the half-plane `re s > 1/2`.

To keep the underlying region **convex** (which makes the identity theorem and the order
theory much easier to apply) we phrase the statement for the entire function

`P(s) = (s - 1) ζ(s)`   (`zetaPoleFree`),

whose zeros in `re s > 1/2` are exactly the zeros of `ζ` there (note `P(1) = 1 ≠ 0`).  Thus

`ZetaLogDerivForm : ∃ g holomorphic on re s > 1/2 with P' = g · P`

and `zeta_iff_logDeriv : ZetaForm ↔ ZetaLogDerivForm`.

## The rigidity lemma

The substance of the reverse implication is the elementary but useful statement
`ne_zero_of_deriv_eq_mul`: if `f` is analytic at `p`, has finite order there, and satisfies
the linear differential equation `f' = S · f` near `p` with `S` analytic at `p`, then
`f(p) ≠ 0`.  Indeed if `f` vanished to order `n + 1` then `f'` would vanish to order exactly
`n`, whereas `S · f` vanishes to order at least `n + 1`.

This lemma is exactly what is needed to convert "`ζ'/ζ` continues holomorphically" into
"`ζ` does not vanish", and it is reused in `RiemannHypothesis.ChebyshevCriterion`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannHypothesis

/-! ## A rigidity lemma for the equation `f' = S · f` -/

/-- **Rigidity for `f' = S f`.**  An analytic function of finite order at `p` which satisfies
a linear homogeneous differential equation `f' = S · f` near `p`, with analytic coefficient
`S`, cannot vanish at `p`. -/
lemma ne_zero_of_deriv_eq_mul {f S : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hS : AnalyticAt ℂ S p) (hfin : analyticOrderAt f p ≠ ⊤)
    (heq : ∀ᶠ z in nhds p, deriv f z = S z * f z) : f p ≠ 0 := by
  intro h0
  have hne0 : analyticOrderAt f p ≠ 0 := hf.analyticOrderAt_ne_zero.mpr h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := by
    cases m with
    | zero => exact absurd hm.symm hne0
    | succ n => exact ⟨n, rfl⟩
  have hord : analyticOrderAt f p = (n : ℕ∞) + 1 := by rw [← hm]; push_cast; ring
  have hd : analyticOrderAt (deriv f) p = (n : ℕ∞) := by
    have h1 := hf.analyticOrderAt_deriv_add_one (x := p)
    rw [show (fun z => f z - f p) = f from funext fun z => by rw [h0, sub_zero], hord] at h1
    exact WithTop.add_right_cancel (by exact ENat.one_ne_top) h1
  have hcong : analyticOrderAt (deriv f) p = analyticOrderAt (S * f) p :=
    analyticOrderAt_congr (by filter_upwards [heq] with z hz using hz)
  have hmul : analyticOrderAt (S * f) p = analyticOrderAt S p + analyticOrderAt f p :=
    analyticOrderAt_mul hS hf
  rw [hcong, hmul, hord] at hd
  have hle : ((n : ℕ∞) + 1) ≤ analyticOrderAt S p + ((n : ℕ∞) + 1) := le_add_self
  have hle2 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by push_cast; exact hle.trans_eq hd
  exact absurd (Nat.cast_le.mp hle2) (by omega)

/-! ## `zetaPoleFree` is entire of finite order everywhere -/

lemma analyticOnNhd_zetaPoleFree : AnalyticOnNhd ℂ zetaPoleFree Set.univ :=
  differentiable_zetaPoleFree.differentiableOn.analyticOnNhd isOpen_univ

lemma analyticAt_zetaPoleFree (p : ℂ) : AnalyticAt ℂ zetaPoleFree p :=
  analyticOnNhd_zetaPoleFree p (Set.mem_univ p)

lemma zetaPoleFree_two_ne_zero : zetaPoleFree 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  rw [zetaPoleFree_of_ne_one h2]
  have hz : riemannZeta 2 ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
  exact mul_ne_zero (by norm_num) hz

/-- `(s - 1) ζ(s)` is entire and not identically zero, so it has finite vanishing order at
every point. -/
lemma analyticOrderAt_zetaPoleFree_ne_top (p : ℂ) : analyticOrderAt zetaPoleFree p ≠ ⊤ := by
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected analyticOnNhd_zetaPoleFree
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ p) ?_
  rw [(analyticAt_zetaPoleFree 2).analyticOrderAt_eq_zero.mpr zetaPoleFree_two_ne_zero]
  exact ENat.zero_ne_top

/-- If `zetaPoleFree` does not vanish on the half-plane `re s > 1/2`, neither does `ζ` away
from its pole; and conversely. -/
lemma riemannZeta_ne_zero_iff_zetaPoleFree_ne_zero {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s ≠ 0 ↔ zetaPoleFree s ≠ 0 := by
  rw [zetaPoleFree_of_ne_one hs]
  constructor
  · exact fun h => mul_ne_zero (sub_ne_zero_of_ne hs) h
  · intro h hz
    exact h (by rw [hz, mul_zero])

/-! ## The criterion -/

/-- **The logarithmic-derivative form of the Riemann hypothesis**: the entire function
`P(s) = (s-1)ζ(s)` has a holomorphic logarithmic derivative on the half-plane `re s > 1/2`,
i.e. there is a holomorphic `g` there with `P' = g · P`. -/
def ZetaLogDerivForm : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 / 2 < s.re → deriv zetaPoleFree s = g s * zetaPoleFree s

theorem zeta_strip_iff_logDeriv : ZetaStripForm ↔ ZetaLogDerivForm := by
  constructor
  · intro h
    have hne : ZetaNonvanishingRightForm := zeta_strip_iff_nonvanishing_right.mp h
    have hP : ∀ s : ℂ, 1 / 2 < s.re → zetaPoleFree s ≠ 0 := by
      intro s hs
      rcases eq_or_ne s 1 with rfl | hs1
      · simp [zetaPoleFree]
      · exact (riemannZeta_ne_zero_iff_zetaPoleFree_ne_zero hs1).mp (hne s hs hs1)
    have hderiv : Differentiable ℂ (deriv zetaPoleFree) := by
      intro z
      exact (analyticOnNhd_zetaPoleFree.deriv z (Set.mem_univ z)).differentiableAt
    refine ⟨fun s => deriv zetaPoleFree s / zetaPoleFree s, ?_, ?_⟩
    · intro s hs
      exact ((hderiv s).differentiableWithinAt).div
        (differentiable_zetaPoleFree s).differentiableWithinAt (hP s hs)
    · intro s hs
      rw [div_mul_cancel₀ _ (hP s hs)]
  · rintro ⟨g, hg, hgeq⟩
    refine zeta_strip_iff_nonvanishing_right.mpr ?_
    intro s hs hs1
    refine (riemannZeta_ne_zero_iff_zetaPoleFree_ne_zero hs1).mpr ?_
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 / 2 < z.re} ∈ nhds s := hopen.mem_nhds hs
    have hgA : AnalyticAt ℂ g s :=
      ((hg.analyticOnNhd hopen) s hs)
    refine ne_zero_of_deriv_eq_mul (analyticAt_zetaPoleFree s) hgA
      (analyticOrderAt_zetaPoleFree_ne_top s) ?_
    filter_upwards [hmem] with z hz using hgeq z hz

/-- **The Riemann hypothesis is equivalent to the existence of a holomorphic logarithmic
derivative of `(s-1)ζ(s)` on `re s > 1/2`.** -/
theorem zeta_iff_logDeriv : ZetaForm ↔ ZetaLogDerivForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_logDeriv

end RiemannHypothesis

end
