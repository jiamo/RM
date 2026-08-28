/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SpeiserMultiple

/-!
# `ξ` on the critical line, and Rolle's theorem for `ξ′`

The completed zeta function `ξ` is *real* on the critical line: `Ξ(t) = ξ(1/2 + it)` takes real
values, because `ξ(s̄) = conj ξ(s)` and `ξ(1 − s) = ξ(s)`.  Hardy's function `Ξ` is therefore a
real-analytic function of a real variable whose zeroes are exactly the zeroes of `ζ` on the
critical line, and whose derivative vanishes exactly where `ξ′` vanishes on the critical line.

Rolle's theorem then applies: **between two zeroes of `ζ` on the critical line there is a zero
of `ξ′` on the critical line**.  This is the elementary, unconditional half of the relation
between the zeroes of `ζ` and the zeroes of `ξ′` on the line; the counting consequences are in
`RiemannHypothesis.SpeiserRolle`.

## Main definitions and results

* `onLine t = 1/2 + i t`, the parametrisation of the critical line;
* `XiReal t`, Hardy's `Ξ`, with `ofReal_XiReal : (Ξ t : ℂ) = ξ(1/2 + it)`;
* `hasDerivAt_XiReal` — `Ξ` is differentiable, with derivative `(ξ′(1/2+it)·i).re`;
* `xiDerivFn_onLine_eq_zero_of_deriv_eq_zero` — a critical point of `Ξ` is a zero of `ξ′`;
* `exists_xiDerivFn_onLine_eq_zero` — **Rolle on the critical line**.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## The critical line -/

/-- The point `1/2 + i t` of the critical line. -/
def onLine (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * I

@[simp] lemma onLine_re (t : ℝ) : (onLine t).re = 1 / 2 := by simp [onLine]

@[simp] lemma onLine_im (t : ℝ) : (onLine t).im = t := by simp [onLine]

lemma onLine_injective : Function.Injective onLine := by
  intro a b hab
  have := congrArg Complex.im hab
  simpa using this

/-- A point of the critical line is `onLine` of its ordinate. -/
lemma eq_onLine {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ = onLine ρ.im := by
  apply Complex.ext <;> simp [h]

lemma conj_onLine (t : ℝ) : (starRingEnd ℂ) (onLine t) = 1 - onLine t := by
  apply Complex.ext
  · simp [onLine]
    ring
  · simp [onLine]

/-! ## `ξ` is real on the critical line -/

lemma xiFn_conj (s : ℂ) : xiFn ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiFn s) := by
  rw [xiFn_eq_zeta23_xi]
  exact Zeta23.XiPrime.xi_conj s

/-- **`ξ` is real on the critical line.** -/
theorem xiFn_onLine_conj (t : ℝ) :
    (starRingEnd ℂ) (xiFn (onLine t)) = xiFn (onLine t) := by
  rw [← xiFn_conj, conj_onLine, xiFn_one_sub]

/-- **Hardy's function** `Ξ(t) = ξ(1/2 + it)`, as a real-valued function of a real variable. -/
def XiReal (t : ℝ) : ℝ := (xiFn (onLine t)).re

lemma xiFn_onLine_im (t : ℝ) : (xiFn (onLine t)).im = 0 := by
  have h := xiFn_onLine_conj t
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

@[simp] lemma ofReal_XiReal (t : ℝ) : ((XiReal t : ℝ) : ℂ) = xiFn (onLine t) := by
  apply Complex.ext
  · simp [XiReal]
  · simp [xiFn_onLine_im t]

lemma XiReal_eq_zero_iff (t : ℝ) : XiReal t = 0 ↔ xiFn (onLine t) = 0 := by
  constructor
  · intro h
    have := ofReal_XiReal t
    rw [h] at this
    simpa using this.symm
  · intro h
    have := ofReal_XiReal t
    rw [h] at this
    exact_mod_cast this

/-! ## The derivative of `Ξ` -/

lemma hasDerivAt_onLine (t : ℝ) : HasDerivAt onLine I t := by
  have h₀ : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h₁ : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) (1 * I) t :=
    (h₀.mul_const I).const_add _
  rw [one_mul] at h₁
  exact h₁

lemma hasDerivAt_xiFn_onLine (t : ℝ) :
    HasDerivAt (fun u : ℝ => xiFn (onLine u)) (xiDerivFn (onLine t) * I) t := by
  have h := (differentiable_xiFn (onLine t)).hasDerivAt.comp t (hasDerivAt_onLine t)
  rw [xiDerivFn]
  exact h

/-- `Ξ` is differentiable, with derivative the real part of `i·ξ′(1/2+it)`. -/
theorem hasDerivAt_XiReal (t : ℝ) :
    HasDerivAt XiReal ((xiDerivFn (onLine t) * I).re) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_xiFn_onLine t)

/-- The derivative of `Ξ` is the *whole* of `i·ξ′(1/2+it)`: the imaginary part vanishes. -/
lemma xiDerivFn_onLine_mul_I_im (t : ℝ) : (xiDerivFn (onLine t) * I).im = 0 := by
  have h' := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_xiFn_onLine t)
  have hconst : HasDerivAt (fun u : ℝ => (xiFn (onLine u)).im) 0 t := by
    have he : (fun u : ℝ => (xiFn (onLine u)).im) = fun _ : ℝ => (0 : ℝ) :=
      funext fun u => xiFn_onLine_im u
    rw [he]
    exact hasDerivAt_const t 0
  exact (hconst.unique h').symm

/-- **A critical point of `Ξ` is a zero of `ξ′`.** -/
theorem xiDerivFn_onLine_eq_zero_of_deriv_eq_zero {t : ℝ}
    (h : (xiDerivFn (onLine t) * I).re = 0) : xiDerivFn (onLine t) = 0 := by
  have him := xiDerivFn_onLine_mul_I_im t
  have hz : xiDerivFn (onLine t) * I = 0 := Complex.ext h him
  rcases mul_eq_zero.1 hz with h0 | h0
  · exact h0
  · exact absurd h0 Complex.I_ne_zero

/-! ## Rolle's theorem on the critical line -/

/-- **Rolle's theorem on the critical line.**  If `ξ` vanishes at two points `1/2 + ia` and
`1/2 + ib` of the critical line, then `ξ′` vanishes at a point of the critical line strictly
between them. -/
theorem exists_xiDerivFn_onLine_eq_zero {a b : ℝ} (hab : a < b)
    (ha : xiFn (onLine a) = 0) (hb : xiFn (onLine b) = 0) :
    ∃ c ∈ Ioo a b, xiDerivFn (onLine c) = 0 := by
  have hcont : ContinuousOn XiReal (Icc a b) := fun t _ =>
    ((hasDerivAt_XiReal t).continuousAt).continuousWithinAt
  have hfI : XiReal a = XiReal b := by
    rw [(XiReal_eq_zero_iff a).2 ha, (XiReal_eq_zero_iff b).2 hb]
  obtain ⟨c, hc, hc'⟩ :=
    exists_hasDerivAt_eq_zero hab hcont hfI (fun t _ => hasDerivAt_XiReal t)
  exact ⟨c, hc, xiDerivFn_onLine_eq_zero_of_deriv_eq_zero hc'⟩

end RiemannHypothesis

end
