/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AbelDirichlet
import RiemannHypothesis.LogDerivCriterion
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# The Chebyshev criterion: a square-root error term in the prime number theorem implies RH

This is a third, independent route to the Riemann hypothesis, complementing the
reformulations of `RiemannHypothesis.Criteria` and the Mertens criterion of
`RiemannHypothesis.MoebiusCriterion`.  Let

`ψ(N) = ∑_{n ≤ N} Λ(n)`   (`chebyshevPsi`)

be the second Chebyshev function.  If the prime number theorem holds with square-root error,

`ψ(N) - N = O(N^{1/2+ε})` for every `ε > 0`   (`ChebyshevBoundForm`),

then the Riemann hypothesis follows (`zeta_of_chebyshevBound`).

## The argument

The hypothesis says exactly that the arithmetic function `a(n) = Λ(n) - 1` has square-root
cancellation, so the machinery of `RiemannHypothesis.AbelDirichlet` makes its Dirichlet
series holomorphic on the half-plane `re s > 1/2`:

`G(s) = ∑_{n ≥ 1} (ψ(n) - n) (n^{-s} - (n+1)^{-s})`   (`chebyshevAbel`),

and for `re s > 1` it equals `-ζ'(s)/ζ(s) - ζ(s)`.

Writing `P(s) = (s-1) ζ(s)` for the entire function of `RiemannHypothesis.Criteria`, that
identity becomes, after clearing the pole,

`(s-1) P(s) G(s) + (s-1) P'(s) - P(s) + P(s)^2 = 0`,

an identity between functions holomorphic on the *convex* half-plane `re s > 1/2`, valid on
`re s > 1` and hence everywhere there.  Away from `s = 1` it can be solved for `P'`:

`P' = S · P`  with `S = (1 - P - (s-1) G)/(s-1)` holomorphic,

and the rigidity lemma `ne_zero_of_deriv_eq_mul` of `RiemannHypothesis.LogDerivCriterion`
forbids `P`, and hence `ζ`, from vanishing there.
-/

noncomputable section

open Complex Filter Finset ArithmeticFunction
open scoped Topology

namespace RiemannHypothesis

/-- The second Chebyshev function `ψ(N) = ∑_{n ≤ N} Λ(n)`. -/
def chebyshevPsi (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, Λ n

/-- **The Chebyshev bound**: `ψ(N) - N = O(N^{1/2+ε})` for every `ε > 0`, i.e. the prime
number theorem with square-root error term. -/
def ChebyshevBoundForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |chebyshevPsi N - N| ≤ C * (N : ℝ) ^ (1 / 2 + ε)

/-- The arithmetic function `Λ(n) - 1`, whose partial sums are `ψ(N) - N`. -/
def chebyshevC : ℕ → ℂ := (fun n : ℕ => (Λ n : ℂ)) - 1

/-- The Abel-summed Dirichlet series of `Λ(n) - 1`. -/
def chebyshevAbel (s : ℂ) : ℂ := abelSum chebyshevC s

lemma partialSum_chebyshevC (N : ℕ) :
    partialSum chebyshevC N = ((chebyshevPsi N : ℝ) : ℂ) - (N : ℂ) := by
  simp only [partialSum, chebyshevC, Pi.sub_apply, Pi.one_apply, Finset.sum_sub_distrib,
    chebyshevPsi]
  push_cast
  simp

lemma norm_partialSum_chebyshevC (N : ℕ) :
    ‖partialSum chebyshevC N‖ = |chebyshevPsi N - N| := by
  rw [partialSum_chebyshevC, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-- The Chebyshev bound is exactly square-root cancellation for `Λ(n) - 1`. -/
lemma sqrtCancellation_chebyshevC (hC : ChebyshevBoundForm) : SqrtCancellation chebyshevC := by
  intro ε hε
  obtain ⟨C, hCb⟩ := hC ε hε
  exact ⟨C, fun N => by rw [norm_partialSum_chebyshevC]; exact hCb N⟩

lemma differentiableOn_chebyshevAbel (hC : ChebyshevBoundForm) :
    DifferentiableOn ℂ chebyshevAbel {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_abelSum_of_sqrtCancellation (sqrtCancellation_chebyshevC hC)

/-- For `re s > 1` the Abel-summed series equals `-ζ'(s)/ζ(s) - ζ(s)`. -/
lemma chebyshevAbel_eq (hC : ChebyshevBoundForm) {s : ℂ} (hs : 1 < s.re) :
    chebyshevAbel s = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have hsum1 : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) s := LSeriesSummable_vonMangoldt hs
  have hsum2 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsub : LSeriesSummable chebyshevC s := LSeriesSummable.sub hsum1 hsum2
  have h := abelSum_eq_LSeries_of_sqrtCancellation
    (sqrtCancellation_chebyshevC hC) (by linarith) hsub
  have hL : LSeries chebyshevC s
      = LSeries (fun n : ℕ => (Λ n : ℂ)) s - LSeries (1 : ℕ → ℂ) s :=
    LSeries_sub hsum1 hsum2
  rw [chebyshevAbel, h, hL, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_one_eq_riemannZeta hs]

/-- The derivative of `P(s) = (s-1)ζ(s)` away from `s = 1`. -/
lemma deriv_zetaPoleFree_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv zetaPoleFree s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : zetaPoleFree =ᶠ[nhds s] fun w : ℂ => (w - 1) * riemannZeta w := by
    have hmem : {w : ℂ | w ≠ 1} ∈ nhds s := (isOpen_ne).mem_nhds hs
    filter_upwards [hmem] with w hw using zetaPoleFree_of_ne_one hw
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have h3 : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := h1.mul h2
  rw [h3.deriv]
  ring

/-! ## The criterion -/

/-- **The Chebyshev criterion**: if `ψ(N) - N = O(N^{1/2+ε})` for every `ε > 0`, then the
Riemann hypothesis holds. -/
theorem zeta_of_chebyshevBound (hC : ChebyshevBoundForm) : ZetaForm := by
  refine zeta_iff_zeta_strip.mpr (zeta_strip_iff_nonvanishing_right.mpr ?_)
  intro s hs hs1
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hderivP : Differentiable ℂ (deriv zetaPoleFree) := fun z =>
    (analyticOnNhd_zetaPoleFree.deriv z (Set.mem_univ z)).differentiableAt
  -- the master identity, first as an analytic function on the half-plane
  set A : ℂ → ℂ := fun z => (z - 1) * zetaPoleFree z * chebyshevAbel z
      + (z - 1) * deriv zetaPoleFree z - zetaPoleFree z + zetaPoleFree z ^ 2 with hA
  have hAan : AnalyticOnNhd ℂ A U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    have h1 : DifferentiableOn ℂ (fun z : ℂ => (z - 1) * zetaPoleFree z * chebyshevAbel z) U :=
      (((differentiable_id.sub_const 1).mul differentiable_zetaPoleFree).differentiableOn).mul
        (differentiableOn_chebyshevAbel hC)
    have h2 : DifferentiableOn ℂ (fun z : ℂ => (z - 1) * deriv zetaPoleFree z) U :=
      ((differentiable_id.sub_const 1).mul hderivP).differentiableOn
    exact ((h1.add h2).sub differentiable_zetaPoleFree.differentiableOn).add
      ((differentiable_zetaPoleFree.pow 2).differentiableOn)
  have hZan : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) U :=
    (differentiable_const 0).differentiableOn.analyticOnNhd hUopen
  have hmem2 : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : A =ᶠ[nhds (2 : ℂ)] fun _ : ℂ => (0 : ℂ) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    have hz1 : (1 : ℝ) < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      simp at hz1
    have hzeta : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hz1)
    have hG := chebyshevAbel_eq hC hz1
    rw [hA]
    simp only
    rw [zetaPoleFree_of_ne_one hzne, deriv_zetaPoleFree_of_ne_one hzne, hG]
    field_simp
    ring
  have hzero := hAan.eqOn_of_preconnected_of_eventuallyEq hZan hUconn hmem2 hev
  -- now solve for `P'` near `s` and apply the rigidity lemma
  have hsU : s ∈ U := hs
  refine (riemannZeta_ne_zero_iff_zetaPoleFree_ne_zero hs1).mpr ?_
  set S : ℂ → ℂ :=
    fun z => (1 - zetaPoleFree z - (z - 1) * chebyshevAbel z) / (z - 1) with hS
  have hSan : AnalyticAt ℂ S s := by
    have hnum : AnalyticAt ℂ (fun z : ℂ => 1 - zetaPoleFree z - (z - 1) * chebyshevAbel z) s := by
      have h1 : AnalyticAt ℂ zetaPoleFree s := analyticAt_zetaPoleFree s
      have h2 : AnalyticAt ℂ chebyshevAbel s :=
        ((differentiableOn_chebyshevAbel hC).analyticOnNhd hUopen) s hsU
      exact ((analyticAt_const).sub h1).sub (((analyticAt_id).sub analyticAt_const).mul h2)
    have hden : AnalyticAt ℂ (fun z : ℂ => z - 1) s := (analyticAt_id).sub analyticAt_const
    exact hnum.div hden (sub_ne_zero_of_ne hs1)
  refine ne_zero_of_deriv_eq_mul (analyticAt_zetaPoleFree s) hSan
    (analyticOrderAt_zetaPoleFree_ne_top s) ?_
  have hnhds : U ∩ {z : ℂ | z ≠ 1} ∈ nhds s :=
    (hUopen.inter isOpen_ne).mem_nhds ⟨hsU, hs1⟩
  filter_upwards [hnhds] with z hz
  obtain ⟨hzU, hzne⟩ := hz
  have h0 := hzero hzU
  simp only [hA] at h0
  have hz1 : z - 1 ≠ 0 := sub_ne_zero_of_ne hzne
  rw [hS]
  field_simp
  linear_combination h0

end RiemannHypothesis

end
