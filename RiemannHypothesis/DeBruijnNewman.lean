/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The de Bruijn–Newman constant

This file defines the de Bruijn–Newman family `H t` and the de Bruijn–Newman constant `Λ`,
and states the two propositions that surround it.

## Definitions

* `dbnTerm n u` and `dbnPhi u` : the super-exponentially decaying weight
  `Φ(u) = ∑_{n ≥ 1} (2 π² n⁴ e^{9u} − 3 π n² e^{5u}) e^{−π n² e^{4u}}`
  of de Bruijn and Newman.  It arises from the Jacobi theta function in the standard
  integral representation of the completed zeta function: `Ξ(z) = ∫_0^∞ Φ(u) cos(u z) du`.

* `dbnH t z = ∫_0^∞ e^{t u²} Φ(u) cos(u z) du` : the heat flow applied to that integral
  representation.  `H 0` is (up to normalisation) the Riemann `Ξ` function, and the Riemann
  hypothesis says exactly that all zeroes of `H 0` are real.

* `dbnLambda` : the de Bruijn–Newman constant `Λ = inf {t | all zeroes of H t are real}`.
  De Bruijn proved that the set `{t | all zeroes of H t are real}` is an up-set and contains
  `[1/2, ∞)`, so the infimum is the boundary of a half-line.

## Results

* `differentiable_dbnH` : for every real `t`, `H t` is an entire function of `z`.  This is the
  analytic content of the definition: the integral converges for every complex `z` because
  `Φ(u)` decays like `e^{−π e^{4u}}`, which beats both the Gaussian factor `e^{t u²}` and the
  exponential growth `e^{u |Im z|}` of the cosine.  The proof goes through the explicit decay
  estimate `|Φ(u)| ≤ C e^{9u} e^{−π e^{4u}}` for `u ≥ 0` (`abs_dbnPhi_le`) and differentiation
  under the integral sign.

## Statements (not proved here)

* `DeBruijnNewmanEquivRH` : `ZetaForm ↔ Λ ≤ 0` (de Bruijn 1950, Newman 1976).
* `DeBruijnNewmanNonnegative` : `0 ≤ Λ` (Rodgers–Tao 2018).

Both are recorded as `Prop`s, in the same spirit as `RiemannHypothesis.Partial`: the
repository states what the literature proves without claiming it.  In particular
`DeBruijnNewmanEquivRH` is *not* proved here; proving it requires the identification of
`H 0` with the Riemann `Ξ` function and de Bruijn's theory of the heat flow on entire
functions.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Real

namespace RiemannHypothesis

/-- The `n`-th term of the de Bruijn–Newman weight `Φ`:
`(2 π² n⁴ e^{9u} − 3 π n² e^{5u}) e^{−π n² e^{4u}}`. -/
def dbnTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (4 * u)))

/-- The de Bruijn–Newman weight
`Φ(u) = ∑_{n ≥ 1} (2 π² n⁴ e^{9u} − 3 π n² e^{5u}) e^{−π n² e^{4u}}`. -/
def dbnPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ, dbnTerm (n + 1) u

/-- The summable majorant of the terms of `Φ` on `u ≥ 0`. -/
def dbnBound (n : ℕ) : ℝ :=
  (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 + 3 * π * ((n : ℝ) + 1) ^ 2) *
    Real.exp (-(π * ((n : ℝ) + 1) ^ 2))

/-- The constant in the decay estimate `|Φ(u)| ≤ C e^{9u} e^{−π e^{4u}}` for `u ≥ 0`. -/
def dbnConst : ℝ := Real.exp π * ∑' n : ℕ, dbnBound n

/-- The integrand of `H t`: `e^{t u²} Φ(u) cos(u z)`. -/
def dbnKernel (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * dbnPhi u : ℝ) : ℂ) * Complex.cos ((u : ℂ) * z)

/-- The de Bruijn–Newman family `H t (z) = ∫_0^∞ e^{t u²} Φ(u) cos(u z) du`. -/
def dbnH (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), dbnKernel t z u

/-- The **de Bruijn–Newman constant** `Λ = inf {t | every zero of H t is real}`. -/
def dbnLambda : ℝ :=
  sInf {t : ℝ | ∀ z : ℂ, dbnH t z = 0 → z.im = 0}

/-- **De Bruijn (1950) – Newman (1976)**: the Riemann hypothesis is equivalent to `Λ ≤ 0`.
Stated, not proved. -/
def DeBruijnNewmanEquivRH : Prop :=
  ZetaForm ↔ dbnLambda ≤ 0

/-- **Rodgers–Tao (2018)**: the de Bruijn–Newman constant is nonnegative.  Stated, not
proved. -/
def DeBruijnNewmanNonnegative : Prop :=
  0 ≤ dbnLambda

/-! ### Elementary estimates for the weight `Φ` -/

lemma dbnBound_nonneg (n : ℕ) : 0 ≤ dbnBound n := by
  have hpi := Real.pi_pos
  unfold dbnBound
  positivity

lemma summable_dbnBound : Summable dbnBound := by
  have hpi := Real.pi_pos
  have hr : ‖Real.exp (-π)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hk : ∀ k : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-π) ^ n) := fun k =>
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have hsum : Summable (fun n : ℕ =>
      (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 + 3 * π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π) ^ n) := by
    have s4 := (hk 4).mul_left (2 * π ^ 2)
    have s3 := (hk 3).mul_left (8 * π ^ 2)
    have s2 := (hk 2).mul_left (12 * π ^ 2 + 3 * π)
    have s1 := (hk 1).mul_left (8 * π ^ 2 + 6 * π)
    have s0 := (hk 0).mul_left (2 * π ^ 2 + 3 * π)
    refine ((((s4.add s3).add s2).add s1).add s0).congr (fun n => ?_)
    ring
  refine Summable.of_nonneg_of_le dbnBound_nonneg (fun n => ?_) hsum
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : Real.exp (-(π * ((n : ℝ) + 1) ^ 2)) ≤ Real.exp (-π) ^ n := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hpi.le (mul_nonneg hn hn), mul_nonneg hpi.le hn]
  have h2 : (0 : ℝ) ≤ 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 + 3 * π * ((n : ℝ) + 1) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h1 h2

/-- Termwise bound valid on `0 ≤ u ≤ A`. -/
lemma abs_dbnTerm_le_of_mem_Icc {A u : ℝ} (hu : u ∈ Icc (0 : ℝ) A) (n : ℕ) :
    |dbnTerm (n + 1) u| ≤ Real.exp (9 * A) * dbnBound n := by
  obtain ⟨hu0, huA⟩ := hu
  have hpi := Real.pi_pos
  have hx : (1 : ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set m : ℝ := (n : ℝ) + 1 with hmdef
  have hm1 : (1 : ℝ) ≤ m := by simp only [hmdef]; linarith
  have hcast : dbnTerm (n + 1) u =
      (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)) *
        Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) := by
    simp only [dbnTerm, hmdef]
    push_cast
    ring
  rw [hcast, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hA : (0 : ℝ) ≤ 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) := by positivity
  have hB : (0 : ℝ) ≤ 3 * π * m ^ 2 * Real.exp (5 * u) := by positivity
  have h1 : |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)| ≤
      2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) + 3 * π * m ^ 2 * Real.exp (5 * u) := by
    rcases abs_cases (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) -
      3 * π * m ^ 2 * Real.exp (5 * u)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have e9 : Real.exp (9 * u) ≤ Real.exp (9 * A) := Real.exp_le_exp.mpr (by linarith)
  have e5 : Real.exp (5 * u) ≤ Real.exp (9 * A) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) + 3 * π * m ^ 2 * Real.exp (5 * u) ≤
      (2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) * Real.exp (9 * A) := by
    have p1 : (0 : ℝ) ≤ 2 * π ^ 2 * m ^ 4 := by positivity
    have p2 : (0 : ℝ) ≤ 3 * π * m ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e9 p1, mul_le_mul_of_nonneg_left e5 p2]
  have h3 : Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) ≤ Real.exp (-(π * m ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg hpi.le (sq_nonneg m)) (sub_nonneg.mpr hx)]
  calc |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)| *
        Real.exp (-(π * m ^ 2 * Real.exp (4 * u)))
      ≤ ((2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) * Real.exp (9 * A)) * Real.exp (-(π * m ^ 2)) :=
        mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by positivity)
    _ = Real.exp (9 * A) * dbnBound n := by simp only [dbnBound, hmdef]; ring

/-- Termwise bound valid for all `u ≥ 0`, with the decay factor made explicit. -/
lemma abs_dbnTerm_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |dbnTerm (n + 1) u| ≤
      (Real.exp π * dbnBound n) * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) := by
  have hpi := Real.pi_pos
  have hx : (1 : ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set m : ℝ := (n : ℝ) + 1 with hmdef
  have hm1 : (1 : ℝ) ≤ m := by simp only [hmdef]; linarith
  have hm2 : (1 : ℝ) ≤ m ^ 2 := by nlinarith
  have hcast : dbnTerm (n + 1) u =
      (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)) *
        Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) := by
    simp only [dbnTerm, hmdef]
    push_cast
    ring
  rw [hcast, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hA : (0 : ℝ) ≤ 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) := by positivity
  have hB : (0 : ℝ) ≤ 3 * π * m ^ 2 * Real.exp (5 * u) := by positivity
  have h1 : |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)| ≤
      2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) + 3 * π * m ^ 2 * Real.exp (5 * u) := by
    rcases abs_cases (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) -
      3 * π * m ^ 2 * Real.exp (5 * u)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have e5 : Real.exp (5 * u) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) + 3 * π * m ^ 2 * Real.exp (5 * u) ≤
      (2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) * Real.exp (9 * u) := by
    have p2 : (0 : ℝ) ≤ 3 * π * m ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e5 p2]
  have key : 0 ≤ π * ((m ^ 2 - 1) * (Real.exp (4 * u) - 1)) :=
    mul_nonneg hpi.le (mul_nonneg (by linarith) (by linarith))
  have h3 : Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) ≤
      Real.exp π * Real.exp (-(π * m ^ 2)) * Real.exp (-(π * Real.exp (4 * u))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [key]
  calc |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)| *
        Real.exp (-(π * m ^ 2 * Real.exp (4 * u)))
      ≤ ((2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) * Real.exp (9 * u)) *
        (Real.exp π * Real.exp (-(π * m ^ 2)) * Real.exp (-(π * Real.exp (4 * u)))) :=
        mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by positivity)
    _ = (Real.exp π * dbnBound n) *
        (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) := by
        simp only [dbnBound, hmdef]; ring

lemma dbnConst_nonneg : 0 ≤ dbnConst :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg dbnBound_nonneg)

/-- The decay estimate for `Φ` on the positive half-line. -/
lemma abs_dbnPhi_le {u : ℝ} (hu : 0 ≤ u) :
    |dbnPhi u| ≤ dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) := by
  have hmaj : Summable (fun n : ℕ => (Real.exp π * dbnBound n) *
      (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) :=
    (summable_dbnBound.mul_left _).mul_right _
  have habs : Summable (fun n : ℕ => |dbnTerm (n + 1) u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_dbnTerm_le_of_nonneg hu n) hmaj
  have h1 : |dbnPhi u| ≤ ∑' n : ℕ, |dbnTerm (n + 1) u| := by
    have := norm_tsum_le_tsum_norm (f := fun n : ℕ => dbnTerm (n + 1) u)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [dbnPhi, Real.norm_eq_abs] using this
  refine h1.trans ?_
  refine (Summable.tsum_le_tsum (fun n => abs_dbnTerm_le_of_nonneg hu n) habs hmaj).trans_eq ?_
  rw [tsum_mul_right, tsum_mul_left]
  simp only [dbnConst]

lemma continuous_dbnTerm (n : ℕ) : Continuous fun u : ℝ => dbnTerm n u := by
  unfold dbnTerm
  fun_prop

lemma continuousOn_dbnPhi_Icc {A : ℝ} : ContinuousOn dbnPhi (Icc 0 A) := by
  change ContinuousOn (fun u => ∑' n : ℕ, dbnTerm (n + 1) u) (Icc 0 A)
  refine continuousOn_tsum (u := fun n => Real.exp (9 * A) * dbnBound n)
    (fun n => (continuous_dbnTerm (n + 1)).continuousOn) (summable_dbnBound.mul_left _) ?_
  intro n x hx
  rw [Real.norm_eq_abs]
  exact abs_dbnTerm_le_of_mem_Icc hx n

lemma continuousOn_dbnPhi_Ioi : ContinuousOn dbnPhi (Ioi 0) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hmem : Icc (0 : ℝ) (u + 1) ∈ 𝓝 u := Icc_mem_nhds hu0 (by linarith)
  exact ((continuousOn_dbnPhi_Icc (A := u + 1) u
    ⟨hu0.le, by linarith⟩).continuousAt hmem).continuousWithinAt

/-! ### The dominating integrand -/

/-- A cubic decay beats a quadratic growth: `exp (a u² + b u − c u³)` is integrable on the
positive half-line for every `c > 0`. -/
lemma integrableOn_exp_quadratic_sub_cube (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (a * u ^ 2 + b * u - c * u ^ 3)) (Ioi 0) := by
  set R : ℝ := max 1 ((|a| + |b| + 1) / c) with hR
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have key : ∀ u : ℝ, R ≤ u → Real.exp (a * u ^ 2 + b * u - c * u ^ 3) ≤ Real.exp (-1 * u) := by
    intro u hu
    refine Real.exp_le_exp.mpr ?_
    have hu1 : (1 : ℝ) ≤ u := le_trans hR1 hu
    have hcu : (|a| + |b| + 1) / c ≤ u := le_trans (le_max_right _ _) hu
    have hcu' : |a| + |b| + 1 ≤ c * u := by
      rw [div_le_iff₀ hc] at hcu; linarith [hcu]
    nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b, sq_nonneg u,
      sq_nonneg (u - 1)]
  have hcont : Continuous fun u : ℝ => Real.exp (a * u ^ 2 + b * u - c * u ^ 3) := by fun_prop
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (a * u ^ 2 + b * u - c * u ^ 3)) (Ioc 0 R) :=
    hcont.integrableOn_Ioc
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (a * u ^ 2 + b * u - c * u ^ 3)) (Ioi R) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi R one_pos)
      (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact key u (le_of_lt hu)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := (Ioc_union_Ioi_eq_Ioi hR0).symm
  rw [hsplit]
  exact h1.union h2

/-- `e^{-π e^{4u}} ≤ e^{-2 u³}` for `u ≥ 0`. -/
lemma exp_neg_pi_exp_le {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-(π * Real.exp (4 * u))) ≤ Real.exp (-2 * u ^ 3) := by
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have h1 : (4 / 3 : ℝ) * u ≤ Real.exp ((4 / 3) * u) := by
    have := Real.add_one_le_exp ((4 / 3 : ℝ) * u)
    linarith
  have h2 : ((4 / 3 : ℝ) * u) ^ 3 ≤ (Real.exp ((4 / 3) * u)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h3 : (Real.exp ((4 / 3) * u)) ^ 3 = Real.exp (4 * u) := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring_nf
  have h4 : (64 / 27 : ℝ) * u ^ 3 ≤ Real.exp (4 * u) := by
    rw [← h3]; nlinarith [h2]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [pow_nonneg hu 3]

lemma norm_ccos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h : (-w * Complex.I).re = w.im := by simp
    rw [h]
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm w)
  have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h : (w * Complex.I).re = -w.im := by simp
    rw [h]
    exact le_trans (neg_le_abs _) (Complex.abs_im_le_norm w)
  rw [Complex.cos, norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2', div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖
      ≤ ‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖ := norm_add_le _ _
    _ ≤ Real.exp ‖w‖ * 2 := by linarith

lemma norm_csin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h : (-w * Complex.I).re = w.im := by simp
    rw [h]
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm w)
  have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h : (w * Complex.I).re = -w.im := by simp
    rw [h]
    exact le_trans (neg_le_abs _) (Complex.abs_im_le_norm w)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2', div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖
      ≤ ‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖ := norm_sub_le _ _
    _ ≤ Real.exp ‖w‖ * 2 := by linarith

/-- The pointwise bound for the integrand of `H t`. -/
lemma norm_dbnKernel_le (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖dbnKernel t z u‖ ≤
      dbnConst * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3) := by
  rw [dbnKernel, norm_mul, Complex.norm_real]
  have h1 : |Real.exp (t * u ^ 2) * dbnPhi u| ≤
      Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_dbnPhi_le hu) (Real.exp_pos _).le
  have h2 : ‖Complex.cos ((u : ℂ) * z)‖ ≤ Real.exp (u * ‖z‖) := by
    refine (norm_ccos_le _).trans_eq ?_
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu]
  have h3 : Real.exp (t * u ^ 2) *
      (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) *
      Real.exp (u * ‖z‖) ≤
      dbnConst * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3) := by
    have hdecay := exp_neg_pi_exp_le hu
    have hstep : Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) *
        Real.exp (u * ‖z‖) ≤
        Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-2 * u ^ 3))) * Real.exp (u * ‖z‖) := by
      have hc := dbnConst_nonneg
      have hpos : (0:ℝ) ≤ Real.exp (t * u ^ 2) * dbnConst * Real.exp (9 * u) *
          Real.exp (u * ‖z‖) := by positivity
      nlinarith [hdecay, hpos]
    refine hstep.trans_eq ?_
    rw [show Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-2 * u ^ 3))) * Real.exp (u * ‖z‖) =
        dbnConst * (Real.exp (t * u ^ 2) * Real.exp (9 * u) * Real.exp (-2 * u ^ 3) *
          Real.exp (u * ‖z‖)) by ring]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  refine le_trans (mul_le_mul h1 h2 (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg dbnConst_nonneg (by positivity)))) h3

lemma continuousOn_dbnKernel (t : ℝ) (z : ℂ) : ContinuousOn (dbnKernel t z) (Ioi 0) := by
  unfold dbnKernel
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_exp.comp (by fun_prop)).continuousOn).mul continuousOn_dbnPhi_Ioi))
  · exact (Complex.continuous_cos.comp (by fun_prop)).continuousOn

lemma integrableOn_dbnKernel (t : ℝ) (z : ℂ) : IntegrableOn (dbnKernel t z) (Ioi 0) := by
  refine Integrable.mono'
    (((integrableOn_exp_quadratic_sub_cube t (9 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul
      dbnConst))
    ((continuousOn_dbnKernel t z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_dbnKernel_le t z (le_of_lt hu)

/-! ### Symmetries of `H t` -/

/-- `H t` is an even function of `z`, because the cosine is. -/
theorem dbnH_neg (t : ℝ) (z : ℂ) : dbnH t (-z) = dbnH t z := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  simp only [dbnKernel, mul_neg, Complex.cos_neg]

/-- `H t` is real on the real axis, in the form `H t (conj z) = conj (H t z)`: the weight and
the Gaussian factor are real, and the cosine commutes with conjugation. -/
theorem dbnH_conj (t : ℝ) (z : ℂ) :
    dbnH t ((starRingEnd ℂ) z) = (starRingEnd ℂ) (dbnH t z) := by
  rw [dbnH, dbnH, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  simp only [dbnKernel, map_mul, Complex.conj_ofReal, ← Complex.cos_conj, map_mul,
    Complex.conj_ofReal]

/-- The zero set of `H t` is symmetric about the real axis. -/
theorem dbnH_conj_eq_zero (t : ℝ) {z : ℂ} (hz : dbnH t z = 0) :
    dbnH t ((starRingEnd ℂ) z) = 0 := by
  rw [dbnH_conj, hz, map_zero]

/-! ### `H t` is entire -/

/-- The `z`-derivative of the integrand. -/
def dbnKernelDeriv (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * dbnPhi u : ℝ) : ℂ) * (-Complex.sin ((u : ℂ) * z) * (u : ℂ))

lemma hasDerivAt_dbnKernel (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => dbnKernel t w u) (dbnKernelDeriv t z u) z := by
  have h : HasDerivAt (fun w : ℂ => (u : ℂ) * w) (u : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (u : ℂ)
  exact (h.ccos.const_mul _)

lemma norm_dbnKernelDeriv_le (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖dbnKernelDeriv t z u‖ ≤
      dbnConst * Real.exp (t * u ^ 2 + (10 + ‖z‖) * u - 2 * u ^ 3) := by
  have hnorm : ‖dbnKernelDeriv t z u‖ =
      |Real.exp (t * u ^ 2) * dbnPhi u| * (‖Complex.sin ((u : ℂ) * z)‖ * u) := by
    rw [dbnKernelDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg hu]
  rw [hnorm]
  have h1 : |Real.exp (t * u ^ 2) * dbnPhi u| ≤
      Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_dbnPhi_le hu) (Real.exp_pos _).le
  have h2 : ‖Complex.sin ((u : ℂ) * z)‖ * u ≤ Real.exp (u * ‖z‖) * Real.exp u := by
    have hs : ‖Complex.sin ((u : ℂ) * z)‖ ≤ Real.exp (u * ‖z‖) := by
      refine (norm_csin_le _).trans_eq ?_
      congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu]
    have hue : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    exact mul_le_mul hs hue hu (Real.exp_pos _).le
  have h3 : Real.exp (t * u ^ 2) *
      (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) *
      (Real.exp (u * ‖z‖) * Real.exp u) ≤
      dbnConst * Real.exp (t * u ^ 2 + (10 + ‖z‖) * u - 2 * u ^ 3) := by
    have hdecay := exp_neg_pi_exp_le hu
    have hstep : Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))))) *
        (Real.exp (u * ‖z‖) * Real.exp u) ≤
        Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-2 * u ^ 3))) *
        (Real.exp (u * ‖z‖) * Real.exp u) := by
      have hc := dbnConst_nonneg
      have hpos : (0:ℝ) ≤ Real.exp (t * u ^ 2) * dbnConst * Real.exp (9 * u) *
          (Real.exp (u * ‖z‖) * Real.exp u) := by positivity
      nlinarith [hdecay, hpos]
    refine hstep.trans_eq ?_
    rw [show Real.exp (t * u ^ 2) *
        (dbnConst * (Real.exp (9 * u) * Real.exp (-2 * u ^ 3))) *
        (Real.exp (u * ‖z‖) * Real.exp u) =
        dbnConst * (Real.exp (t * u ^ 2) * Real.exp (9 * u) * Real.exp (-2 * u ^ 3) *
          Real.exp (u * ‖z‖) * Real.exp u) by ring]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  refine le_trans ?_ h3
  exact mul_le_mul h1 h2 (by positivity)
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg dbnConst_nonneg (by positivity)))

lemma continuousOn_dbnKernelDeriv (t : ℝ) (z : ℂ) :
    ContinuousOn (dbnKernelDeriv t z) (Ioi 0) := by
  unfold dbnKernelDeriv
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_exp.comp (by fun_prop)).continuousOn).mul continuousOn_dbnPhi_Ioi))
  · exact ((Complex.continuous_sin.comp (by fun_prop)).neg.mul (by fun_prop)).continuousOn

/-- **The de Bruijn–Newman family is entire**: for every real `t`, `z ↦ H t (z)` is
differentiable on all of `ℂ`. -/
theorem differentiable_dbnH (t : ℝ) : Differentiable ℂ (dbnH t) := by
  intro z
  have hball : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hbound_int : Integrable
      (fun u : ℝ => dbnConst * Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_quadratic_sub_cube t (11 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul dbnConst
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun w u => dbnKernel t w u)
    (F' := fun w u => dbnKernelDeriv t w u)
    (bound := fun u => dbnConst * Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3))
    (s := Metric.ball z 1) (x₀ := z) hball
    (Eventually.of_forall fun w =>
      (continuousOn_dbnKernel t w).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_dbnKernel t z)
    ((continuousOn_dbnKernelDeriv t z).aestronglyMeasurable measurableSet_Ioi)
    ?_ hbound_int ?_
  · exact (hmain.2).differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := Metric.mem_ball.mp hw
      rw [Complex.dist_eq] at this
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    refine (norm_dbnKernelDeriv_le t w hu0).trans ?_
    have hmono : Real.exp (t * u ^ 2 + (10 + ‖w‖) * u - 2 * u ^ 3) ≤
        Real.exp (t * u ^ 2 + (11 + ‖z‖) * u - 2 * u ^ 3) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hu0, hw']
    exact mul_le_mul_of_nonneg_left hmono dbnConst_nonneg
  · filter_upwards with u
    intro w _
    exact hasDerivAt_dbnKernel t w u

end RiemannHypothesis

end
