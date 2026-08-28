/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Spectral
import RiemannHypothesis.DeBruijnNewman
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The theta profile `W` behind the de Bruijn–Newman weight

This file introduces the function

`W(u) = e^u ω(e^{4u})`,  where  `ω(x) = ∑_{n ≥ 1} e^{-π n² x}`,

and establishes the facts about it that are needed to identify the de Bruijn–Newman function
`H₀` with the Riemann `Ξ` function:

* `wFun_eq_tsum`, `summable_wTerm` : `W` is the sum of the series `∑ e^{u - π n² e^{4u}}`;
* `hasDerivAt_wFun`, `hasDerivAt_wFun'` : `W` is twice differentiable, with the derivatives
  obtained by differentiating the series termwise;
* `dbnPhi_eq` : the de Bruijn–Newman weight is `Φ = (W'' - W)/8`;
* `wFun_neg` : the theta functional equation in the `u`-variable, `W(-u) = W(u) + sinh u`;
* `wFun'_zero` : consequently `W'(0) = -1/2`, the boundary term of the integration by parts;
* decay estimates and integrability of `W`, `W'`, `W''` against `cos(u z)` on `(0, ∞)`.
-/

noncomputable section

open Set MeasureTheory Filter Real
open scoped Topology Real

namespace RiemannHypothesis

/-- `ω(x) = ∑_{n ≥ 1} e^{-π n² x}`, the half theta series. -/
def thetaOmega (x : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x))

/-- The `n`-th term of the series for `W`: `e^{u - π (n+1)² e^{4u}}`. -/
def wTerm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))

/-- `W(u) = e^u ω(e^{4u})`, written as a series. -/
def wFun (u : ℝ) : ℝ := ∑' n : ℕ, wTerm n u

/-- The termwise derivative of `W`. -/
def wFun' (u : ℝ) : ℝ :=
  ∑' n : ℕ, (1 - 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) * wTerm n u

/-- The termwise second derivative of `W`. -/
def wFun'' (u : ℝ) : ℝ :=
  ∑' n : ℕ, (1 - 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
    + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) * wTerm n u

/-- The constant in the decay estimates for `W`, `W'` and `W''`. -/
def wConst : ℝ :=
  Real.exp π * ∑' n : ℕ,
    (1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4) *
      Real.exp (-(π * ((n : ℝ) + 1) ^ 2))

/-! ### Summability -/

/-- Summability of `n^k e^{-π n² E}` for `E > 0`. -/
lemma summable_pow_exp_neg (k : ℕ) {E : ℝ} (hE : 0 < E) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * E)) := by
  have hpi : 0 < π := Real.pi_pos
  have hr : ‖Real.exp (-(π * E))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hgeo : Summable fun n : ℕ => (n : ℝ) ^ k * (Real.exp (-(π * E))) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have hshift : Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * (Real.exp (-(π * E))) ^ (n + 1) := by
    have := (summable_nat_add_iff 1).mpr hgeo
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hshift
  gcongr
  have he : (Real.exp (-(π * E))) ^ (n + 1) = Real.exp (-(π * E) * ((n : ℝ) + 1)) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ π * E * ((n : ℝ) + 1) * (n : ℝ) := by positivity
  nlinarith

lemma wTerm_eq (n : ℕ) (u : ℝ) :
    wTerm n u = Real.exp u * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) := by
  rw [wTerm, ← Real.exp_add]
  ring_nf

lemma wTerm_pos (n : ℕ) (u : ℝ) : 0 < wTerm n u := Real.exp_pos _

lemma summable_wTerm_mul (u : ℝ) (k : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * wTerm n u := by
  have h := (summable_pow_exp_neg k (E := Real.exp (4 * u)) (Real.exp_pos _)).mul_left
    (Real.exp u)
  refine h.congr fun n => ?_
  rw [wTerm_eq]
  ring

lemma summable_wTerm (u : ℝ) : Summable fun n : ℕ => wTerm n u := by
  have h := summable_wTerm_mul u 0
  simpa using h

/-! ### `W` as `e^u ω(e^{4u})`, and the theta functional equation -/

lemma thetaOmega_eq_tsum (x : ℝ) :
    thetaOmega x = ∑' n : ℕ, Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x)) := rfl

lemma summable_thetaOmega_term (x : ℝ) (hx : 0 < x) :
    Summable fun n : ℕ => Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x)) := by
  simpa using summable_pow_exp_neg 0 hx

lemma wFun_eq (u : ℝ) : wFun u = Real.exp u * thetaOmega (Real.exp (4 * u)) := by
  rw [wFun, thetaOmega, ← tsum_mul_left]
  exact tsum_congr fun n => wTerm_eq n u

/-- The even Hurwitz kernel at `a = 0` is `1 + 2 ω`. -/
lemma evenKernel_zero_eq (x : ℝ) (hx : 0 < x) :
    HurwitzZeta.evenKernel 0 x = 1 + 2 * thetaOmega x := by
  have H := (HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) hx).nat_add_neg_add_one
  have h1 : HasSum (fun n : ℕ => Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x))) (thetaOmega x) :=
    (summable_thetaOmega_term x hx).hasSum
  have h0 : HasSum (fun n : ℕ => Real.exp (-(π * (n : ℝ) ^ 2 * x))) (thetaOmega x + 1) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using h1
  have hsum2 := h0.add h1
  have hval : HurwitzZeta.evenKernel ((0 : ℝ) : UnitAddCircle) x
      = thetaOmega x + 1 + thetaOmega x := by
    refine HasSum.unique (H.congr_fun ?_) hsum2
    intro n
    push_cast
    ring_nf
  rw [show ((0 : UnitAddCircle)) = ((0 : ℝ) : UnitAddCircle) by norm_num, hval]
  ring

/-- The theta functional equation in the form `ω(1/x) = √x ω(x) + (√x - 1)/2`. -/
lemma thetaOmega_inv (x : ℝ) (hx : 0 < x) :
    thetaOmega x⁻¹ = Real.sqrt x * thetaOmega x + (Real.sqrt x - 1) / 2 := by
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hfe := HurwitzZeta.evenKernel_functional_equation 0 x
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at hfe
  rw [evenKernel_zero_eq x hx, show (1 : ℝ) / x = x⁻¹ by ring,
    evenKernel_zero_eq x⁻¹ hxinv] at hfe
  have hsq : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  rw [hsq] at hfe
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  field_simp at hfe ⊢
  linarith [hfe]

/-- The theta functional equation in the `u`-variable: `W(-u) = W(u) + sinh u`. -/
theorem wFun_neg (u : ℝ) : wFun (-u) = wFun u + Real.sinh u := by
  have hE : (0 : ℝ) < Real.exp (4 * u) := Real.exp_pos _
  have hsqrt : Real.sqrt (Real.exp (4 * u)) = Real.exp (2 * u) := by
    have : Real.exp (4 * u) = (Real.exp (2 * u)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [this, Real.sqrt_sq (Real.exp_nonneg _)]
  have h1 : Real.exp (4 * -u) = (Real.exp (4 * u))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [wFun_eq, wFun_eq, h1, thetaOmega_inv _ hE, hsqrt, Real.sinh_eq]
  have h2 : Real.exp (-u) * Real.exp (u * 2) = Real.exp u := by
    rw [← Real.exp_add]; ring_nf
  ring_nf
  rw [h2]
  ring

/-! ### Differentiability -/

/-- The polynomial coefficient appearing in the first derivative of `wTerm`. -/
def wCoeff1 (n : ℕ) (u : ℝ) : ℝ := 1 - 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)

/-- The polynomial coefficient appearing in the second derivative of `wTerm`. -/
def wCoeff2 (n : ℕ) (u : ℝ) : ℝ :=
  1 - 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
    + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)

lemma wFun'_eq (u : ℝ) : wFun' u = ∑' n : ℕ, wCoeff1 n u * wTerm n u := rfl

lemma wFun''_eq (u : ℝ) : wFun'' u = ∑' n : ℕ, wCoeff2 n u * wTerm n u := rfl

lemma hasDerivAt_wTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (wTerm n) (wCoeff1 n u * wTerm n u) u := by
  have hinner : HasDerivAt (fun y : ℝ => y - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * y))
      (wCoeff1 n u) u := by
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (4 * y)) (Real.exp (4 * u) * 4) u := by
      have h0 : HasDerivAt (fun y : ℝ => 4 * y) 4 u := by
        simpa using (hasDerivAt_id u).const_mul (4 : ℝ)
      exact h0.exp
    have h2 := (hasDerivAt_id u).sub (h1.const_mul (π * ((n : ℝ) + 1) ^ 2))
    exact h2.congr_deriv (by simp only [wCoeff1]; ring)
  have h := hinner.exp
  have heq : wTerm n = fun y : ℝ => Real.exp (y - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * y)) := rfl
  rw [heq]
  exact h.congr_deriv (mul_comm _ _)

lemma hasDerivAt_wTerm_deriv (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y => wCoeff1 n y * wTerm n y) (wCoeff2 n u * wTerm n u) u := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (4 * y)) (Real.exp (4 * u) * 4) u := by
    have h0 : HasDerivAt (fun y : ℝ => 4 * y) 4 u := by
      simpa using (hasDerivAt_id u).const_mul (4 : ℝ)
    exact h0.exp
  have hc : HasDerivAt (fun y => wCoeff1 n y)
      (-(4 * π * ((n : ℝ) + 1) ^ 2 * (Real.exp (4 * u) * 4))) u := by
    simpa [wCoeff1] using
      ((h1.const_mul (4 * π * ((n : ℝ) + 1) ^ 2)).const_sub 1)
  have := hc.mul (hasDerivAt_wTerm n u)
  refine this.congr_deriv ?_
  have h8 : Real.exp (8 * u) = Real.exp (4 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]; ring_nf
  simp only [wCoeff1, wCoeff2, h8]
  ring

/-- A summable majorant for the terms and their first two derivatives on `[-M, M]`. -/
def wMaj (M : ℝ) (n : ℕ) : ℝ :=
  (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * M)
      + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * M)) *
    (Real.exp M * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (-(4 * M)))))

lemma summable_wMaj (M : ℝ) : Summable (wMaj M) := by
  have hE : (0 : ℝ) < Real.exp (-(4 * M)) := Real.exp_pos _
  have h0 := (summable_pow_exp_neg 0 hE).mul_left (Real.exp M)
  have h2 := (summable_pow_exp_neg 2 hE).mul_left (24 * π * Real.exp (4 * M) * Real.exp M)
  have h4 :=
    (summable_pow_exp_neg 4 hE).mul_left (16 * π ^ 2 * Real.exp (8 * M) * Real.exp M)
  refine ((h0.add h2).add h4).congr fun n => ?_
  simp only [wMaj]
  ring

lemma abs_wTerm_le {M y : ℝ} (hy : |y| ≤ M) (n : ℕ) :
    |wTerm n y| ≤ Real.exp M * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (-(4 * M)))) := by
  have hy1 : y ≤ M := (abs_le.mp hy).2
  have hy2 : -M ≤ y := (abs_le.mp hy).1
  have h4 : Real.exp (-(4 * M)) ≤ Real.exp (4 * y) := Real.exp_le_exp.mpr (by linarith)
  have hpos : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [wTerm_eq, abs_of_pos (by positivity)]
  have hb : Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * y)))
      ≤ Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (-(4 * M)))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul (Real.exp_le_exp.mpr hy1) hb (Real.exp_nonneg _) (Real.exp_nonneg _)

lemma abs_wCoeff1_le {M y : ℝ} (hy : |y| ≤ M) (n : ℕ) :
    |wCoeff1 n y| ≤ 1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * M)
      + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * M) := by
  have hy1 : y ≤ M := (abs_le.mp hy).2
  have h4 : Real.exp (4 * y) ≤ Real.exp (4 * M) := Real.exp_le_exp.mpr (by linarith)
  have hpos : (0 : ℝ) < Real.exp (4 * y) := Real.exp_pos _
  have hp8 : (0 : ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * M) := by positivity
  have hn : (0 : ℝ) ≤ 4 * π * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> simp only [wCoeff1] <;> nlinarith

lemma abs_wCoeff2_le {M y : ℝ} (hy : |y| ≤ M) (n : ℕ) :
    |wCoeff2 n y| ≤ 1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * M)
      + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * M) := by
  have hy1 : y ≤ M := (abs_le.mp hy).2
  have h4 : Real.exp (4 * y) ≤ Real.exp (4 * M) := Real.exp_le_exp.mpr (by linarith)
  have h8 : Real.exp (8 * y) ≤ Real.exp (8 * M) := Real.exp_le_exp.mpr (by linarith)
  have hpos4 : (0 : ℝ) < Real.exp (4 * y) := Real.exp_pos _
  have hpos8 : (0 : ℝ) < Real.exp (8 * y) := Real.exp_pos _
  have hn2 : (0 : ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hn4 : (0 : ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
  rw [abs_le]
  constructor <;> simp only [wCoeff2] <;> nlinarith

lemma norm_wCoeff1_mul_wTerm_le {M y : ℝ} (hy : |y| ≤ M) (n : ℕ) :
    ‖wCoeff1 n y * wTerm n y‖ ≤ wMaj M n := by
  rw [Real.norm_eq_abs, abs_mul, wMaj]
  exact mul_le_mul (abs_wCoeff1_le hy n) (abs_wTerm_le hy n) (abs_nonneg _) (by positivity)

lemma norm_wCoeff2_mul_wTerm_le {M y : ℝ} (hy : |y| ≤ M) (n : ℕ) :
    ‖wCoeff2 n y * wTerm n y‖ ≤ wMaj M n := by
  rw [Real.norm_eq_abs, abs_mul, wMaj]
  exact mul_le_mul (abs_wCoeff2_le hy n) (abs_wTerm_le hy n) (abs_nonneg _) (by positivity)

theorem hasDerivAt_wFun (u : ℝ) : HasDerivAt wFun (wFun' u) u := by
  set M : ℝ := |u| + 1 with hM
  have hmem : u ∈ Ioo (-M) M := by
    constructor <;> [nlinarith [abs_nonneg u, neg_abs_le u]; nlinarith [le_abs_self u]]
  have hle : ∀ y ∈ Ioo (-M) M, |y| ≤ M := fun y hy => abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_wMaj M) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_wTerm n y)
    (fun n y hy => norm_wCoeff1_mul_wTerm_le (hle y hy) n) hmem (summable_wTerm u) hmem

theorem hasDerivAt_wFun' (u : ℝ) : HasDerivAt wFun' (wFun'' u) u := by
  set M : ℝ := |u| + 1 with hM
  have hmem : u ∈ Ioo (-M) M := by
    constructor <;> [nlinarith [abs_nonneg u, neg_abs_le u]; nlinarith [le_abs_self u]]
  have hle : ∀ y ∈ Ioo (-M) M, |y| ≤ M := fun y hy => abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  have hsum1 : Summable fun n : ℕ => wCoeff1 n u * wTerm n u :=
    .of_norm_bounded (summable_wMaj M) fun n =>
      norm_wCoeff1_mul_wTerm_le (hle u hmem) n
  exact hasDerivAt_tsum_of_isPreconnected (summable_wMaj M) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_wTerm_deriv n y)
    (fun n y hy => norm_wCoeff2_mul_wTerm_le (hle y hy) n) hmem hsum1 hmem

/-- The boundary term of the integration by parts: `W'(0) = -1/2`.  This is the derivative at
`0` of the theta functional equation `W(-u) = W(u) + sinh u`. -/
theorem wFun'_zero : wFun' 0 = -(1 / 2) := by
  have h1 : HasDerivAt (fun u : ℝ => wFun (-u)) (-wFun' 0) 0 := by
    have hneg : HasDerivAt (fun u : ℝ => -u) (-1) 0 := hasDerivAt_neg 0
    exact ((hasDerivAt_wFun (-(0 : ℝ))).comp (0 : ℝ) hneg).congr_deriv
      (by ring_nf : wFun' (-(0 : ℝ)) * (-1) = -wFun' 0)
  have h2 : HasDerivAt (fun u : ℝ => wFun u + Real.sinh u) (wFun' 0 + Real.cosh 0) 0 :=
    (hasDerivAt_wFun 0).add (Real.hasDerivAt_sinh 0)
  have heq : (fun u : ℝ => wFun (-u)) = fun u : ℝ => wFun u + Real.sinh u := funext wFun_neg
  rw [heq] at h1
  have := h1.unique h2
  simp only [Real.cosh_zero] at this
  linarith

/-! ### The de Bruijn–Newman weight as `(W'' - W)/8` -/

lemma summable_wCoeff1_mul_wTerm (u : ℝ) : Summable fun n : ℕ => wCoeff1 n u * wTerm n u :=
  .of_norm_bounded (summable_wMaj |u|) fun n =>
    norm_wCoeff1_mul_wTerm_le (le_refl |u|) n

lemma summable_wCoeff2_mul_wTerm (u : ℝ) : Summable fun n : ℕ => wCoeff2 n u * wTerm n u :=
  .of_norm_bounded (summable_wMaj |u|) fun n =>
    norm_wCoeff2_mul_wTerm_le (le_refl |u|) n

theorem dbnPhi_eq (u : ℝ) : dbnPhi u = (wFun'' u - wFun u) / 8 := by
  rw [wFun''_eq, wFun,
    ← (summable_wCoeff2_mul_wTerm u).tsum_sub (summable_wTerm u), ← tsum_div_const]
  refine tsum_congr fun n => ?_
  have hE : Real.exp (8 * u) = Real.exp (4 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]; ring_nf
  have h9 : Real.exp (9 * u) = Real.exp u * (Real.exp (4 * u) * Real.exp (4 * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only [dbnTerm, wCoeff2, wTerm_eq, hE, h5, h9]
  push_cast
  ring

/-! ### Decay estimates -/

/-- The summand of the constant `wConst`. -/
def wConstTerm (n : ℕ) : ℝ :=
  (1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4) *
    Real.exp (-(π * ((n : ℝ) + 1) ^ 2))

lemma summable_wConstTerm : Summable wConstTerm := by
  have h0 := summable_pow_exp_neg 0 (E := (1 : ℝ)) one_pos
  have h2 := (summable_pow_exp_neg 2 (E := (1 : ℝ)) one_pos).mul_left (24 * π)
  have h4 := (summable_pow_exp_neg 4 (E := (1 : ℝ)) one_pos).mul_left (16 * π ^ 2)
  refine ((h0.add h2).add h4).congr fun n => ?_
  simp only [wConstTerm, mul_one]
  ring

lemma wConst_eq : wConst = Real.exp π * ∑' n : ℕ, wConstTerm n := rfl

lemma wConst_nonneg : 0 ≤ wConst := by
  refine mul_nonneg (Real.exp_nonneg _) (tsum_nonneg fun n => ?_)
  have : (0 : ℝ) ≤ 1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 := by
    positivity
  exact mul_nonneg this (Real.exp_nonneg _)

/-- The common decay estimate for the three series: any coefficients bounded by the
polynomial factor give a sum bounded by `wConst e^{9u} e^{-π e^{4u}}` for `u ≥ 0`. -/
lemma abs_tsum_mul_wTerm_le {c : ℕ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hc : ∀ n, |c n| ≤ 1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
      + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) :
    |∑' n : ℕ, c n * wTerm n u| ≤
      wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) := by
  have hE1 : (1 : ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  set K : ℝ := Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) * Real.exp π with hK
  have hKpos : 0 ≤ K := by positivity
  have hsum : HasSum (fun n => K * wConstTerm n) (K * ∑' n, wConstTerm n) :=
    summable_wConstTerm.hasSum.mul_left K
  have hbound : ∀ n : ℕ, ‖c n * wTerm n u‖ ≤ K * wConstTerm n := by
    intro n
    set m : ℝ := (n : ℝ) + 1 with hm
    have hm1 : (1 : ℝ) ≤ m := by simp [hm]
    have hE2 : Real.exp (8 * u) = Real.exp (4 * u) * Real.exp (4 * u) := by
      rw [← Real.exp_add]; ring_nf
    -- the polynomial factor
    have hpoly : 1 + 24 * π * m ^ 2 * Real.exp (4 * u) + 16 * π ^ 2 * m ^ 4 * Real.exp (8 * u)
        ≤ (1 + 24 * π * m ^ 2 + 16 * π ^ 2 * m ^ 4) * (Real.exp (4 * u) * Real.exp (4 * u)) := by
      rw [hE2]
      have h1 : (1 : ℝ) ≤ Real.exp (4 * u) * Real.exp (4 * u) := by nlinarith
      have h2 : Real.exp (4 * u) ≤ Real.exp (4 * u) * Real.exp (4 * u) := by nlinarith
      have hp2 : (0 : ℝ) ≤ 24 * π * m ^ 2 := by positivity
      nlinarith
    -- the exponential factor
    have hexp : Real.exp u * Real.exp (-(π * m ^ 2 * Real.exp (4 * u)))
        ≤ Real.exp u * (Real.exp (-(π * Real.exp (4 * u))) *
          (Real.exp π * Real.exp (-(π * m ^ 2)))) := by
      have hle : -(π * m ^ 2 * Real.exp (4 * u))
          ≤ -(π * Real.exp (4 * u)) + (π + -(π * m ^ 2)) := by
        have hmm : (1 : ℝ) ≤ m ^ 2 := by nlinarith
        have hpi : 0 < π := Real.pi_pos
        nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.mpr hmm))
          (sub_nonneg.mpr hE1)]
      have := Real.exp_le_exp.mpr hle
      rw [Real.exp_add, Real.exp_add] at this
      exact mul_le_mul_of_nonneg_left this (Real.exp_nonneg _)
    have hw : wTerm n u = Real.exp u * Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) := wTerm_eq n u
    rw [Real.norm_eq_abs, abs_mul, hw,
      abs_of_pos (show (0:ℝ) < Real.exp u * Real.exp (-(π * m ^ 2 * Real.exp (4 * u))) by
        positivity)]
    have hcn := hc n
    calc |c n| * (Real.exp u * Real.exp (-(π * m ^ 2 * Real.exp (4 * u))))
        ≤ ((1 + 24 * π * m ^ 2 + 16 * π ^ 2 * m ^ 4) *
            (Real.exp (4 * u) * Real.exp (4 * u))) *
          (Real.exp u * (Real.exp (-(π * Real.exp (4 * u))) *
            (Real.exp π * Real.exp (-(π * m ^ 2))))) := by
          refine mul_le_mul (le_trans hcn hpoly) hexp (by positivity) (by positivity)
      _ = K * wConstTerm n := by
          simp only [hK, wConstTerm, ← hm]
          have h9 : Real.exp (9 * u)
              = Real.exp (4 * u) * Real.exp (4 * u) * Real.exp u := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [h9]
          ring
  have := tsum_of_norm_bounded hsum hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans_eq ?_
  simp only [hK, wConst_eq]
  ring

lemma abs_wFun_le {u : ℝ} (hu : 0 ≤ u) :
    |wFun u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) := by
  have h : wFun u = ∑' n : ℕ, (1 : ℝ) * wTerm n u := by
    rw [wFun]; exact tsum_congr fun n => (one_mul _).symm
  rw [h]
  refine abs_tsum_mul_wTerm_le hu fun n => ?_
  have h1 : (0 : ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by positivity
  have h2 : (0 : ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u) := by positivity
  rw [abs_one]
  linarith

lemma abs_wFun'_le {u : ℝ} (hu : 0 ≤ u) :
    |wFun' u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) := by
  rw [wFun'_eq]
  exact abs_tsum_mul_wTerm_le hu fun n => abs_wCoeff1_le (le_of_eq (abs_of_nonneg hu)) n

lemma abs_wFun''_le {u : ℝ} (hu : 0 ≤ u) :
    |wFun'' u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) := by
  rw [wFun''_eq]
  exact abs_tsum_mul_wTerm_le hu fun n => abs_wCoeff2_le (le_of_eq (abs_of_nonneg hu)) n

/-- The crude form of the decay used for the limits at `+∞`. -/
lemma abs_le_exp_neg_of_three_le {f : ℝ → ℝ} {u : ℝ} (hu : 3 ≤ u)
    (hf : |f u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) :
    |f u| ≤ wConst * Real.exp (-u) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hdecay := exp_neg_pi_exp_le hu0
  have hstep : Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))
      ≤ Real.exp (-u) := by
    calc Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))
        ≤ Real.exp (9 * u) * Real.exp (-2 * u ^ 3) :=
          mul_le_mul_of_nonneg_left hdecay (Real.exp_nonneg _)
      _ = Real.exp (9 * u + -2 * u ^ 3) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u, sq_nonneg (u - 3)])
  calc |f u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) := hf
    _ = wConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) := by ring
    _ ≤ wConst * Real.exp (-u) := mul_le_mul_of_nonneg_left hstep wConst_nonneg

/-- `W` tends to `0` at `+∞`. -/
lemma tendsto_wFun_atTop : Tendsto wFun atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun u : ℝ => wConst * Real.exp (-u)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with u hu
    exact abs_le_exp_neg_of_three_le hu (abs_wFun_le (by linarith))
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul wConst)

/-- `W'` tends to `0` at `+∞`. -/
lemma tendsto_wFun'_atTop : Tendsto wFun' atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun u : ℝ => wConst * Real.exp (-u)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with u hu
    exact abs_le_exp_neg_of_three_le hu (abs_wFun'_le (by linarith))
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul wConst)

/-- Any function with the `W`-type decay, multiplied by an exponential, tends to `0`. -/
lemma tendsto_decay_mul_exp {f : ℝ → ℝ}
    (hf : ∀ {u : ℝ}, 0 ≤ u →
      |f u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) (a : ℝ) :
    Tendsto (fun u : ℝ => |f u| * Real.exp (a * u)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun u : ℝ => wConst * Real.exp (-u)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (|a| + 3 : ℝ)] with u hu
    have ha : (0 : ℝ) ≤ |a| := abs_nonneg a
    have hu3 : (3 : ℝ) ≤ u := by linarith
    have hu0 : (0 : ℝ) ≤ u := by linarith
    have hdecay := exp_neg_pi_exp_le hu0
    have hstep : Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) * Real.exp (a * u)
        ≤ Real.exp (-u) := by
      calc Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) * Real.exp (a * u)
          ≤ Real.exp (9 * u) * Real.exp (-2 * u ^ 3) * Real.exp (a * u) := by
            gcongr
        _ = Real.exp (9 * u + -2 * u ^ 3 + a * u) := by rw [← Real.exp_add, ← Real.exp_add]
        _ ≤ Real.exp (-u) := by
            refine Real.exp_le_exp.mpr ?_
            have hle : a ≤ |a| := le_abs_self a
            nlinarith [sq_nonneg u, sq_nonneg (u - 3), mul_nonneg ha hu0]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg (a * u)), abs_abs]
    calc |f u| * Real.exp (a * u)
        ≤ (wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) * Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (hf hu0) (Real.exp_nonneg _)
      _ = wConst * (Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u))) * Real.exp (a * u)) := by
          ring
      _ ≤ wConst * Real.exp (-u) := mul_le_mul_of_nonneg_left hstep wConst_nonneg
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul wConst)

/-! ### Continuity and integrability against `cos (u z)` -/

lemma differentiable_wFun : Differentiable ℝ wFun := fun u => (hasDerivAt_wFun u).differentiableAt

lemma differentiable_wFun' : Differentiable ℝ wFun' :=
  fun u => (hasDerivAt_wFun' u).differentiableAt

lemma continuous_wFun : Continuous wFun := differentiable_wFun.continuous

lemma continuous_wFun' : Continuous wFun' := differentiable_wFun'.continuous

/-- `W''` is continuous on `(0, ∞)`: it equals `8Φ + W`, and `Φ` is continuous there. -/
lemma continuousOn_wFun''_Ioi : ContinuousOn wFun'' (Ioi 0) := by
  have h : ∀ u : ℝ, wFun'' u = 8 * dbnPhi u + wFun u := by
    intro u
    have := dbnPhi_eq u
    linarith
  simp only [funext h]
  exact (continuousOn_dbnPhi_Ioi.const_smul (8 : ℝ)).add continuous_wFun.continuousOn |>.congr
    fun u _ => by simp [smul_eq_mul]

/-- Integrability of the general cosine integrand, given the decay estimate. -/
lemma integrableOn_mul_cos_of_decay {f : ℝ → ℝ} (hcont : ContinuousOn f (Ioi 0)) (z : ℂ)
    (hf : ∀ {u : ℝ}, 0 ≤ u →
      |f u| ≤ wConst * Real.exp (9 * u) * Real.exp (-(π * Real.exp (4 * u)))) :
    IntegrableOn (fun u : ℝ => (f u : ℂ) * Complex.cos (u * z)) (Ioi 0) := by
  have hint : IntegrableOn
      (fun u : ℝ => wConst * Real.exp (0 * u ^ 2 + (9 + ‖z‖) * u - 2 * u ^ 3)) (Ioi 0) :=
    (integrableOn_exp_quadratic_sub_cube 0 (9 + ‖z‖) (by norm_num : (0:ℝ) < 2)).const_mul wConst
  refine Integrable.mono' hint ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Complex.continuous_ofReal.comp_continuousOn hcont).mul
      ((Complex.continuous_cos.comp (by fun_prop)).continuousOn)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  rw [norm_mul, Complex.norm_real]
  have h2 : ‖Complex.cos ((u : ℝ) * z)‖ ≤ Real.exp (u * ‖z‖) := by
    refine (norm_ccos_le _).trans_eq ?_
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
  have hdecay := exp_neg_pi_exp_le hu0
  have hstep : ‖f u‖ * ‖Complex.cos ((u : ℝ) * z)‖
      ≤ (wConst * Real.exp (9 * u) * Real.exp (-2 * u ^ 3)) * Real.exp (u * ‖z‖) := by
    refine mul_le_mul ?_ h2 (norm_nonneg _) (by have := wConst_nonneg; positivity)
    rw [Real.norm_eq_abs]
    refine (hf hu0).trans ?_
    have : Real.exp (-(π * Real.exp (4 * u))) ≤ Real.exp (-2 * u ^ 3) := hdecay
    have hpos : (0 : ℝ) ≤ wConst * Real.exp (9 * u) := by
      have := wConst_nonneg; positivity
    nlinarith
  refine hstep.trans_eq ?_
  rw [show wConst * Real.exp (9 * u) * Real.exp (-2 * u ^ 3) * Real.exp (u * ‖z‖)
      = wConst * (Real.exp (9 * u) * Real.exp (-2 * u ^ 3) * Real.exp (u * ‖z‖)) by ring]
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

lemma integrableOn_wFun_mul_cos (z : ℂ) :
    IntegrableOn (fun u : ℝ => (wFun u : ℂ) * Complex.cos (u * z)) (Ioi 0) :=
  integrableOn_mul_cos_of_decay continuous_wFun.continuousOn z fun hu => abs_wFun_le hu

lemma integrableOn_wFun''_mul_cos (z : ℂ) :
    IntegrableOn (fun u : ℝ => (wFun'' u : ℂ) * Complex.cos (u * z)) (Ioi 0) :=
  integrableOn_mul_cos_of_decay continuousOn_wFun''_Ioi z fun hu => abs_wFun''_le hu

end RiemannHypothesis

end
