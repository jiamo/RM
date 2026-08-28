/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Connected
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Dirichlet eta function

This file proves the analytic facts about the Dirichlet eta function `η(s)` (defined in
`RiemannHypothesis.Defs`) that the equivalence of the formulations of the Riemann hypothesis
needs.

## Main results

* `summable_pairedTerm`: for `0 < re s` the paired series defining `η(s)` converges
  absolutely.
* `differentiableOn_dirichletEta`: `η` is differentiable (hence analytic) on the right
  half-plane `{s | 0 < re s}`.  Each paired term is entire, and the paired series converges
  absolutely and locally uniformly, so the Weierstrass theorem applies.
* `dirichletEta_eq_tsum_alternating_of_one_lt_re`: for `1 < re s` the classical alternating
  series representation `η(s) = ∑' n, (-1)^n / (n+1)^s` holds.
* `dirichletEta_eq_mul_riemannZeta`: for `0 < re s`, `s ≠ 1` we have the classical identity
  `η(s) = (1 - 2^(1-s)) ζ(s)`.  Both sides are analytic on the punctured right half-plane
  and agree on the open set `{s | 1 < re s}` by an elementary manipulation of absolutely
  convergent Dirichlet series, so the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) applies; the domain is preconnected
  by `RiemannHypothesis.isPreconnected_punctured_halfPlane`.
-/

noncomputable section

open Complex Set Filter Finset

open scoped BigOperators Topology

namespace RiemannHypothesis

/-! ## The paired terms are entire -/

/-- `s ↦ n ^ (-s)` is entire for `n ≠ 0`. -/
lemma differentiable_const_cpow_neg (n : ℕ) (hn : n ≠ 0) :
    Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) := by
  intro s
  exact (differentiableAt_id.neg.const_cpow (c := (n : ℂ)) (Or.inl (by exact_mod_cast hn)))

/-- Each paired term is entire. -/
lemma differentiable_pairedTerm (j : ℕ) : Differentiable ℂ (pairedTerm j) := by
  unfold pairedTerm
  exact (differentiable_const_cpow_neg (2 * j + 1) (by omega)).sub
    (differentiable_const_cpow_neg (2 * j + 2) (by omega))

/-! ## The norm bound -/

/-- The norm of a paired term, bounded via the mean value theorem applied to `exp` on the
segment joining `-s log(2j+1)` to `-s log(2j+2)`. -/
lemma norm_pairedTerm_le (j : ℕ) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ‖pairedTerm j s‖ ≤
      ‖s‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) := by
  let u : ℝ := Real.log (2 * j + 1 : ℝ)
  let v : ℝ := Real.log (2 * j + 2 : ℝ)
  have hne1 : (2 * j + 1 : ℕ) ≠ 0 := by omega
  have hne2 : (2 * j + 2 : ℕ) ≠ 0 := by omega
  have hpos1 : 0 < (2 * j + 1 : ℝ) := by positivity
  have hpos2 : 0 < (2 * j + 2 : ℝ) := by positivity
  have huj : u ≤ v := by
    dsimp [u, v]
    exact Real.log_le_log hpos1 (by linarith : (2 * j + 1 : ℝ) ≤ (2 * j + 2 : ℝ))
  have hcast1 : ((2 * j + 1 : ℕ) : ℂ) = ((2 * j + 1 : ℝ) : ℂ) := by norm_num
  have hcast2 : ((2 * j + 2 : ℕ) : ℂ) = ((2 * j + 2 : ℝ) : ℂ) := by norm_num
  have hpa : pairedTerm j s = exp (-s * (u : ℂ)) - exp (-s * (v : ℂ)) := by
    unfold pairedTerm
    rw [hcast1, hcast2]
    rw [Complex.cpow_def_of_ne_zero (x := ((2 * j + 1 : ℝ) : ℂ))
      (by exact_mod_cast (by omega : (2 * j + 1 : ℕ) ≠ 0)) (-s)]
    rw [Complex.cpow_def_of_ne_zero (x := ((2 * j + 2 : ℝ) : ℂ))
      (by exact_mod_cast (by omega : (2 * j + 2 : ℕ) ≠ 0)) (-s)]
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * j + 1)]
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * j + 2)]
    congr 1
    · ring_nf
    · ring_nf
  rw [hpa]
  let C : ℝ := Real.exp (-s.re * u)
  have hf : ∀ x ∈ segment ℝ (-s * (u : ℂ)) (-s * (v : ℂ)), DifferentiableAt ℂ exp x := by
    intro x hx
    exact Complex.differentiable_exp (𝕜 := ℂ) x
  have hbound : ∀ x ∈ segment ℝ (-s * (u : ℂ)) (-s * (v : ℂ)), ‖deriv exp x‖ ≤ C := by
    intro x hx
    rcases mem_segment_real_comb hx with ⟨a, b, ha, hb, hab, hxdef⟩
    have hmid : u ≤ a * u + b * v := by
      calc
        u = (a + b) * u := by rw [hab]; ring
        _ = a * u + b * u := by ring
        _ ≤ a * u + b * v := by
          gcongr
    have hxre : x.re ≤ -s.re * u := by
      rw [hxdef]
      calc
        (a • (-s * (u : ℂ)) + b • (-s * (v : ℂ))).re = -s.re * (a * u + b * v) := by
          simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
          ring_nf
        _ ≤ -s.re * u := by
          exact mul_le_mul_of_nonpos_left hmid (by linarith [hs0])
    calc
      ‖deriv exp x‖ = ‖exp x‖ := by rw [Complex.deriv_exp]
      _ = Real.exp x.re := Complex.norm_exp x
      _ ≤ C := by
        dsimp [C]
        exact (Real.exp_le_exp.mpr hxre)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hf hbound
    (convex_segment (𝕜 := ℝ) (-s * (u : ℂ)) (-s * (v : ℂ)))
    (left_mem_segment ℝ (-s * (u : ℂ)) (-s * (v : ℂ)))
    (right_mem_segment ℝ (-s * (u : ℂ)) (-s * (v : ℂ)))
  calc
    ‖exp (-s * (u : ℂ)) - exp (-s * (v : ℂ))‖ ≤ C * ‖(-s * (v : ℂ)) - (-s * (u : ℂ))‖ := by
      rw [norm_sub_rev]
      exact hmvt
    _ = C * (‖s‖ * (v - u)) := by
      have hnorm : ‖(-s * (v : ℂ)) - (-s * (u : ℂ))‖ = ‖s‖ * (v - u) := by
        rw [show (-s * (v : ℂ)) - (-s * (u : ℂ)) = -s * ((v : ℂ) - (u : ℂ)) by ring]
        rw [norm_mul, norm_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr huj)]
      rw [hnorm]
    _ = C * ‖s‖ * (v - u) := by ring
    _ = ‖s‖ * (v - u) * ((2 * j + 1 : ℝ) ^ (-s.re)) := by
      dsimp [C, u, v]
      have hC : Real.exp (-s.re * Real.log (2 * j + 1 : ℝ)) = (2 * j + 1 : ℝ) ^ (-s.re) := by
        rw [Real.rpow_def_of_pos hpos1]
        congr 1
        ring
      rw [hC]
      ring
    _ = ‖s‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) := by
      dsimp [u, v]
      rw [Real.log_div hpos2.ne' hpos1.ne']

/-- The logarithms `log ((2j+2)/(2j+1))` are bounded by `1/(2j+1)`. -/
lemma log_pair_le_inv (j : ℕ) :
    Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) ≤ 1 / (2 * j + 1 : ℝ) := by
  have hpos : 0 < (2 * j + 1 : ℝ) := by positivity
  have hx : 0 < 1 + 1 / (2 * j + 1 : ℝ) := by positivity
  have hx' : (2 * j + 2 : ℝ) / (2 * j + 1 : ℝ) = 1 + 1 / (2 * j + 1 : ℝ) := by
    field_simp [hpos.ne']
    ring
  rw [hx']
  rw [Real.log_le_iff_le_exp hx]
  rw [add_comm]
  exact Real.add_one_le_exp (1 / (2 * j + 1 : ℝ))

/-! ## Summability and analyticity -/

/-- The paired series is summable at any `s` with `0 < re s`. -/
lemma summable_pairedTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun j : ℕ => pairedTerm j s) := by
  refine Summable.of_norm_bounded (g := fun j => ‖s‖ * (j + 1 : ℝ) ^ (-(1 + s.re / 2))) ?_ ?_
  · have hp : -(1 + s.re / 2) < -1 := by linarith [hs]
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re / 2))) :=
      Real.summable_nat_rpow.mpr hp
    have h' : Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-(1 + s.re / 2))) := by
      have hc := h.comp_injective (add_left_injective 1)
      simpa [Function.comp_def] using hc
    exact h'.mul_left ‖s‖
  · intro j
    calc
      ‖pairedTerm j s‖
          ≤ ‖s‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) :=
        norm_pairedTerm_le j (le_of_lt hs)
      _ ≤ ‖s‖ * (1 / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-s.re)) := by
        gcongr
        exact log_pair_le_inv j
      _ = ‖s‖ * (2 * j + 1 : ℝ) ^ (-(1 + s.re)) := by
        rw [mul_assoc]
        rw [show (1 / (2 * j + 1 : ℝ)) * (2 * j + 1 : ℝ) ^ (-s.re)
            = (2 * j + 1 : ℝ) ^ (-(1 + s.re)) by
          have hneg : (2 * j + 1 : ℝ) ^ (-1 : ℝ) = 1 / (2 * j + 1 : ℝ) := by
            rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * j + 1)]
            rw [Real.rpow_one]
            rw [div_eq_mul_inv]
            rw [one_mul]
          rw [← hneg]
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2 * j + 1)]
          rw [show -1 + -s.re = -(1 + s.re) by ring]]
      _ ≤ ‖s‖ * (j + 1 : ℝ) ^ (-(1 + s.re)) := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
          (by exact_mod_cast (by omega : 0 < j + 1))
          (by exact_mod_cast (by omega : j + 1 ≤ 2 * j + 1))
          (by linarith : -(1 + s.re) ≤ 0)) (norm_nonneg s)
      _ ≤ ‖s‖ * (j + 1 : ℝ) ^ (-(1 + s.re / 2)) := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (by omega : 1 ≤ j + 1))
          (by linarith : -(1 + s.re) ≤ -(1 + s.re / 2))) (norm_nonneg s)

/-- The paired series is analytic on the whole right half-plane. -/
lemma differentiableOn_tsum_paired :
    DifferentiableOn ℂ (fun s : ℂ => ∑' j : ℕ, pairedTerm j s) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hsr : 0 < s.re := hs
  let δ : ℝ := s.re / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hsr]
  let U : Set ℂ := {z : ℂ | ‖z - s‖ < δ}
  have hU_open : IsOpen U :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have hU_sub : U ⊆ {z : ℂ | δ < z.re} := by
    intro z hz
    have hle : s.re - z.re ≤ ‖z - s‖ := by
      have h1 : |(s - z).re| ≤ ‖s - z‖ := Complex.abs_re_le_norm (s - z)
      have h2 : (s - z).re = s.re - z.re := by simp
      rw [h2] at h1
      rw [norm_sub_rev] at h1
      exact le_trans (abs_le.mp h1).2 (by linarith)
    have hzn : ‖z - s‖ < δ := by simpa [U] using hz
    dsimp [δ] at hle hzn ⊢
    linarith [hle, hzn]
  have hU_self : s ∈ U := by
    dsimp [U]
    simpa using hδ
  let M : ℝ := ‖s‖ + δ
  have hM : ∀ z ∈ U, ‖z‖ ≤ M := by
    intro z hz
    calc
      ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by
        nth_rewrite 1 [← sub_add_cancel z s]
        exact norm_add_le (z - s) s
      _ ≤ δ + ‖s‖ := by
        have hzn : ‖z - s‖ ≤ δ := le_of_lt (by simpa [U] using hz)
        linarith
      _ = M := by dsimp [M]; ring
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' j : ℕ, pairedTerm j s) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun j : ℕ => M * (j + 1 : ℝ) ^ (-(1 + δ / 2)))
      ?_ (fun j => (differentiable_pairedTerm j).differentiableOn) hU_open ?_
    · have hp : -(1 + δ / 2) < -1 := by linarith [hδ]
      have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + δ / 2))) :=
        Real.summable_nat_rpow.mpr hp
      have h' : Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-(1 + δ / 2))) := by
        have hc := h.comp_injective (add_left_injective 1)
        simpa [Function.comp_def] using hc
      exact h'.mul_left M
    · intro j z hz
      have hzδ' : δ < z.re := by simpa using hU_sub hz
      have hz0 : 0 < z.re := lt_trans hδ hzδ'
      have hzδ : δ ≤ z.re := le_of_lt hzδ'
      calc
        ‖pairedTerm j z‖
            ≤ ‖z‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-z.re)) :=
          norm_pairedTerm_le j (le_of_lt hz0)
        _ ≤ M * (1 / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-z.re)) := by
          have hL0 : 0 ≤ Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) := by
            rw [Real.log_nonneg_iff (by positivity : 0 < (2 * j + 2 : ℝ) / (2 * j + 1 : ℝ))]
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * j + 1)]
            norm_num
          have hX0 : 0 ≤ (2 * j + 1 : ℝ) ^ (-z.re) := by positivity
          calc
            ‖z‖ * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-z.re))
                ≤ M * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ))
                    * ((2 * j + 1 : ℝ) ^ (-z.re)) := by
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM z hz) hL0) hX0
            _ ≤ M * (1 / (2 * j + 1 : ℝ)) * ((2 * j + 1 : ℝ) ^ (-z.re)) := by
              have hM0 : 0 ≤ M := by nlinarith [norm_nonneg s, hδ]
              have h1 : M * Real.log ((2 * j + 2 : ℝ) / (2 * j + 1 : ℝ))
                  ≤ M * (1 / (2 * j + 1 : ℝ)) := by
                exact mul_le_mul_of_nonneg_left (log_pair_le_inv j) hM0
              exact mul_le_mul_of_nonneg_right h1 hX0
        _ = M * (2 * j + 1 : ℝ) ^ (-(1 + z.re)) := by
          rw [mul_assoc]
          rw [show (1 / (2 * j + 1 : ℝ)) * (2 * j + 1 : ℝ) ^ (-z.re)
              = (2 * j + 1 : ℝ) ^ (-(1 + z.re)) by
            have hneg : (2 * j + 1 : ℝ) ^ (-1 : ℝ) = 1 / (2 * j + 1 : ℝ) := by
              rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * j + 1)]
              rw [Real.rpow_one]
              rw [div_eq_mul_inv]
              rw [one_mul]
            rw [← hneg]
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2 * j + 1)]
            rw [show -1 + -z.re = -(1 + z.re) by ring]]
        _ ≤ M * (j + 1 : ℝ) ^ (-(1 + z.re)) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
            (by exact_mod_cast (by omega : 0 < j + 1))
            (by exact_mod_cast (by omega : j + 1 ≤ 2 * j + 1))
            (by linarith : -(1 + z.re) ≤ 0)) (by nlinarith [norm_nonneg s, hδ])
        _ ≤ M * (j + 1 : ℝ) ^ (-(1 + δ)) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (by omega : 1 ≤ j + 1))
            (by linarith [hzδ] : -(1 + z.re) ≤ -(1 + δ))) (by nlinarith [norm_nonneg s, hδ])
        _ ≤ M * (j + 1 : ℝ) ^ (-(1 + δ / 2)) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (by omega : 1 ≤ j + 1))
            (by linarith : -(1 + δ) ≤ -(1 + δ / 2))) (by nlinarith [norm_nonneg s, hδ])
  exact (hdiff.differentiableAt (hU_open.mem_nhds hU_self)).differentiableWithinAt

/-- The Dirichlet eta function is analytic on the right half-plane `{s | 0 < re s}`. -/
lemma differentiableOn_dirichletEta :
    DifferentiableOn ℂ dirichletEta {s : ℂ | 0 < s.re} := by
  exact differentiableOn_tsum_paired

/-- `η` is analytic on the punctured right half-plane. -/
lemma analyticOnNhd_dirichletEta :
    AnalyticOnNhd ℂ dirichletEta ({s : ℂ | 0 < s.re} \ {1}) := by
  exact (differentiableOn_dirichletEta.analyticOnNhd
    (isOpen_lt continuous_const continuous_re)).mono (by intro z hz; exact hz.1)

/-! ## The alternating series representation, for `1 < re s` -/

/-- For `1 < re s` the classical alternating series `∑' n, (-1)^n / (n+1)^s` converges
absolutely, and its sum is `η(s)`. -/
lemma dirichletEta_eq_tsum_alternating_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    dirichletEta s = ∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s := by
  have hs0 : 0 < s.re := by linarith
  have hAlt : Summable (fun n : ℕ => (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) := by
    refine Summable.of_norm_bounded (g := fun n => (n + 1 : ℝ) ^ (-s.re)) ?_ ?_
    · have hp : -s.re < -1 := by linarith
      have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := Real.summable_nat_rpow.mpr hp
      exact (h.comp_injective (add_left_injective 1)).congr (by
        intro n
        simp only [Function.comp_apply]
        rw [Nat.cast_add]
        norm_num)
    · intro n
      calc
        ‖(-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s‖ = ‖(n + 1 : ℂ) ^ s‖⁻¹ := by
          rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
          simp [div_eq_mul_inv]
        _ = (n + 1 : ℝ) ^ (-s.re) := by
          rw [show (n + 1 : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_num]
          rw [show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by norm_num]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (x := ((n + 1 : ℕ) : ℝ))
            (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) s]
          rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
        _ ≤ (n + 1 : ℝ) ^ (-s.re) := le_rfl
  have hP : Summable (fun j : ℕ => pairedTerm j s) := summable_pairedTerm hs0
  -- the even partial sums of the alternating series are the partial sums of the paired series
  have hS_even : ∀ K : ℕ, (∑ n ∈ range (2 * K), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) =
      ∑ j ∈ range K, pairedTerm j s := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [show 2 * (K + 1) = 2 * K + 2 by omega]
      rw [sum_range_succ, sum_range_succ]
      have h1 : (-1 : ℂ) ^ (2 * K) = 1 := by
        rw [pow_mul]
        norm_num
      have h2 : (-1 : ℂ) ^ (2 * K + 1) = -1 := by
        rw [pow_succ, h1]
        norm_num
      have hnew : (-1 : ℂ) ^ (2 * K) / (((2 * K : ℕ) : ℂ) + 1) ^ s +
          (-1 : ℂ) ^ (2 * K + 1) / (((2 * K + 1 : ℕ) : ℂ) + 1) ^ s = pairedTerm K s := by
        rw [h1, h2, pairedTerm]
        rw [show (1 : ℂ) / (((2 * K : ℕ) : ℂ) + 1) ^ s = (((2 * K : ℕ) : ℂ) + 1) ^ (-s) by
          rw [div_eq_mul_inv, one_mul]
          rw [← cpow_neg]]
        rw [show (-1 : ℂ) / (((2 * K + 1 : ℕ) : ℂ) + 1) ^ s
            = -((((2 * K + 1 : ℕ) : ℂ) + 1) ^ (-s)) by
          rw [div_eq_mul_inv]
          rw [← cpow_neg]
          ring]
        simp [Nat.cast_add, Nat.cast_one]
        ring_nf
      rw [ih, add_assoc, hnew]
      rw [show ∑ j ∈ range (K + 1), pairedTerm j s
          = (∑ j ∈ range K, pairedTerm j s) + pairedTerm K s by
        rw [sum_range_succ]]
  -- both the alternating tsum and the paired tsum are limits of the even partial sums
  have h₁ : Tendsto (fun K : ℕ => ∑ n ∈ range (2 * K), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 (∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s)) := by
    have hmap : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
      tendsto_atTop_mono (fun K => by dsimp; omega) tendsto_id
    exact (hAlt.tendsto_sum_tsum_nat.comp hmap)
  have h₂ : Tendsto (fun K : ℕ => ∑ n ∈ range (2 * K), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 (∑' j : ℕ, pairedTerm j s)) := by
    simpa [hS_even] using hP.tendsto_sum_tsum_nat
  have hEq : (∑' j : ℕ, pairedTerm j s) = ∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s :=
    tendsto_nhds_unique h₂ h₁
  exact (by rfl : dirichletEta s = ∑' j : ℕ, pairedTerm j s).trans hEq

/-! ## The identity `η(s) = (1 - 2^(1-s)) ζ(s)` -/

/-- The elementary identity on the half-plane of absolute convergence: for `1 < re s`,
`η(s) = (1 - 2^(1-s)) ζ(s)`.  Proof: split the absolutely convergent Dirichlet series of
`ζ` into its odd and even parts. -/
lemma dirichletEta_eq_mul_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    dirichletEta s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  let O : ℂ := ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)
  let E : ℂ := ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)
  -- summability of the odd and even subseries
  have hOddSum : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (g := fun k => (k + 1 : ℝ) ^ (-s.re)) ?_ ?_
    · have hp : -s.re < -1 := by linarith
      have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := Real.summable_nat_rpow.mpr hp
      exact (h.comp_injective (add_left_injective 1)).congr (by
        intro n
        simp only [Function.comp_apply]
        rw [Nat.cast_add]
        norm_num)
    · intro k
      calc
        ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖ = (2 * k + 1 : ℝ) ^ (-s.re) := by
          rw [show ((2 * k + 1 : ℕ) : ℂ) = ((2 * k + 1 : ℝ) : ℂ) by norm_num]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * k + 1) (-s)]
          simp
        _ ≤ (k + 1 : ℝ) ^ (-s.re) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < k + 1)
            (by linarith : (k + 1 : ℝ) ≤ 2 * k + 1) (by linarith : -s.re ≤ 0)
  have hEvenSum : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (g := fun k => (k + 1 : ℝ) ^ (-s.re)) ?_ ?_
    · have hp : -s.re < -1 := by linarith
      have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := Real.summable_nat_rpow.mpr hp
      exact (h.comp_injective (add_left_injective 1)).congr (by
        intro n
        simp only [Function.comp_apply]
        rw [Nat.cast_add]
        norm_num)
    · intro k
      calc
        ‖((2 * k + 2 : ℕ) : ℂ) ^ (-s)‖ = (2 * k + 2 : ℝ) ^ (-s.re) := by
          rw [show ((2 * k + 2 : ℕ) : ℂ) = ((2 * k + 2 : ℝ) : ℂ) by norm_num]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * k + 2) (-s)]
          simp
        _ ≤ (k + 1 : ℝ) ^ (-s.re) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < k + 1)
            (by linarith : (k + 1 : ℝ) ≤ 2 * k + 2) (by linarith : -s.re ≤ 0)
  have hO : HasSum (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) O := by
    simpa [O] using hOddSum.hasSum
  have hE : HasSum (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) E := by
    simpa [E] using hEvenSum.hasSum
  -- `ζ = O + E`: the odd/even split of the Dirichlet series of `ζ`
  have hzeta : riemannZeta s = O + E := by
    have hEvenOdd : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (O + E) :=
      HasSum.even_add_odd hO hE
    have hSeries : riemannZeta s = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
      exact tsum_congr (by
        intro n
        rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by norm_num]
        rw [div_eq_mul_inv, one_mul]
        rw [← cpow_neg])
    rw [hSeries]
    exact hEvenOdd.tsum_eq
  -- `E = 2^(-s) * ζ`
  have hE' : E = 2 ^ (-s) * riemannZeta s := by
    calc
      E = ∑' k : ℕ, (2 ^ (-s) * ((k + 1 : ℕ) : ℂ) ^ (-s)) := by
        exact tsum_congr (by
          intro k
          have hk : (2 * k + 2 : ℕ) = 2 * (k + 1) := by omega
          rw [hk]
          rw [show ((2 * (k + 1) : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) by norm_num]
          rw [mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) (-s)]
          norm_num)
      _ = 2 ^ (-s) * (∑' k : ℕ, ((k + 1 : ℕ) : ℂ) ^ (-s)) := by
        rw [tsum_mul_left]
      _ = 2 ^ (-s) * riemannZeta s := by
        congr 1
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
        exact tsum_congr (by
          intro n
          rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by norm_num]
          rw [div_eq_mul_inv, one_mul]
          rw [← cpow_neg])
  -- `η = O - E`
  have heta : dirichletEta s = O - E := by
    have hP : HasSum (fun j : ℕ => pairedTerm j s) (O - E) := hO.sub hE
    unfold dirichletEta
    exact hP.tsum_eq
  -- put the pieces together
  have htwo : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring]
    rw [cpow_add (1 : ℂ) (-s) (by norm_num : (2 : ℂ) ≠ 0)]
    rw [cpow_one]
  calc
    dirichletEta s = O - E := heta
    _ = O + E - 2 * E := by ring
    _ = (1 - 2 * 2 ^ (-s)) * (O + E) := by
      have hE'' : E = 2 ^ (-s) * (O + E) := by
        calc
          E = 2 ^ (-s) * riemannZeta s := hE'
          _ = 2 ^ (-s) * (O + E) := by rw [hzeta]
      calc
        O + E - 2 * E = O + E - 2 * (2 ^ (-s) * (O + E)) := by
          conv_lhs => arg 2; rw [hE'']
        _ = (1 - 2 * 2 ^ (-s)) * (O + E) := by ring
    _ = (1 - 2 * 2 ^ (-s)) * riemannZeta s := by rw [hzeta]
    _ = (1 - 2 ^ (1 - s)) * riemannZeta s := by rw [← htwo]


/-- `s ↦ 1 - 2^(1-s)` is entire, hence analytic on any open set. -/
lemma analyticOnNhd_one_sub_two_cpow :
    AnalyticOnNhd ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) ({s : ℂ | 0 < s.re} \ {1}) := by
  have h₂ : DifferentiableOn ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) univ := by
    intro s hs
    fun_prop
  have h₁ : AnalyticOnNhd ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) univ :=
    DifferentiableOn.analyticOnNhd h₂ isOpen_univ
  exact (AnalyticOnNhd.sub
    (analyticOnNhd_const (𝕜 := ℂ) (E := ℂ) (F := ℂ) (v := (1 : ℂ)) (s := univ)) h₁).mono
    (by intro z hz; trivial)

/-- `ζ` is analytic on the punctured right half-plane. -/
lemma analyticOnNhd_riemannZeta :
    AnalyticOnNhd ℂ riemannZeta ({s : ℂ | 0 < s.re} \ {1}) := by
  have h₁ : AnalyticOnNhd ℂ riemannZeta ({s : ℂ | s ≠ 1}) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro s hs
    exact (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact h₁.mono (by intro z hz; exact hz.2)

/-- The right-hand side of the identity `η = (1 - 2^(1-s)) ζ` is analytic on the punctured
right half-plane. -/
lemma analyticOnNhd_mul_riemannZeta :
    AnalyticOnNhd ℂ (fun s : ℂ => (1 - 2 ^ (1 - s)) * riemannZeta s)
      ({s : ℂ | 0 < s.re} \ {1}) := by
  exact (analyticOnNhd_one_sub_two_cpow.mul analyticOnNhd_riemannZeta)

/-- **The classical identity** `η(s) = (1 - 2^(1-s)) ζ(s)`, valid on the punctured right
half-plane.  Both sides are analytic there and agree on the open set `{s | 1 < re s}`, so the
identity theorem applies; the domain is preconnected by
`RiemannHypothesis.isPreconnected_punctured_halfPlane`. -/
lemma dirichletEta_eq_mul_riemannZeta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    dirichletEta s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hU : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := isPreconnected_punctured_halfPlane
  have hz₀ : (2 : ℂ) ∈ ({s : ℂ | 0 < s.re} \ {1}) := by simp
  have hfg : dirichletEta =ᶠ[𝓝 (2 : ℂ)] (fun s : ℂ => (1 - 2 ^ (1 - s)) * riemannZeta s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact dirichletEta_eq_mul_riemannZeta_of_one_lt_re hz
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_dirichletEta) (analyticOnNhd_mul_riemannZeta) hU hz₀ hfg
  exact heq ⟨hs0, hs1⟩

end RiemannHypothesis

end
