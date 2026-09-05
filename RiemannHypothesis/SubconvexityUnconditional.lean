/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.AFESubconvexity
import RiemannHypothesis.KusminLandauGeneral
import RiemannHypothesis.Continuation

/-!
# Unconditional subconvexity on the critical line

`RiemannHypothesis.AFESubconvexity` bounds the Dirichlet polynomial `∑_{n ≤ N} n^(-1/2-it)` for
`N ≤ √t` by `t^(1/6) log t`, and deduces the subconvexity bound for `ζ` itself *conditionally on
the approximate functional equation*, which shortens the Dirichlet polynomial to length `√(t/2π)`.

This file removes that hypothesis.  The approximate functional equation is not needed: the
Euler–Maclaurin representation of `ζ` (`RiemannHypothesis.riemannZeta_eq_zetaApprox_of_pos_re`)
already writes `ζ(1/2+it)` as a Dirichlet polynomial of length `N ≈ t²` plus a bounded error, and
the three van der Corput tests of this repository between them bound *every* dyadic block of that
much longer polynomial by the same `t^(1/6)`:

* `30 t^(1/3) ≤ M ≤ t^(2/3)` — van der Corput's third derivative test
  (`RiemannHypothesis.VanDerCorputThird`);
* `t^(2/3) ≤ M ≤ 2t` — van der Corput's second derivative test
  (`RiemannHypothesis.VanDerCorputSums`);
* `2t ≤ M ≤ t²` — the Kusmin–Landau first derivative test
  (`RiemannHypothesis.KusminLandauGeneral`), the phase derivative `t/2πx` being then smaller
  than `1/4π` and therefore separated from the integers by itself;
* `M ≤ 30 t^(1/3)` — the trivial bound.

The height parameter is written `u = t^(1/6)`, as in `RiemannHypothesis.AFESubconvexity`.

## Main results

* `block_bound_numeric_quartic` — the arithmetic core of the third derivative test, with the
  range of the block extended from `M ≤ u³` to `M ≤ u⁴`, which is where the test stops being
  the strongest of the three.
* `norm_sum_e2pi_logPhase_block_le_quartic`, `norm_sum_e2pi_logPhase_block_le_mid`,
  `norm_sum_e2pi_logPhase_block_le_long` — the three block estimates.
* `norm_sum_e2pi_logPhase_block_le_all` — one block, in the whole range `30u² ≤ M ≤ u¹²`.
* `norm_zetaSum_le_of_le_pow_twelve` — the Dirichlet polynomial of length `N ≤ t²`.
* `norm_riemannZeta_sub_zetaSum_le` — the Euler–Maclaurin error at length `⌊t²⌋`.
* `norm_riemannZeta_criticalLine_le` — **unconditionally**,
  `‖ζ(1/2+it)‖ ≤ 200 t^(1/6) (log t + 1)` for `t ≥ 10⁹`.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace SubconvexityUnconditional

open KusminLandau VanDerCorputThird AFESubconvexity

/-! ## The third derivative test up to `M ≤ u⁴` -/

set_option maxHeartbeats 1000000 in
-- The `nlinarith` chain below is heavy; it needs more than the default heartbeat budget.
/-- The arithmetic core of the block estimate, with `P ≤ u⁴` in place of `P ≤ u³`. -/
theorem block_bound_numeric_quartic {P L H R A X u : ℝ} (hu : 1 ≤ u) (hP30 : 30 * u ^ 2 ≤ P)
    (hPu : P ≤ u ^ 4) (hL0 : 0 ≤ L) (hLP : L ≤ P)
    (hH0 : 0 < H) (hHlo : P ≤ H * u ^ 2) (hHhi : H * u ^ 2 ≤ 2 * P)
    (hR0 : 0 ≤ R) (hRb : R * P ^ 3 * 3 ≤ u ^ 6)
    (hA0 : 0 ≤ A) (hAb : A * u ^ 4 ≤ 8 * P ^ 2) (hX0 : 0 ≤ X)
    (hmain : H * X ^ 2
      ≤ (L + H) * (L + 8 * R * L * H ^ 2 + 16 * H + 20 * R * L * H * A + 80 * A)) :
    X ≤ 60 * Real.sqrt P * u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hP0 : (0 : ℝ) < P := by nlinarith
  have e3 : H ^ 2 * u ^ 4 ≤ 4 * P ^ 2 := by nlinarith [mul_pos hH0 (pow_pos hu0 2)]
  have t1 : (R * P ^ 3 * 3) * L ≤ u ^ 6 * P := mul_le_mul hRb hLP hL0 (by positivity)
  have t2 : ((R * P ^ 3 * 3) * L) * (H ^ 2 * u ^ 4) ≤ (u ^ 6 * P) * (4 * P ^ 2) :=
    mul_le_mul t1 e3 (by positivity) (by positivity)
  have ha : 8 * R * L * H ^ 2 ≤ 11 * u ^ 2 := by
    have hpos : (0 : ℝ) < 3 * P ^ 3 * u ^ 4 := by positivity
    have key : (3 * P ^ 3 * u ^ 4) * (8 * R * L * H ^ 2) ≤ (3 * P ^ 3 * u ^ 4) * (11 * u ^ 2) := by
      nlinarith [t2, pow_pos hP0 3, pow_pos hu0 6]
    exact le_of_mul_le_mul_left key hpos
  have hb : 16 * H ≤ 32 * P := by nlinarith [hH0.le]
  have s2 : ((R * P ^ 3 * 3) * L) * (H * u ^ 2) ≤ (u ^ 6 * P) * (2 * P) :=
    mul_le_mul t1 hHhi (by positivity) (by positivity)
  have s3 : (((R * P ^ 3 * 3) * L) * (H * u ^ 2)) * (A * u ^ 4)
      ≤ ((u ^ 6 * P) * (2 * P)) * (8 * P ^ 2) :=
    mul_le_mul s2 hAb (by positivity) (by positivity)
  have hc : 20 * R * L * H * A ≤ 107 * P := by
    have hpos : (0 : ℝ) < 3 * P ^ 3 * u ^ 6 := by positivity
    have key : (3 * P ^ 3 * u ^ 6) * (20 * R * L * H * A) ≤ (3 * P ^ 3 * u ^ 6) * (107 * P) := by
      nlinarith [s3, pow_pos hP0 4, pow_pos hu0 6]
    exact le_of_mul_le_mul_left key hpos
  have hd : 80 * A ≤ 640 * P := by
    have h1 : A * u ^ 4 ≤ (8 * P) * u ^ 4 := by nlinarith
    have h2 : A ≤ 8 * P := le_of_mul_le_mul_right h1 (pow_pos hu0 4)
    linarith
  have hinner : L + 8 * R * L * H ^ 2 + 16 * H + 20 * R * L * H * A + 80 * A ≤ 781 * P := by
    nlinarith
  have hinner0 : (0 : ℝ) ≤ L + 8 * R * L * H ^ 2 + 16 * H + 20 * R * L * H * A + 80 * A := by
    have hH0' : (0 : ℝ) ≤ H := hH0.le
    positivity
  have houter : L + H ≤ 3 * P := by nlinarith
  have hprod : (L + H) * (L + 8 * R * L * H ^ 2 + 16 * H + 20 * R * L * H * A + 80 * A)
      ≤ (3 * P) * (781 * P) := mul_le_mul houter hinner hinner0 (by positivity)
  have hHX : H * X ^ 2 ≤ 2343 * P ^ 2 := by nlinarith
  have hX2 : X ^ 2 ≤ 2343 * P * u ^ 2 := by
    have h1 : P * X ^ 2 ≤ (H * u ^ 2) * X ^ 2 := mul_le_mul_of_nonneg_right hHlo (sq_nonneg X)
    have h3 : u ^ 2 * (H * X ^ 2) ≤ u ^ 2 * (2343 * P ^ 2) :=
      mul_le_mul_of_nonneg_left hHX (by positivity)
    have h4 : P * X ^ 2 ≤ P * (2343 * P * u ^ 2) :=
      calc P * X ^ 2 ≤ (H * u ^ 2) * X ^ 2 := h1
        _ = u ^ 2 * (H * X ^ 2) := by ring
        _ ≤ u ^ 2 * (2343 * P ^ 2) := h3
        _ = P * (2343 * P * u ^ 2) := by ring
    exact le_of_mul_le_mul_left h4 hP0
  have hsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP0.le
  have hY0 : (0 : ℝ) ≤ 60 * Real.sqrt P * u := by positivity
  have hle : X ^ 2 ≤ (60 * Real.sqrt P * u) ^ 2 := by
    have hexp : (60 * Real.sqrt P * u) ^ 2 = 3600 * P * u ^ 2 := by
      rw [mul_pow, mul_pow, hsq]; ring
    rw [hexp]
    nlinarith [mul_pos hP0 (pow_pos hu0 2)]
  have hfin := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hX0, Real.sqrt_sq hY0] at hfin

set_option maxHeartbeats 1000000 in
-- The numerical substitutions below are heavy; they need more than the default budget.
/-- **The third derivative test on a block, up to `M ≤ u⁴`.** -/
theorem norm_sum_e2pi_logPhase_block_le_quartic {M L : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ u ^ 4) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set P : ℝ := (M : ℝ) with hPdef
  have hP0 : (0 : ℝ) < P := by nlinarith
  have hLP : (L : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hLM
  set c : ℝ := u ^ 6 / (2 * Real.pi) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set H : ℕ := ⌈P / u ^ 2⌉₊ with hHdef
  have hHlo : P ≤ (H : ℝ) * u ^ 2 := by
    have h := Nat.le_ceil (P / u ^ 2)
    rw [← hHdef] at h
    rw [div_le_iff₀ (by positivity)] at h
    exact h
  have hHhi : (H : ℝ) * u ^ 2 ≤ 2 * P := by
    have h1 : (H : ℝ) < P / u ^ 2 + 1 := by
      rw [hHdef]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : (H : ℝ) * u ^ 2 < (P / u ^ 2 + 1) * u ^ 2 :=
      mul_lt_mul_of_pos_right h1 (by positivity)
    have h3 : (P / u ^ 2 + 1) * u ^ 2 = P + u ^ 2 := by field_simp
    rw [h3] at h2
    nlinarith
  have hHpos : 0 < H := Nat.ceil_pos.mpr (by positivity)
  -- the trivial bound suffices when the block is shorter than the number of shifts
  rcases lt_or_ge L H with hLH | hHL
  · have htriv : ‖∑ j ∈ range L, e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log (P + (j : ℝ)))‖
        ≤ (L : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      simp [KusminLandau.norm_e2pi]
    refine htriv.trans ?_
    have hLH' : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH.le
    have hsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP0.le
    have hsP : Real.sqrt P ≤ u ^ 3 := by
      have h1 : P ≤ (u ^ 3) ^ 2 := by nlinarith [pow_pos hu0 3, pow_pos hu0 4, hu0.le]
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at this
    have hsP0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
    -- `L ≤ H ≤ 2P/u²` and `2P ≤ 60 √P u³`
    have hkey : (H : ℝ) * u ^ 2 ≤ (60 * Real.sqrt P * u) * u ^ 2 := by
      have hPeq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
      have h2P : 2 * P ≤ (60 * Real.sqrt P * u) * u ^ 2 := by
        nlinarith [pow_pos hu0 3, mul_le_mul_of_nonneg_left hsP hsP0, hu0.le]
      linarith
    have hstep : (L : ℝ) * u ^ 2 ≤ (60 * Real.sqrt P * u) * u ^ 2 :=
      (mul_le_mul_of_nonneg_right hLH' (by positivity)).trans hkey
    exact le_of_mul_le_mul_right hstep (by positivity)
  -- the main case: apply the third-derivative test
  set r : ℝ := c / (4 * P ^ 3) with hrdef
  set R : ℝ := 2 * c / P ^ 3 with hRdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hrP : r * P ^ 3 = u ^ 6 / (8 * Real.pi) := by
    rw [hrdef, hc]; field_simp; ring
  have hRP : R * P ^ 3 = u ^ 6 / Real.pi := by
    rw [hRdef, hc]; field_simp
  have hRb : R * P ^ 3 * 3 ≤ u ^ 6 := by
    rw [hRP, div_mul_eq_mul_div, div_le_iff₀ hpi]
    nlinarith [pow_pos hu0 6]
  -- the points of the block are positive and at most `2P`
  have hxpos : ∀ x ∈ Set.Icc P (P + (L : ℝ)), 0 < x := fun x hx => lt_of_lt_of_le hP0 hx.1
  have hxle : ∀ x ∈ Set.Icc P (P + (L : ℝ)), x ≤ 2 * P := fun x hx => by
    have := hx.2; linarith
  have hmain := VanDerCorputThird.norm_sq_sum_e2pi_le_of_deriv_three
    (f := fun x => c * Real.log x) (f' := fun x => c * x⁻¹)
    (f'' := fun x => -c * (x ^ 2)⁻¹) (f''' := fun x => 2 * c * (x ^ 3)⁻¹)
    (a := P) (N := L) (H := H) (r := r) (R := R) hHpos hHL ?_ ?_ ?_ hr0 ?_ ?_ ?_
  rotate_left
  · intro x hx
    exact (Real.hasDerivAt_log (ne_of_gt (hxpos x hx))).const_mul c
  · intro x hx
    have h := (hasDerivAt_inv (ne_of_gt (hxpos x hx))).const_mul c
    exact h.congr_deriv (by ring)
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hxpos x hx)
    have h := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).const_mul (-c)
    refine h.congr_deriv ?_
    field_simp
    ring
  · -- `H r ≤ 1`
    have hsize : u ^ 4 ≤ 4 * Real.pi * P ^ 2 := by
      nlinarith [mul_le_mul hM hM (by positivity : (0 : ℝ) ≤ 30 * u ^ 2) hP0.le,
        pow_pos hu0 4, hpi3]
    have h1 : (H : ℝ) * u ^ 2 * (r * P ^ 3) ≤ (2 * P) * (r * P ^ 3) :=
      mul_le_mul_of_nonneg_right hHhi (by positivity)
    have h2 : (2 * P) * (r * P ^ 3) ≤ 1 * (u ^ 2 * P ^ 3) := by
      rw [hrP, one_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 2 * P * u ^ 2)]
    have hkey : (H : ℝ) * r * (u ^ 2 * P ^ 3) ≤ 1 * (u ^ 2 * P ^ 3) := by
      calc (H : ℝ) * r * (u ^ 2 * P ^ 3) = (H : ℝ) * u ^ 2 * (r * P ^ 3) := by ring
        _ ≤ (2 * P) * (r * P ^ 3) := h1
        _ ≤ 1 * (u ^ 2 * P ^ 3) := h2
    exact le_of_mul_le_mul_right hkey (by positivity)
  · intro x hx
    have hxp := hxpos x hx
    have hx2 := hxle x hx
    have hx3 : x ^ 3 ≤ 8 * P ^ 3 := by nlinarith [pow_le_pow_left₀ hxp.le hx2 3]
    have hinv : (8 * P ^ 3)⁻¹ ≤ (x ^ 3)⁻¹ := by
      apply inv_anti₀ (by positivity) hx3
    have heq : r = 2 * c * (8 * P ^ 3)⁻¹ := by rw [hrdef]; field_simp; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  · intro x hx
    have hxp := hxpos x hx
    have hxge : P ≤ x := hx.1
    have hx3 : P ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hP0.le hxge 3
    have hinv : (x ^ 3)⁻¹ ≤ (P ^ 3)⁻¹ := by
      apply inv_anti₀ (by positivity) hx3
    have heq : R = 2 * c * (P ^ 3)⁻¹ := by rw [hRdef]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  -- turn the bound on the squared norm into the bound on the norm
  set A : ℝ := Real.sqrt H / Real.sqrt r with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hAsq : A ^ 2 = (H : ℝ) / r := by
    rw [hAdef, div_pow, Real.sq_sqrt (Nat.cast_nonneg H), Real.sq_sqrt hr0.le]
  have hAb : A * u ^ 4 ≤ 8 * P ^ 2 := by
    have hbound : A ≤ 8 * P ^ 2 / u ^ 4 := by
      have hle : A ^ 2 ≤ (8 * P ^ 2 / u ^ 4) ^ 2 := by
        rw [hAsq, div_le_iff₀ hr0]
        have hrhs : ((8 * P ^ 2 / u ^ 4) ^ 2 * r) * (u ^ 8 * P ^ 3)
            = 64 * P ^ 4 * (r * P ^ 3) := by field_simp; ring
        have hstep : (H : ℝ) * (u ^ 8 * P ^ 3)
            ≤ ((8 * P ^ 2 / u ^ 4) ^ 2 * r) * (u ^ 8 * P ^ 3) := by
          rw [hrhs, hrP, mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hHhi
              (by positivity : (0 : ℝ) ≤ 8 * Real.pi * (u ^ 6 * P ^ 3)),
            mul_le_mul_of_nonneg_right hpi4 (by positivity : (0 : ℝ) ≤ 16 * P ^ 4 * u ^ 6)]
        exact le_of_mul_le_mul_right hstep (by positivity)
      have hfin := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hA0, Real.sqrt_sq (by positivity)] at hfin
    rwa [le_div_iff₀ (by positivity : (0 : ℝ) < u ^ 4)] at hbound
  have hconj : ∑ j ∈ range L, e2pi (-c * Real.log (P + (j : ℝ)))
      = (starRingEnd ℂ) (∑ j ∈ range L, e2pi (c * Real.log (P + (j : ℝ)))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [← VanDerCorputSums.e2pi_neg]; congr 1; ring
  rw [hconj, RCLike.norm_conj]
  refine block_bound_numeric_quartic (P := P) (L := (L : ℝ)) (H := (H : ℝ)) (R := R) (A := A)
    (u := u) hu hM hMu (Nat.cast_nonneg L) hLP (by exact_mod_cast hHpos) hHlo hHhi hR0 hRb
    hA0 hAb (norm_nonneg _) ?_
  refine hmain.trans_eq ?_
  rw [hAdef]
  ring

/-! ## The second derivative test in the middle range `u⁴ ≤ M ≤ 2u⁶` -/

/-- From `a² ≤ b²` with both sides nonnegative, `a ≤ b`. -/
private theorem le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith

set_option maxHeartbeats 1000000 in
-- The numerical chain below is heavy; it needs more than the default budget.
/-- **The second derivative test on a block**, in the range `u⁴ ≤ M ≤ 2u⁶`. -/
theorem norm_sum_e2pi_logPhase_block_le_mid {M L : ℕ} {u : ℝ} (hu : 10 ≤ u)
    (hM : u ^ 4 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ 2 * u ^ 6) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set c : ℝ := u ^ 6 / (2 * Real.pi) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hM0 : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  have hLM' : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hLM
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  set r : ℝ := c / (4 * (M : ℝ) ^ 2) with hrdef
  set R : ℝ := c / (M : ℝ) ^ 2 with hRdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  -- `6c ≤ u⁶ ≤ 8c`, the only two facts about `π` that are used
  have hcpi : c * (2 * Real.pi) = u ^ 6 := by rw [hc]; field_simp
  have hchi : 6 * c ≤ u ^ 6 := by nlinarith [hc0.le]
  have hclo : u ^ 6 ≤ 8 * c := by nlinarith [hc0.le]
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    have hM2 : u ^ 8 ≤ (M : ℝ) ^ 2 := by nlinarith [pow_pos hu0 4]
    nlinarith [pow_pos hu0 6, pow_pos hu0 8]
  -- the points of the block lie in `[M, 2M]`
  have hxpos : ∀ x ∈ Set.Icc ((M : ℝ)) ((M : ℝ) + (L : ℝ)), 0 < x := fun x hx =>
    lt_of_lt_of_le hM0 hx.1
  have hxle : ∀ x ∈ Set.Icc ((M : ℝ)) ((M : ℝ) + (L : ℝ)), x ≤ 2 * (M : ℝ) := fun x hx => by
    have := hx.2; linarith
  have hmain := VanDerCorputSums.norm_sum_e2pi_le_of_deriv_two
    (f := fun x => -c * Real.log x) (g := fun x => -c * x⁻¹) (g' := fun x => c * (x ^ 2)⁻¹)
    (a := (M : ℝ)) (L := L) (r := r) (R := R) hr0 hr1 ?_ ?_ ?_ ?_
  rotate_left
  · intro x hx
    exact (Real.hasDerivAt_log (ne_of_gt (hxpos x hx))).const_mul (-c)
  · intro x hx
    have h := (hasDerivAt_inv (ne_of_gt (hxpos x hx))).const_mul (-c)
    exact h.congr_deriv (by ring)
  · intro x hx
    have hxp := hxpos x hx
    have hx2 := hxle x hx
    have hsq : x ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by nlinarith
    have hinv : (4 * (M : ℝ) ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
    have : r = c * (4 * (M : ℝ) ^ 2)⁻¹ := by rw [hrdef]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hinv hc0.le
  · intro x hx
    have hxp := hxpos x hx
    have hsq : (M : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
    have hinv : (x ^ 2)⁻¹ ≤ ((M : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
    have : R = c * ((M : ℝ) ^ 2)⁻¹ := by rw [hRdef]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hinv hc0.le
  refine le_trans hmain ?_
  -- the numerical part
  set S : ℝ := Real.sqrt M with hSdef
  set sc : ℝ := Real.sqrt c with hscdef
  have hS0 : 0 < S := Real.sqrt_pos.mpr hM0
  have hS2 : S ^ 2 = (M : ℝ) := Real.sq_sqrt hM0.le
  have hsc0 : 0 < sc := Real.sqrt_pos.mpr hc0
  have hsc2 : sc ^ 2 = c := Real.sq_sqrt hc0.le
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hM0
  have hscne : sc ≠ 0 := ne_of_gt hsc0
  have hSu : u ^ 2 ≤ S := by
    refine le_of_sq_le_sq hS0.le ?_
    nlinarith [hS2, hM]
  have hsqrtr : Real.sqrt r = sc / (2 * (M : ℝ)) := by
    have hval : r = (sc / (2 * (M : ℝ))) ^ 2 := by
      rw [div_pow, hsc2, hrdef]; ring
    rw [hval, Real.sqrt_sq (by positivity)]
  have hRL : R * (L : ℝ) ≤ c / (M : ℝ) := by
    rw [hRdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hM0]
    nlinarith [mul_nonneg (mul_nonneg hc0.le hM0.le) (sub_nonneg.mpr hLM')]
  have hSsc : S ≤ 4 * sc := by
    refine le_of_sq_le_sq (by positivity) ?_
    nlinarith [hS2, hsc2, hclo]
  have hcsc : c / sc = sc := by
    rw [div_eq_iff hscne, ← pow_two, hsc2]
  have hA : 4 * (c / (M : ℝ)) ≤ (2 / 3) * u ^ 2 := by
    have h1 : c / (M : ℝ) ≤ u ^ 2 / 6 := by
      rw [div_le_div_iff₀ hM0 (by norm_num)]
      nlinarith [hchi, mul_le_mul_of_nonneg_left hM (le_of_lt (pow_pos hu0 2))]
    linarith
  have hB : 20 * sc ≤ 9 * u ^ 3 := by
    refine le_of_sq_le_sq (by positivity) ?_
    nlinarith [hsc2, hchi]
  have hC : 40 * ((M : ℝ) / sc) ≤ 160 * S := by
    have h1 : (M : ℝ) / sc ≤ 4 * S := by
      rw [div_le_iff₀ hsc0]
      nlinarith [hS2, mul_nonneg hS0.le (sub_nonneg.mpr hSsc)]
    linarith
  have hexp : 2 * (R * (L : ℝ) + 2) * (2 + 5 / Real.sqrt r)
      ≤ 4 * (c / (M : ℝ)) + 20 * sc + 8 + 40 * ((M : ℝ) / sc) := by
    rw [hsqrtr]
    have h5 : (5 : ℝ) / (sc / (2 * (M : ℝ))) = 10 * ((M : ℝ) / sc) := by
      field_simp; ring
    rw [h5]
    have hid : 2 * (c / (M : ℝ) + 2) * (2 + 10 * ((M : ℝ) / sc))
        = 4 * (c / (M : ℝ)) + 20 * (c / sc) + 8 + 40 * ((M : ℝ) / sc) := by
      field_simp; ring
    have hmono : 2 * (R * (L : ℝ) + 2) * (2 + 10 * ((M : ℝ) / sc))
        ≤ 2 * (c / (M : ℝ) + 2) * (2 + 10 * ((M : ℝ) / sc)) := by
      have hnn : (0 : ℝ) ≤ 2 + 10 * ((M : ℝ) / sc) := by positivity
      nlinarith [hRL, hnn]
    rw [hid, hcsc] at hmono
    exact hmono
  refine le_trans hexp ?_
  have e1 : 160 * S ≤ 16 * (S * u) := by nlinarith [hS0.le]
  have e2 : 9 * u ^ 3 ≤ 9 * (S * u) := by nlinarith [hSu, hu0.le]
  have e3 : (2 / 3) * u ^ 2 ≤ S * u := by nlinarith [hSu, hu0.le, hS0.le]
  have e4 : (8 : ℝ) ≤ S * u := by nlinarith [hSu, hS0.le]
  nlinarith [hA, hB, hC, e1, e2, e3, e4]

/-! ## The Kusmin–Landau test in the long range `2u⁶ ≤ M ≤ u¹²` -/

set_option maxHeartbeats 1000000 in
-- The numerical chain below is heavy; it needs more than the default budget.
/-- **The Kusmin–Landau first derivative test on a block**, in the range `2u⁶ ≤ M ≤ u¹²`, where
the phase derivative `u⁶/2πx` is below `1/4π` and hence separated from every integer by itself. -/
theorem norm_sum_e2pi_logPhase_block_le_long {M L : ℕ} {u : ℝ} (hu : 10 ≤ u)
    (hM : 2 * u ^ 6 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set c : ℝ := u ^ 6 / (2 * Real.pi) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hM0 : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  have hS0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  -- `6c ≤ u⁶ ≤ 8c`, the only two facts about `π` that are used
  have hcpi : c * (2 * Real.pi) = u ^ 6 := by rw [hc]; field_simp
  have hchi : 6 * c ≤ u ^ 6 := by nlinarith [hc0.le]
  have hclo : u ^ 6 ≤ 8 * c := by nlinarith [hc0.le]
  have hcM : 12 * c ≤ (M : ℝ) := by nlinarith
  rcases Nat.eq_zero_or_pos L with rfl | hL0
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
  have hKM : (K : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hLM
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  set lam : ℝ := c / (2 * (M : ℝ)) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hxpos : ∀ x ∈ Set.Icc ((M : ℝ)) ((M : ℝ) + (K : ℝ)), 0 < x := fun x hx =>
    lt_of_lt_of_le hM0 hx.1
  have hxle : ∀ x ∈ Set.Icc ((M : ℝ)) ((M : ℝ) + (K : ℝ)), x ≤ 2 * (M : ℝ) := fun x hx => by
    have := hx.2; linarith
  have hmain := KusminLandau.norm_sum_e2pi_le_of_deriv_general
    (f := fun x => -c * Real.log x) (f' := fun x => -c * x⁻¹) (c := (M : ℝ)) (K := K)
    (lam := lam) hlam0 ?_ ?_ ?_
  rotate_left
  · intro x hx
    exact (Real.hasDerivAt_log (ne_of_gt (hxpos x hx))).const_mul (-c)
  · intro x hx m
    have hxp := hxpos x hx
    have hx2 := hxle x hx
    have hval : -c * x⁻¹ = -(c / x) := by field_simp
    have hcx0 : 0 < c / x := by positivity
    have hsmall : c / x ≤ 1 / 12 := by
      rw [div_le_div_iff₀ hxp (by norm_num)]
      nlinarith [hx.1]
    have hbig : lam ≤ c / x := by
      rw [hlamdef, div_le_div_iff₀ (by positivity) hxp]
      nlinarith [hc0.le]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [hval]
      simp only [Int.cast_zero, sub_zero, abs_neg, abs_of_pos hcx0]
      exact hbig
    · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
        calc (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(m : ℝ)| := by push_cast [Int.cast_abs]; ring
      have hlamsmall : lam ≤ 1 / 12 := by
        rw [hlamdef, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hc0.le]
      rw [hval]
      have := abs_sub_abs_le_abs_sub (-(c / x)) ((m : ℝ))
      have h2 : |-(c / x)| = c / x := by rw [abs_neg, abs_of_pos hcx0]
      rw [h2] at this
      have h3 : |(m : ℝ)| - c / x ≤ |-(c / x) - (m : ℝ)| := by
        have := abs_sub_abs_le_abs_sub ((m : ℝ)) (-(c / x))
        rw [h2] at this
        rw [abs_sub_comm]
        linarith
      linarith
  · left
    intro x hx y hy hxy
    have hxp := hxpos x hx
    have hyp := hxpos y hy
    simp only
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    have : y⁻¹ ≤ x⁻¹ := by
      exact inv_anti₀ hxp hxy
    exact mul_le_mul_of_nonneg_left this hc0.le
  refine le_trans hmain ?_
  -- the numerical part
  have hMK : (0 : ℝ) < (M : ℝ) + (K : ℝ) := by linarith
  have hvar : |(-c * ((M : ℝ) + (K : ℝ))⁻¹) - (-c * (M : ℝ)⁻¹)| ≤ 1 := by
    have heq : (-c * ((M : ℝ) + (K : ℝ))⁻¹) - (-c * (M : ℝ)⁻¹)
        = c / (M : ℝ) - c / ((M : ℝ) + (K : ℝ)) := by
      field_simp
      ring
    have h1 : c / ((M : ℝ) + (K : ℝ)) ≤ c / (M : ℝ) :=
      div_le_div_of_nonneg_left hc0.le hM0 (by linarith)
    have h2 : c / (M : ℝ) ≤ 1 := by
      rw [div_le_one hM0]; linarith
    have h3 : (0 : ℝ) ≤ c / ((M : ℝ) + (K : ℝ)) := by positivity
    rw [heq, abs_of_nonneg (by linarith)]
    linarith
  have hlaminv : 2 / lam = 4 * (M : ℝ) / c := by
    rw [hlamdef]; field_simp; ring
  have hstep : (|(-c * ((M : ℝ) + (K : ℝ))⁻¹) - (-c * (M : ℝ)⁻¹)| + 2) * (1 + 2 / lam)
      ≤ 3 * (1 + 4 * (M : ℝ) / c) := by
    rw [hlaminv]
    refine mul_le_mul_of_nonneg_right (by linarith) ?_
    positivity
  refine le_trans hstep ?_
  -- `3 (1 + 4M/c) ≤ 60 √M u`
  set S : ℝ := Real.sqrt M with hSdef
  have hS2 : S ^ 2 = (M : ℝ) := Real.sq_sqrt hM0.le
  have hSpos : 0 < S := hS0
  have hSu6 : S ≤ 2 * u ^ 6 := by
    refine le_of_sq_le_sq (by positivity) ?_
    nlinarith [hS2, hMu, pow_pos hu0 6, pow_pos hu0 12]
  have hS16 : S ≤ 16 * c := by linarith
  have hkey : 4 * (M : ℝ) / c ≤ 64 * S := by
    rw [div_le_iff₀ hc0]
    nlinarith [hS2, mul_nonneg hSpos.le (sub_nonneg.mpr hS16)]
  have h3 : (3 : ℝ) ≤ S := by
    refine le_of_sq_le_sq hSpos.le ?_
    nlinarith [hS2, hM, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10) hu 6]
  have e1 : 192 * S ≤ 20 * (S * u) := by nlinarith [hSpos.le]
  have e2 : (3 : ℝ) ≤ S * u := by nlinarith [hSpos.le]
  nlinarith [hkey, e1, e2]

/-- **The block estimate in the whole range `30u² ≤ M ≤ u¹²`.** -/
theorem norm_sum_e2pi_logPhase_block_le_all {M L : ℕ} {u : ℝ} (hu : 10 ≤ u)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u := by
  rcases le_or_gt ((M : ℝ)) (u ^ 4) with h4 | h4
  · exact norm_sum_e2pi_logPhase_block_le_quartic (by linarith) hM h4 hLM
  rcases le_or_gt ((M : ℝ)) (2 * u ^ 6) with h6 | h6
  · exact norm_sum_e2pi_logPhase_block_le_mid hu h4.le h6 hLM
  · exact norm_sum_e2pi_logPhase_block_le_long hu h6.le hMu hLM

/-- The block of the Dirichlet polynomial of `ζ` on the critical line, in the whole range. -/
theorem norm_sum_block_criticalLine_le_all {M L : ℕ} {u : ℝ} (hu : 10 ≤ u)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, ((M + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I))‖ ≤ 60 * u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by nlinarith
  set w : ℕ → ℝ := fun j => ((M : ℝ) + j) ^ (-(1 / 2) : ℝ) with hwdef
  set z : ℕ → ℂ := fun j => e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + j)) with hzdef
  have hpos : ∀ j : ℕ, (0 : ℝ) < (M : ℝ) + j := fun j => by positivity
  have hterm : ∀ j ∈ range L,
      ((M + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)) = (w j : ℂ) * z j := by
    intro j _
    have hcast : ((M + j : ℕ) : ℂ) = (((M : ℝ) + (j : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, cpow_criticalLine_eq (hpos j)]
  rw [Finset.sum_congr rfl hterm]
  have hnn : ∀ i, 0 ≤ w i := fun i => Real.rpow_nonneg (hpos i).le _
  have hanti : ∀ i j : ℕ, i ≤ j → w j ≤ w i := by
    intro i j hij
    have hle : (M : ℝ) + i ≤ (M : ℝ) + j := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    exact Real.rpow_le_rpow_of_nonpos (hpos i) hle (by norm_num)
  have hB : ∀ l, l ≤ L → ‖∑ j ∈ range l, z j‖ ≤ 60 * Real.sqrt M * u := fun l hl =>
    norm_sum_e2pi_logPhase_block_le_all hu hM hMu (le_trans hl hLM)
  refine (norm_sum_weighted_le hnn hanti hB).trans_eq ?_
  have hw0 : w 0 = (Real.sqrt M)⁻¹ := by
    rw [hwdef]
    simp only [Nat.cast_zero, add_zero]
    rw [Real.rpow_neg hM0.le, Real.sqrt_eq_rpow]
  rw [hw0]
  field_simp

/-- Summing the block bound over dyadic blocks up to length `N ≤ u¹² = t²`. -/
theorem norm_zetaSum_le_of_le_pow_twelve {N : ℕ} {u : ℝ} (hu : 10 ≤ u)
    (hN : (N : ℝ) ≤ 2 * u ^ 12) :
    ‖zetaSum N (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)‖ ≤ 60 * u * (Nat.log 2 N + 1) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ 2 * u ^ 12 →
      ‖zetaSum n (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)‖ ≤ 60 * u * (Nat.log 2 n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hlog0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
      by_cases hsmall : (n : ℝ) < 60 * u ^ 2
      · refine (norm_zetaSum_criticalLine_le n (u ^ 6)).trans ?_
        have h1 : Real.sqrt n ≤ 30 * u := by
          have hle : (n : ℝ) ≤ (30 * u) ^ 2 := by nlinarith
          have h := Real.sqrt_le_sqrt hle
          rwa [Real.sqrt_sq (by positivity)] at h
        nlinarith
      · rw [not_lt] at hsmall
        have hn60 : (60 : ℝ) ≤ (n : ℝ) := by nlinarith
        have hn2 : 2 ≤ n := by
          have : (2 : ℝ) ≤ (n : ℝ) := by linarith
          exact_mod_cast this
        set K : ℕ := n / 2 with hKdef
        have hKn : K < n := Nat.div_lt_self (by omega) (by norm_num)
        have hKle : K + 1 ≤ n := by omega
        have hKtwice : n ≤ 2 * K + 1 := by omega
        have hKcast : (K : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hKle
        have hKu : (K : ℝ) ≤ 2 * u ^ 12 := le_trans (by exact_mod_cast hKn.le) hn
        have hIH := ih K hKn hKu
        have hsplit : zetaSum n (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)
            = zetaSum K (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)
              + ∑ j ∈ range (n - K),
                  ((K + 1 + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)) := by
          rw [zetaSum, zetaSum, ← Finset.Ico_add_one_right_eq_Icc,
            ← Finset.Ico_add_one_right_eq_Icc,
            ← Finset.sum_Ico_consecutive
              (fun m => ((m : ℂ)) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)))
              (by omega : 1 ≤ K + 1) (by omega : K + 1 ≤ n + 1)]
          congr 1
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_add_right]
        have hblock : ‖∑ j ∈ range (n - K),
            ((K + 1 + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I))‖ ≤ 60 * u := by
          refine norm_sum_block_criticalLine_le_all (M := K + 1) (L := n - K) hu ?_ ?_ (by omega)
          · have : (n : ℝ) ≤ 2 * (K : ℝ) + 1 := by exact_mod_cast hKtwice
            push_cast
            nlinarith
          · push_cast
            linarith [hKcast, hn]
        have hlogn : Nat.log 2 n = Nat.log 2 K + 1 :=
          Nat.log_of_one_lt_of_le (by norm_num) hn2
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [hlogn]
        have hcast : ((Nat.log 2 K + 1 : ℕ) : ℝ) = (Nat.log 2 K : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith [hIH, hblock]
  exact key N hN

/-! ## The Euler–Maclaurin error at length `t²` -/

/-- One step of the telescoping bound: `(x+1)^(-3/2) ≤ 2/√x - 2/√(x+1)` for `x ≥ 1`. -/
private theorem rpow_neg_three_halves_le_sub (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ (-(3 / 2) : ℝ) ≤ 2 / Real.sqrt x - 2 / Real.sqrt (x + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set a : ℝ := Real.sqrt x with hadef
  set b : ℝ := Real.sqrt (x + 1) with hbdef
  have ha0 : 0 < a := Real.sqrt_pos.mpr hx0
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcube : (x + 1) ^ (-(3 / 2) : ℝ) = (b ^ 3)⁻¹ := by
    rw [show (-(3 / 2) : ℝ) = (1 / 2 : ℝ) * (-3 : ℝ) by norm_num,
      Real.rpow_mul (by linarith), ← Real.sqrt_eq_rpow,
      show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast]
  rw [hcube]
  have h2 : (b - a) * (b + a) = 1 := by nlinarith
  have h4 : a * b * (a + b) ≤ 2 * b ^ 3 := by nlinarith
  have h5 : a * b ≤ 2 * (b - a) * b ^ 3 := by
    have hs : (0 : ℝ) < a + b := by linarith
    refine le_of_mul_le_mul_right ?_ hs
    have heq : 2 * (b - a) * b ^ 3 * (a + b) = 2 * b ^ 3 * ((b - a) * (b + a)) := by ring
    rw [heq, h2]
    linarith
  have hsub : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by
    field_simp
  rw [hsub, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h5]

/-- The tail of `∑ (n+1)^(-3/2)`, by telescoping. -/
theorem tsum_shift_rpow_neg_three_halves_le (N : ℕ) (hN : 0 < N) :
    ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) ≤ 2 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℕ → ℝ := fun i => 2 / Real.sqrt ((i : ℝ) + (N : ℝ)) with hfdef
  have hterm : ∀ i : ℕ, (((i + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) ≤ f i - f (i + 1) := by
    intro i
    have hcast : ((i + N : ℕ) : ℝ) = (i : ℝ) + (N : ℝ) := by push_cast; ring
    have hx : (1 : ℝ) ≤ (i : ℝ) + (N : ℝ) := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have h := rpow_neg_three_halves_le_sub ((i : ℝ) + (N : ℝ)) hx
    rw [hcast]
    refine h.trans (le_of_eq ?_)
    rw [hfdef]
    congr 2
    push_cast
    ring
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  calc ∑ n ∈ range M, (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ)
      ≤ ∑ n ∈ range M, (f n - f (n + 1)) := Finset.sum_le_sum fun n _ => hterm n
    _ = f 0 - f M := Finset.sum_range_sub' f M
    _ ≤ 2 / Real.sqrt N := by
        have hf0 : f 0 = 2 / Real.sqrt N := by rw [hfdef]; norm_num
        have hfM : 0 ≤ f M := by rw [hfdef]; positivity
        rw [hf0]
        linarith

/-- **The Euler–Maclaurin error.**  At length `N` between `t²` and `2t²`, the Riemann zeta function
on the critical line differs from its Dirichlet polynomial of length `N` by at most `10`. -/
theorem norm_riemannZeta_sub_zetaSum_le {N : ℕ} {t : ℝ} (ht : 2 ≤ t) (hN : t ^ 2 ≤ (N : ℝ))
    (hN2 : (N : ℝ) ≤ 2 * t ^ 2) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum N (1 / 2 + (t : ℂ) * I)‖ ≤ 10 := by
  have ht0 : (0 : ℝ) < t := by linarith
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hsim] at this
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  -- the Euler–Maclaurin representation
  have hzeta := riemannZeta_eq_zetaApprox_of_pos_re N hs0 hs1
  -- the Dirichlet polynomial in the two shapes
  have hpoly : ∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s) = zetaSum N s := by
    rw [zetaSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  -- the polar term
  have hpolar : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 2 := by
    have hnum : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      congr 1
      simp [hs]
      norm_num
    have hden : t ≤ ‖s - 1‖ := by
      have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
      have him : (s - 1).im = t := by simp [hs]
      rw [him, abs_of_pos ht0] at this
      exact this
    have hnum2 : ((N : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ 2 * t := by
      rw [show (1 / 2 : ℝ) = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]
      have h1 : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (4 * t ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      refine h1.trans (le_of_eq ?_)
      rw [show (4 : ℝ) * t ^ 2 = (2 * t) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [norm_div, hnum, div_le_iff₀ (lt_of_lt_of_le ht0 hden)]
    nlinarith [hnum2, hden, ht0]
  -- the tail
  have hsummable : Summable (fun n : ℕ => eulerTerm (n + N) s) :=
    (summable_eulerTerm hs0 hs1).comp_injective (add_left_injective N)
  have hbound : ∀ n : ℕ,
      ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
    intro n
    have h := norm_eulerTerm_le (n + N) hs0.le hs1
    rw [hsre] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    norm_num
  have hsummable_bound : Summable
      (fun n : ℕ => ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
    refine Summable.mul_left _ ?_
    exact (summable_natAddOne_rpow_neg (p := 3 / 2) (by norm_num)).comp_injective
      (add_left_injective N)
  have hsummable_norm : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsummable_bound
  have htail : ‖∑' n : ℕ, eulerTerm (n + N) s‖ ≤ ‖s‖ * (2 / Real.sqrt N) := by
    refine (norm_tsum_le_tsum_norm hsummable_norm).trans ?_
    refine (hsummable_norm.tsum_le_tsum hbound hsummable_bound).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_shift_rpow_neg_three_halves_le N hNpos)
      (norm_nonneg _)
  have hnorms : ‖s‖ ≤ 1 + t := by
    have h1 : ‖s‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := by rw [hs]; exact norm_add_le _ _
    have h2 : ‖(t : ℂ) * I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2, h3] at h1
    linarith
  have hsqrtN : t ≤ Real.sqrt N := by
    have h1 : Real.sqrt (t ^ 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt hN
    rwa [Real.sqrt_sq ht0.le] at h1
  have htail2 : ‖s‖ * (2 / Real.sqrt N) ≤ 8 := by
    have h1 : (2 : ℝ) / Real.sqrt N ≤ 2 / t := by
      apply div_le_div_of_nonneg_left (by norm_num) ht0 hsqrtN
    have h2 : ‖s‖ * (2 / Real.sqrt N) ≤ (1 + t) * (2 / t) := by
      refine mul_le_mul hnorms h1 (by positivity) (by linarith)
    have h3 : (1 + t) * (2 / t) = 2 / t + 2 := by field_simp
    rw [h3] at h2
    have h4 : (2 : ℝ) / t ≤ 1 := by
      rw [div_le_one ht0]; linarith
    linarith
  -- put the pieces together
  have hsplit : riemannZeta s - zetaSum N s
      = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ∑' n : ℕ, eulerTerm (n + N) s := by
    rw [hzeta]
    unfold zetaApprox
    rw [hpoly]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith [hpolar, htail, htail2]

/-- **Unconditional subconvexity on the critical line**: `‖ζ(1/2+it)‖ ≤ 200 t^(1/6) (log t + 1)`
for `t ≥ 10⁹`.  This is the classical Weyl–Hardy–Littlewood exponent `1/6`, with no hypothesis. -/
theorem norm_riemannZeta_criticalLine_le {t : ℝ} (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ 200 * t ^ ((1 : ℝ) / 6) * (Real.log t + 1) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  set u : ℝ := t ^ ((1 : ℝ) / 6) with hudef
  have hu6 : u ^ 6 = t := by
    rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul ht0.le]
    norm_num
  have hu10 : 10 ≤ u := by
    have hbase : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) = 10 := by
      rw [← Real.rpow_natCast (10 : ℝ) 6, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h1 : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) ≤ ((10 : ℝ) ^ 9) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    have h2 : ((10 : ℝ) ^ 9) ^ ((1 : ℝ) / 6) ≤ u :=
      Real.rpow_le_rpow (by positivity) ht (by norm_num)
    rw [hbase] at h1
    linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hu12 : u ^ 12 = t ^ 2 := by
    have : u ^ 12 = (u ^ 6) ^ 2 := by ring
    rw [this, hu6]
  -- the length of the Dirichlet polynomial
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have hNlo : t ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) < t ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN2 : (N : ℝ) ≤ 2 * t ^ 2 := by nlinarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast this
  -- the Dirichlet polynomial
  have hzs : ‖zetaSum N (1 / 2 + (t : ℂ) * I)‖ ≤ 60 * u * (Nat.log 2 N + 1) := by
    have h := norm_zetaSum_le_of_le_pow_twelve (N := N) (u := u) hu10 (by rw [hu12]; exact hN2)
    rwa [hu6] at h
  -- the Euler–Maclaurin error
  have hem := norm_riemannZeta_sub_zetaSum_le (N := N) ht2 hNlo hN2
  -- the number of dyadic blocks
  have hlogN : ((Nat.log 2 N : ℕ) : ℝ) ≤ 1 + 2.887 * Real.log t := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N) := by positivity
    have hlogle : Real.log ((2 : ℝ) ^ (Nat.log 2 N)) ≤ Real.log (2 * t ^ 2) :=
      Real.log_le_log h2pos (hpow.trans hN2)
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogle
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at hlogle
    nlinarith [hlogle, hl2, hnn, hlogt]
  -- combine
  have hsplit : riemannZeta (1 / 2 + (t : ℂ) * I)
      = (riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum N (1 / 2 + (t : ℂ) * I))
        + zetaSum N (1 / 2 + (t : ℂ) * I) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hblocks : 60 * u * ((Nat.log 2 N : ℝ) + 1) ≤ 120 * u + 173.22 * u * Real.log t := by
    nlinarith [hlogN, hu0, hlogt]
  have hfinal : 10 + (120 * u + 173.22 * u * Real.log t) ≤ 200 * u * (Real.log t + 1) := by
    nlinarith [hu10, hlogt, hu0]
  have hcast : ((Nat.log 2 N : ℕ) : ℝ) + 1 = ((Nat.log 2 N : ℕ) : ℝ) + 1 := rfl
  calc ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum N (1 / 2 + (t : ℂ) * I)‖
        + ‖zetaSum N (1 / 2 + (t : ℂ) * I)‖
      ≤ 10 + 60 * u * ((Nat.log 2 N : ℝ) + 1) := by
        linarith [hem, hzs]
    _ ≤ 10 + (120 * u + 173.22 * u * Real.log t) := by linarith
    _ ≤ 200 * u * (Real.log t + 1) := hfinal

end SubconvexityUnconditional

end RiemannHypothesis

end
