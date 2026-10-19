/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.VanDerCorputThird
import RiemannHypothesis.ApproximateFunctionalEquation

/-!
# Subconvexity on the critical line from the approximate functional equation

`RiemannHypothesis.ApproximateFunctionalEquation` records the approximate functional equation of
Hardy and Littlewood as a `Prop`, `AFECriticalLine C`, and derives from it — using only the
*trivial* bound `‖∑_{n ≤ N} n^(-1/2-it)‖ ≤ 2√N` for the two Dirichlet polynomials — the log-free
convexity bound `‖ζ(1/2+it)‖ ≤ (C+4) t^(1/4)`.

This file replaces the trivial bound by a genuine cancellation estimate.  Van der Corput's
third-derivative test (`RiemannHypothesis.VanDerCorputThird`), applied to the phase
`x ↦ (t/2π) log x` on a dyadic block, gives `‖∑_{M ≤ n < M+L} n^(-1/2-it)‖ ≪ t^(1/6)` uniformly
for `t^(1/3) ≪ M ≤ √t`, and summing `O(log t)` such blocks bounds the whole Dirichlet polynomial
of length `√(t/2π)`.  Together with the approximate functional equation this is the classical
subconvexity exponent `1/6` of Hardy and Littlewood.  The approximate functional equation is now
a theorem (`afeCriticalLine : AFECriticalLine 250`, `RiemannHypothesis.AFECriticalLineProof`), so
the hypothesis of the last theorem below can be discharged; the exponent `1/6` for `ζ` is also
proved without it in `RiemannHypothesis.SubconvexityUnconditional`.

## Main results

All of the following are **unconditional** except the last one.

* `norm_sum_weighted_le` — Abel summation: if every prefix of `∑ z j` has norm at most `B` and the
  weights `w` are nonnegative and nonincreasing, then `‖∑_{j<L} w j z j‖ ≤ w 0 · B`.
* `block_bound_numeric` — the arithmetic core: the conclusion of the third-derivative test with
  `H ≈ M/u²`, `R ≈ u⁶/M³` and `√H/√r ≈ M²/u⁴` substituted, rearranged into `X ≤ 60 √M u`.
* `norm_sum_e2pi_logPhase_block_le` — the exponential sum with phase `−(u⁶/2π) log x` over a block
  of length `L ≤ M` starting at `M` is at most `60 √M u`, for `30 u² ≤ M ≤ u³`.
* `cpow_criticalLine_eq` — the splitting `x^(-1/2-it) = x^(-1/2) · e(−(t/2π) log x)`.
* `norm_sum_block_criticalLine_le` — the block of the Dirichlet polynomial itself:
  `‖∑_{j<L} (M+j)^(-1/2-i u⁶)‖ ≤ 60 u` for `30 u² ≤ M ≤ u³`, `L ≤ M`.
* `norm_zetaSum_le_of_le_cube` — summing over dyadic blocks:
  `‖∑_{n ≤ N} n^(-1/2-i u⁶)‖ ≤ 60 u (log₂ N + 1)` for `N ≤ u³`.
* `norm_riemannZeta_criticalLine_le_of_afe` — **with `AFECriticalLine C` as hypothesis**,
  `‖ζ(1/2+it)‖ ≤ C + 120 t^(1/6) (log t + 1)` for `t ≥ 10⁹`; with `afeCriticalLine` this holds
  with `C = 250`.

The height parameter is written `u = t^(1/6)` throughout, so that every inequality that has to be
checked is polynomial in `u`.  The constants are not optimized; `60` is comfortably larger than
the `√2343 ≈ 48.4` that the argument actually produces.

## Hypothesis hygiene (AGENTS.md)

Only the last theorem takes a hypothesis, `AFECriticalLine C`, whose four hygiene questions are
answered in the module docstring of `RiemannHypothesis.ApproximateFunctionalEquation`; it is
proved for `C = 250` by `afeCriticalLine`.  Nothing in this file assumes anything else:
the block estimate, the Abel summation and the dyadic decomposition are proved outright.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace AFESubconvexity

open KusminLandau VanDerCorputThird

/-- **Abel summation.**  If every prefix of `∑ z j` has norm at most `B` and the weights `w` are
nonnegative and nonincreasing, then `‖∑_{j < L} w j z j‖ ≤ w 0 * B`. -/
theorem norm_sum_weighted_le {L : ℕ} {w : ℕ → ℝ} {z : ℕ → ℂ} {B : ℝ}
    (hnn : ∀ i, 0 ≤ w i) (hanti : ∀ i j : ℕ, i ≤ j → w j ≤ w i)
    (hB : ∀ l, l ≤ L → ‖∑ j ∈ range l, z j‖ ≤ B) :
    ‖∑ j ∈ range L, (w j : ℂ) * z j‖ ≤ w 0 * B := by
  have hsmul : ∀ j : ℕ, (w j : ℂ) * z j = w j • z j := by
    intro j; simp [Complex.real_smul]
  simp only [hsmul]
  rw [Finset.sum_range_by_parts w z L]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖w (L - 1) • ∑ i ∈ range L, z i‖ ≤ w (L - 1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    exact mul_le_mul_of_nonneg_left (hB L le_rfl) (hnn _)
  have h2 : ‖∑ i ∈ range (L - 1), (w (i + 1) - w i) • ∑ j ∈ range (i + 1), z j‖
      ≤ ∑ i ∈ range (L - 1), (w i - w (i + 1)) * B := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hstep : w (i + 1) ≤ w i := hanti i (i + 1) (Nat.le_succ i)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hb : ‖∑ j ∈ range (i + 1), z j‖ ≤ B := hB (i + 1) (by omega)
    calc -(w (i + 1) - w i) * ‖∑ j ∈ range (i + 1), z j‖
        = (w i - w (i + 1)) * ‖∑ j ∈ range (i + 1), z j‖ := by ring
      _ ≤ (w i - w (i + 1)) * B := mul_le_mul_of_nonneg_left hb (by linarith)
  have h3 : ∑ i ∈ range (L - 1), (w i - w (i + 1)) * B = (w 0 - w (L - 1)) * B := by
    rw [← Finset.sum_mul, Finset.sum_range_sub' w (L - 1)]
  rw [h3] at h2
  nlinarith [h1, h2]

set_option maxHeartbeats 1000000 in
-- The `nlinarith` chain below is heavy; it needs more than the default heartbeat budget.
/-- The arithmetic core of the block estimate: the shape of the third-derivative test with the
relevant sizes of `H`, `R` and `√H/√r` substituted. -/
theorem block_bound_numeric {P L H R A X u : ℝ} (hu : 1 ≤ u) (hP30 : 30 * u ^ 2 ≤ P)
    (hPu : P ≤ u ^ 3) (hL0 : 0 ≤ L) (hLP : L ≤ P)
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
    have h1 : (A * u) * u ^ 3 ≤ (8 * P) * u ^ 3 := by nlinarith [pow_pos hu0 3]
    have h2 : A * u ≤ 8 * P := le_of_mul_le_mul_right h1 (pow_pos hu0 3)
    nlinarith
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
/-- **The third-derivative test applied to the phase of `ζ` on a block.**  For
`30 u² ≤ M ≤ u³` and a block of length `L ≤ M` starting at `M`, the exponential sum with phase
`−(u⁶/2π) log x` is at most `60 √M u`. -/
theorem norm_sum_e2pi_logPhase_block_le {M L : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ u ^ 3) (hLM : L ≤ M) :
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
      have h1 : P ≤ (u ^ 3) ^ 2 := by nlinarith [pow_pos hu0 3]
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
  refine block_bound_numeric (P := P) (L := (L : ℝ)) (H := (H : ℝ)) (R := R) (A := A)
    (u := u) hu hM hMu (Nat.cast_nonneg L) hLP (by exact_mod_cast hHpos) hHlo hHhi hR0 hRb
    hA0 hAb (norm_nonneg _) ?_
  refine hmain.trans_eq ?_
  rw [hAdef]
  ring

/-- On the critical line the factor `x^(-1/2-it)` splits into the real weight `x^(-1/2)` and the
pure phase `e(−(t/2π) log x)`. -/
theorem cpow_criticalLine_eq {x t : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))
      = ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * e2pi (-(t / (2 * Real.pi)) * Real.log x) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    KusminLandau.e2pi, Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have h2 : ((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log x) : ℝ) : ℂ)
      = -((t : ℂ) * (Real.log x : ℂ)) := by push_cast; field_simp
  rw [h2]
  push_cast
  ring

/-- The block of the Dirichlet polynomial of `ζ` on the critical line, at height `t = u⁶`:
`‖∑_{j < L} (M + j)^(-1/2 - i u⁶)‖ ≤ 60 u` for `30 u² ≤ M ≤ u³` and `L ≤ M`. -/
theorem norm_sum_block_criticalLine_le {M L : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ u ^ 3) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, ((M + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I))‖ ≤ 60 * u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
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
    norm_sum_e2pi_logPhase_block_le hu hM hMu (le_trans hl hLM)
  refine (norm_sum_weighted_le hnn hanti hB).trans_eq ?_
  have hw0 : w 0 = (Real.sqrt M)⁻¹ := by
    rw [hwdef]
    simp only [Nat.cast_zero, add_zero]
    rw [Real.rpow_neg hM0.le, Real.sqrt_eq_rpow]
  rw [hw0]
  field_simp

/-- Summing the block bound over dyadic blocks: `‖∑_{n ≤ N} n^(-1/2 - i u⁶)‖ ≤ 60 u (log₂ N + 1)`
for `N ≤ u³`. -/
theorem norm_zetaSum_le_of_le_cube {N : ℕ} {u : ℝ} (hu : 1 ≤ u) (hN : (N : ℝ) ≤ u ^ 3) :
    ‖zetaSum N (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)‖ ≤ 60 * u * (Nat.log 2 N + 1) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have key : ∀ n : ℕ, (n : ℝ) ≤ u ^ 3 →
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
        have hKu : (K : ℝ) ≤ u ^ 3 := le_trans (by exact_mod_cast hKn.le) hn
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
          refine norm_sum_block_criticalLine_le (M := K + 1) (L := n - K) hu ?_ ?_ (by omega)
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

/-- **Conditionally on the approximate functional equation, the subconvexity bound
`‖ζ(1/2 + i t)‖ ≪ t^(1/6) log t` on the critical line.** -/
theorem norm_riemannZeta_criticalLine_le_of_afe {C : ℝ} (hafe : AFECriticalLine C) {t : ℝ}
    (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C + 120 * t ^ ((1 : ℝ) / 6) * (Real.log t + 1) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have ht1 : (1 : ℝ) ≤ t := by nlinarith
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  set u : ℝ := t ^ ((1 : ℝ) / 6) with hudef
  have hu1 : 1 ≤ u := Real.one_le_rpow ht1 (by norm_num)
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hu6 : u ^ 6 = t := by
    rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul ht0.le]
    norm_num
  have hu3 : u ^ 3 = Real.sqrt t := by
    rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul ht0.le,
      Real.sqrt_eq_rpow]
    norm_num
  -- the length of the two sums of the approximate functional equation is at most `√t = u³`
  have hNsqrt : ((afeLength t : ℕ) : ℝ) ≤ Real.sqrt t := by
    refine le_trans (Nat.floor_le (Real.sqrt_nonneg _)) (Real.sqrt_le_sqrt ?_)
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hNle : ((afeLength t : ℕ) : ℝ) ≤ u ^ 3 := by rw [hu3]; exact hNsqrt
  -- `log₂` of the length is at most `log t`
  have hlogN : ((Nat.log 2 (afeLength t) : ℕ) : ℝ) ≤ Real.log t := by
    rcases Nat.eq_zero_or_pos (afeLength t) with h0 | hpos
    · rw [h0]; simpa using hlogt
    · have hpow : (2 : ℝ) ^ (Nat.log 2 (afeLength t)) ≤ ((afeLength t : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 (afeLength t)) := by positivity
      have hlogle : Real.log ((2 : ℝ) ^ (Nat.log 2 (afeLength t)))
          ≤ Real.log (Real.sqrt t) := Real.log_le_log h2pos (hpow.trans hNsqrt)
      rw [Real.log_pow, Real.sqrt_eq_rpow, Real.log_rpow ht0] at hlogle
      have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 (afeLength t))]
  -- the two Dirichlet polynomials
  have hsum : ‖zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 60 * u * (Nat.log 2 (afeLength t) + 1) := by
    have h := norm_zetaSum_le_of_le_cube (N := afeLength t) hu1 hNle
    rwa [hu6] at h
  have hdual : ‖zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      = ‖zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)‖ := by
    rw [norm_mul, norm_zetaChi_criticalLine, one_mul, zetaSumDual_criticalLine, RCLike.norm_conj]
  have hafet := hafe t ht2
  have hquarter : (0 : ℝ) < t ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right hquarter).mp (le_trans (norm_nonneg _) hafet)
  have hCq : C * t ^ (-(1 / 4) : ℝ) ≤ C := by
    have hle : t ^ (-(1 / 4) : ℝ) ≤ t ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    rw [Real.rpow_zero] at hle
    nlinarith
  have hsplit : riemannZeta (1 / 2 + (t : ℂ) * I)
      = (riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
          - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I))
        + zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        + zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I) := by
    ring
  rw [hsplit]
  refine le_trans norm_add₃_le ?_
  rw [hdual]
  have hmul : 60 * u * ((Nat.log 2 (afeLength t) : ℝ) + 1) ≤ 60 * u * (Real.log t + 1) := by
    have := hlogN
    nlinarith
  linarith [hafet, hsum, hCq, hmul]

end AFESubconvexity

end RiemannHypothesis
