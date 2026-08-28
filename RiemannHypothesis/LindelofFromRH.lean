/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Criteria
import RiemannHypothesis.XiGrowth
import RiemannHypothesis.ZeroCountLocal
import RiemannHypothesis.ThreeCircles
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# The Lindelöf bound away from the critical line, under the Riemann hypothesis

Littlewood's theorem is that the Riemann hypothesis implies the Lindelöf hypothesis.  This file
proves the part of it that does not need the delicate choice of radii depending on the height:
for every fixed `δ > 0`, the Riemann hypothesis gives `ζ(σ + i t) = O_ε(t^ε)` uniformly for
`σ ≥ 1/2 + δ`.

## The argument

Under the Riemann hypothesis `ζ` has no zero with `re s > 1/2`, so the entire function
`zetaPoleFree s = (s − 1) ζ(s)` of `RiemannHypothesis.Criteria` has none either, and
`RiemannHypothesis.exists_holomorphic_log_halfPlane` supplies a holomorphic branch `F` of its
logarithm on `re s > 1/2`.  Fix a height `t` and centre a disc at `s₀ = 3 + i t`; the open disc of
radius `5/2` about `s₀` lies in `re s > 1/2`.  Write `G z = F(s₀ + z) − F(s₀)`, so `G 0 = 0`, and
note `re G z = log ‖zetaPoleFree (s₀ + z)‖ − log ‖zetaPoleFree s₀‖` — the unknown branch constant
cancels.

* On the disc of radius `1` the real part of `G` is `O(1)`, because there `re s ≥ 2` forces
  `1/2 ≤ ‖ζ‖ ≤ 2`.  Borel–Carathéodory turns this into `‖G‖ ≤ 4` on `‖z‖ ≤ 1/2`.
* On the disc of radius `5/2` the real part of `G` is at most `6 log t`, because
  `‖ζ(s)‖ ≤ 16‖s‖² + 2` there (`RiemannHypothesis.norm_riemannZeta_le_sq`) while
  `‖zetaPoleFree s₀‖ ≥ t/2`.  Borel–Carathéodory turns this into `‖G‖ ≤ 60 log t / δ` on
  `‖z‖ ≤ 5/2 − δ/2`.
* Hadamard's three circles (`RiemannHypothesis.three_circles`) interpolates between the two
  circles `‖z‖ = 1/2` and `‖z‖ = 5/2 − δ/2`.  At the point `z = σ − 3` the interpolation exponent
  is `log(2(3 − σ))/log(5 − δ) ≤ log(5 − 2δ)/log(5 − δ) < 1`, so `‖G‖` there is
  `O_δ((log t)^{1−c})` with `c = c(δ) > 0`.

Exponentiating, `‖ζ(σ + i t)‖ ≤ 3 exp(4 (60 log t/δ)^{λ₀})`, which is `O_ε(t^ε)` because
`λ₀ < 1`.

## Main results

* `exists_bound_riemannZeta_of_zetaStripForm` — under `ZetaStripForm` (the Riemann hypothesis),
  for every `δ > 0` and `ε > 0` there are `C` and `T₀` with `‖ζ(s)‖ ≤ C (im s)^ε` whenever
  `re s ≥ 1/2 + δ` and `im s ≥ T₀`.
* `exists_bound_riemannZeta_abs_im_of_zetaStripForm` — the same with `|im s|`, by the conjugation
  symmetry `ζ(conj s) = conj (ζ s)`.

## Scope

The bound degenerates as `δ → 0`: the exponent `λ₀ = log(5 − 2δ)/log(5 − δ)` tends to `1`, and
`T₀` tends to infinity.  The critical line itself is therefore *not* covered, and
`LindelofHypothesis` of `RiemannHypothesis/LindelofDensity.lean`, which asks for the bound
uniformly for `re s ≥ 1/2`, is **not** proved here.  Reaching it is Littlewood's theorem
`log ζ(1/2 + i t) = O(log t / log log t)`, which needs the radii of the three circles to shrink
with `t`, and is not formalized.
-/

noncomputable section

open Complex Metric Set

namespace RiemannHypothesis

/-! ## The logarithm branch supplied by the Riemann hypothesis -/

/-- Under the Riemann hypothesis, `zetaPoleFree` has a holomorphic logarithm on `re s > 1/2`. -/
theorem exists_logBranch_of_zetaStripForm (h : ZetaStripForm) :
    ∃ F : ℂ → ℂ, (∀ s : ℂ, 1 / 2 < s.re →
        HasDerivAt F (deriv zetaPoleFree s / zetaPoleFree s) s) ∧
      ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s := by
  have hne : ZetaNonvanishingRightForm := zeta_strip_iff_nonvanishing_right.mp h
  have hzero : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → zetaPoleFree s ≠ 0 := by
    intro s hs hs0
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [zetaPoleFree, Function.update_self] at hs0
      exact one_ne_zero hs0
    · rw [zetaPoleFree_of_ne_one hs1] at hs0
      rcases mul_eq_zero.mp hs0 with h1 | h2
      · exact hs1 (by linear_combination h1)
      · exact hne s (by simpa using hs) hs1 h2
  exact exists_holomorphic_log_halfPlane differentiable_zetaPoleFree hzero

/-! ## Elementary bounds for `zetaPoleFree` -/

/-- `‖(s − 1) ζ(s)‖ ≤ (‖s‖ + 1)(16‖s‖² + 2)` on `re s ≥ 1/2`, away from the real axis. -/
theorem norm_zetaPoleFree_le_poly {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : 3 ≤ |s.im|) :
    ‖zetaPoleFree s‖ ≤ (‖s‖ + 1) * (16 * ‖s‖ ^ 2 + 2) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h2
    simp at h2
    linarith
  rw [zetaPoleFree_of_ne_one hs1, norm_mul]
  have ha : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by simp
  have hb : ‖riemannZeta s‖ ≤ 16 * ‖s‖ ^ 2 + 2 := norm_riemannZeta_le_sq h1 (Or.inr h2)
  exact mul_le_mul ha hb (norm_nonneg _) (by positivity)

/-- Near the centre `3 + i t` the function `zetaPoleFree` is bounded above by `2(t + 3)`. -/
theorem norm_zetaPoleFree_le_near {t : ℝ} (ht : 4 ≤ t) {s : ℂ} (hre : 2 ≤ s.re)
    (hd : ‖s - ((3 : ℂ) + (t : ℂ) * I)‖ < 1) : ‖zetaPoleFree s‖ ≤ 2 * (t + 3) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hzeta : ‖riemannZeta s‖ ≤ 2 := by
    have h := norm_riemannZeta_le_of_one_lt_re (s := s) (by linarith)
    have h1 : 1 / (s.re - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hcentre : ‖(3 : ℂ) + (t : ℂ) * I - 1‖ ≤ t + 2 := by
    have h : (3 : ℂ) + (t : ℂ) * I - 1 = 2 + (t : ℂ) * I := by ring
    rw [h]
    calc ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
      _ = t + 2 := by rw [abs_of_nonneg (by linarith)]; ring
  have hnorm : ‖s - 1‖ ≤ t + 3 := by
    have h : s - 1 = (s - ((3 : ℂ) + (t : ℂ) * I)) + ((3 : ℂ) + (t : ℂ) * I - 1) := by ring
    calc ‖s - 1‖ ≤ ‖s - ((3 : ℂ) + (t : ℂ) * I)‖ + ‖(3 : ℂ) + (t : ℂ) * I - 1‖ := by
          rw [h]; exact norm_add_le _ _
      _ ≤ 1 + (t + 2) := by linarith
      _ = t + 3 := by ring
  rw [zetaPoleFree_of_ne_one hs1, norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (t + 3) * 2 :=
        mul_le_mul hnorm hzeta (norm_nonneg _) (by linarith)
    _ = 2 * (t + 3) := by ring

/-- At the centre `3 + i t` the function `zetaPoleFree` is bounded below by `t/2`. -/
theorem le_norm_zetaPoleFree_center {t : ℝ} (ht : 4 ≤ t) :
    t / 2 ≤ ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ := by
  have hre : ((3 : ℂ) + (t : ℂ) * I).re = 3 := by simp
  have hs1 : (3 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hzeta : (1 : ℝ) / 2 ≤ ‖riemannZeta ((3 : ℂ) + (t : ℂ) * I)‖ :=
    half_le_norm_riemannZeta_of_three_le_re (by rw [hre])
  have hnorm : t ≤ ‖(3 : ℂ) + (t : ℂ) * I - 1‖ := by
    have h : (3 : ℂ) + (t : ℂ) * I - 1 = 2 + (t : ℂ) * I := by ring
    rw [h]
    have him : |((2 : ℂ) + (t : ℂ) * I).im| ≤ ‖(2 : ℂ) + (t : ℂ) * I‖ :=
      Complex.abs_im_le_norm _
    have : ((2 : ℂ) + (t : ℂ) * I).im = t := by simp
    rw [this, abs_of_nonneg (by linarith)] at him
    exact him
  rw [zetaPoleFree_of_ne_one hs1, norm_mul]
  calc t / 2 = t * (1 / 2) := by ring
    _ ≤ ‖(3 : ℂ) + (t : ℂ) * I - 1‖ * ‖riemannZeta ((3 : ℂ) + (t : ℂ) * I)‖ :=
        mul_le_mul hnorm hzeta (by norm_num) (by linarith [norm_nonneg ((3 : ℂ) + (t : ℂ) * I - 1)])

/-- And above by `2(t + 3)`. -/
theorem norm_zetaPoleFree_center_le {t : ℝ} (ht : 4 ≤ t) :
    ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ ≤ 2 * (t + 3) :=
  norm_zetaPoleFree_le_near ht (by norm_num) (by norm_num)

/-! ## The normalized branch on a disc about `3 + i t` -/

/-- `logShift F t z = F(3 + i t + z) − F(3 + i t)`: the branch of `log zetaPoleFree`, translated
to the centre and normalized to vanish there. -/
def logShift (F : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  F ((3 : ℂ) + (t : ℂ) * I + z) - F ((3 : ℂ) + (t : ℂ) * I)

@[simp] lemma logShift_zero (F : ℂ → ℂ) (t : ℝ) : logShift F t 0 = 0 := by
  simp [logShift]

/-- Every point of the open disc of radius `5/2` about `3 + i t` has real part `> 1/2` and, for
`t ≥ 6`, imaginary part `≥ 3`.

(The hypothesis is `6 ≤ t` rather than the `4 ≤ t` of a first draft: the imaginary part of a point
of the disc is only `≥ t − 5/2`, so `t ≥ 11/2` is needed for `im ≥ 3`.  Every use of the lemma has
`t ≥ 100`.) -/
lemma mem_halfPlane_of_mem_ball {t : ℝ} (ht : 6 ≤ t) {z : ℂ} (hz : ‖z‖ < 5 / 2) :
    1 / 2 < ((3 : ℂ) + (t : ℂ) * I + z).re ∧
      3 ≤ ((3 : ℂ) + (t : ℂ) * I + z).im ∧
      ‖(3 : ℂ) + (t : ℂ) * I + z‖ ≤ t + 6 := by
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  have h1 : ((3 : ℂ) + (t : ℂ) * I + z).re = 3 + z.re := by simp
  have h2 : ((3 : ℂ) + (t : ℂ) * I + z).im = t + z.im := by simp
  refine ⟨by rw [h1]; linarith [hre'.1], by rw [h2]; linarith [him'.1], ?_⟩
  calc ‖(3 : ℂ) + (t : ℂ) * I + z‖ ≤ ‖(3 : ℂ) + (t : ℂ) * I‖ + ‖z‖ := norm_add_le _ _
    _ ≤ (‖(3 : ℂ)‖ + ‖(t : ℂ) * I‖) + ‖z‖ := by
        gcongr
        exact norm_add_le _ _
    _ = (3 + |t|) + ‖z‖ := by simp
    _ = (3 + t) + ‖z‖ := by rw [abs_of_nonneg (by linarith)]
    _ ≤ t + 6 := by linarith

/-- `re (logShift F t z)` is the difference of the two logarithms of `‖zetaPoleFree‖`. -/
lemma re_logShift {F : ℂ → ℂ}
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {t : ℝ} (ht : 6 ≤ t) {z : ℂ} (hz : ‖z‖ < 5 / 2) :
    (logShift F t z).re = Real.log ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I + z)‖
      - Real.log ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ := by
  have key : ∀ w : ℂ, 1 / 2 < w.re → Real.log ‖zetaPoleFree w‖ = (F w).re := by
    intro w hw
    rw [← hFexp w hw, Complex.norm_exp, Real.log_exp]
  have h1 : 1 / 2 < ((3 : ℂ) + (t : ℂ) * I + z).re := (mem_halfPlane_of_mem_ball ht hz).1
  have h2 : 1 / 2 < ((3 : ℂ) + (t : ℂ) * I).re := by norm_num
  rw [key _ h1, key _ h2, logShift, Complex.sub_re]

lemma differentiableOn_logShift {F : ℂ → ℂ}
    (hFderiv : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt F (deriv zetaPoleFree s / zetaPoleFree s) s)
    {t : ℝ} (ht : 6 ≤ t) {R : ℝ} (hR : R ≤ 5 / 2) :
    DifferentiableOn ℂ (logShift F t) (ball 0 R) := by
  intro z hz
  have hz' : ‖z‖ < 5 / 2 := lt_of_lt_of_le (by simpa using mem_ball_zero_iff.mp hz) hR
  have hmem : 1 / 2 < ((3 : ℂ) + (t : ℂ) * I + z).re := (mem_halfPlane_of_mem_ball ht hz').1
  have hF : DifferentiableAt ℂ F ((3 : ℂ) + (t : ℂ) * I + z) := (hFderiv _ hmem).differentiableAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ => (3 : ℂ) + (t : ℂ) * I + w) z :=
    differentiableAt_id.const_add _
  exact ((hF.comp z hshift).sub_const (F ((3 : ℂ) + (t : ℂ) * I))).differentiableWithinAt

/-! ## The two Borel–Carathéodory bounds -/

/-- Monotonicity of `Real.log` in the form needed below: the lower bound is only known to be
nonnegative, and `Real.log 0 = 0` is harmless because the upper bound is at least `1`. -/
private lemma log_le_log_of_le_of_one_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 ≤ b) :
    Real.log a ≤ Real.log b := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, Real.log_zero]
    exact Real.log_nonneg hb
  · exact Real.log_le_log h hab

/-- On the disc of radius `1` the real part of the normalized branch is at most `2`. -/
lemma re_logShift_le_two {F : ℂ → ℂ}
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {t : ℝ} (ht : 100 ≤ t) {z : ℂ} (hz : ‖z‖ < 1) : (logShift F t z).re ≤ 2 := by
  have ht6 : (6 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hz' : ‖z‖ < 5 / 2 := by linarith
  rw [re_logShift hFexp ht6 hz']
  -- upper bound at the point
  have hre : (2 : ℝ) ≤ ((3 : ℂ) + (t : ℂ) * I + z).re := by
    have h1 : ((3 : ℂ) + (t : ℂ) * I + z).re = 3 + z.re := by simp
    have := abs_le.mp (Complex.abs_re_le_norm z)
    rw [h1]; linarith [this.1]
  have hd : ‖(3 : ℂ) + (t : ℂ) * I + z - ((3 : ℂ) + (t : ℂ) * I)‖ < 1 := by
    simpa using hz
  have hupper : ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I + z)‖ ≤ 2 * (t + 3) :=
    norm_zetaPoleFree_le_near (by linarith) hre hd
  have hlower : t / 2 ≤ ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ := le_norm_zetaPoleFree_center
    (by linarith)
  have hlog1 : Real.log ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I + z)‖ ≤ Real.log (2 * (t + 3)) :=
    log_le_log_of_le_of_one_le (norm_nonneg _) hupper (by linarith)
  have hlog2 : Real.log (t / 2) ≤ Real.log ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ :=
    Real.log_le_log (by linarith) hlower
  -- `log (2(t+3)) - log (t/2) = log 4 + log (1 + 3/t) ≤ 2 log 2 + 3/t < 2`
  have hsplit : Real.log (2 * (t + 3)) - Real.log (t / 2)
      = Real.log 4 + Real.log (1 + 3 / t) := by
    have h1 : (2 : ℝ) * (t + 3) = (4 * (1 + 3 / t)) * (t / 2) := by field_simp; ring
    rw [h1, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog3 : Real.log (1 + 3 / t) ≤ 3 / t := by
    have := Real.log_le_sub_one_of_pos (x := 1 + 3 / t) (by positivity)
    linarith
  have h3t : 3 / t ≤ 3 / 100 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- On the disc of radius `5/2` the real part of the normalized branch is at most `6 log t`. -/
lemma re_logShift_le_log {F : ℂ → ℂ}
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {t : ℝ} (ht : 100 ≤ t) {z : ℂ} (hz : ‖z‖ < 5 / 2) :
    (logShift F t z).re ≤ 6 * Real.log t := by
  have ht6 : (6 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  rw [re_logShift hFexp ht6 hz]
  obtain ⟨hre, him, hnorm⟩ := mem_halfPlane_of_mem_ball ht6 hz
  set w : ℂ := (3 : ℂ) + (t : ℂ) * I + z with hw
  have hnorm0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hupper : ‖zetaPoleFree w‖ ≤ (‖w‖ + 1) * (16 * ‖w‖ ^ 2 + 2) :=
    norm_zetaPoleFree_le_poly (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hpoly : (‖w‖ + 1) * (16 * ‖w‖ ^ 2 + 2) ≤ (t + 7) * (16 * (t + 6) ^ 2 + 2) := by
    have h1 : ‖w‖ + 1 ≤ t + 7 := by linarith
    have h2 : 16 * ‖w‖ ^ 2 + 2 ≤ 16 * (t + 6) ^ 2 + 2 := by nlinarith
    nlinarith
  -- and this is at most `(t/2) * t^6`
  have hcube : (t + 7) * (16 * (t + 6) ^ 2 + 2) ≤ t / 2 * t ^ 6 := by
    have h1 : (t + 7) * (16 * (t + 6) ^ 2 + 2) ≤ 20 * t ^ 3 := by nlinarith
    have h2 : (20 : ℝ) * t ^ 3 ≤ t / 2 * t ^ 6 := by nlinarith [pow_pos ht0 3, pow_pos ht0 6]
    linarith
  have hlog1 : Real.log ‖zetaPoleFree w‖ ≤ Real.log (t / 2 * t ^ 6) :=
    log_le_log_of_le_of_one_le (norm_nonneg _) (by linarith) (by nlinarith [pow_pos ht0 6])
  have hlower : t / 2 ≤ ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ :=
    le_norm_zetaPoleFree_center (by linarith)
  have hlog2 : Real.log (t / 2) ≤ Real.log ‖zetaPoleFree ((3 : ℂ) + (t : ℂ) * I)‖ :=
    Real.log_le_log (by linarith) hlower
  have hsplit : Real.log (t / 2 * t ^ 6) = Real.log (t / 2) + 6 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  linarith

/-- **Borel–Carathéodory, small disc**: `‖G‖ ≤ 4` on `‖z‖ ≤ 1/2`. -/
theorem norm_logShift_le_four {F : ℂ → ℂ}
    (hFderiv : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt F (deriv zetaPoleFree s / zetaPoleFree s) s)
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {t : ℝ} (ht : 100 ≤ t) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖logShift F t z‖ ≤ 4 := by
  have ht6 : (6 : ℝ) ≤ t := by linarith
  have hball : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  have hmaps : Set.MapsTo (logShift F t) (ball (0 : ℂ) 1) {w : ℂ | w.re ≤ 2} := by
    intro y hy
    exact re_logShift_le_two hFexp ht (by simpa using mem_ball_zero_iff.mp hy)
  have hbc := Complex.borelCaratheodory_zero (M := 2) (f := logShift F t) (R := 1) (z := z)
    (by norm_num) (differentiableOn_logShift hFderiv ht6 (by norm_num)) hmaps (by norm_num)
    hball (logShift_zero F t)
  refine hbc.trans ?_
  have hpos : (0 : ℝ) < 1 - ‖z‖ := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg z]

/-- **Borel–Carathéodory, large disc**: `‖G‖ ≤ 60 log t / δ` on `‖z‖ ≤ 5/2 − δ/2`. -/
theorem norm_logShift_le_log_div {F : ℂ → ℂ}
    (hFderiv : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt F (deriv zetaPoleFree s / zetaPoleFree s) s)
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {t : ℝ} (ht : 100 ≤ t) {z : ℂ}
    (hz : ‖z‖ ≤ 5 / 2 - δ / 2) : ‖logShift F t z‖ ≤ 60 * Real.log t / δ := by
  have ht6 : (6 : ℝ) ≤ t := by linarith
  have hlog : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hball : z ∈ ball (0 : ℂ) (5 / 2) := by
    rw [mem_ball_zero_iff]
    linarith
  have hmaps : Set.MapsTo (logShift F t) (ball (0 : ℂ) (5 / 2))
      {w : ℂ | w.re ≤ 6 * Real.log t} := by
    intro y hy
    exact re_logShift_le_log hFexp ht (by simpa using mem_ball_zero_iff.mp hy)
  have hbc := Complex.borelCaratheodory_zero (M := 6 * Real.log t) (f := logShift F t)
    (R := 5 / 2) (z := z) (by linarith)
    (differentiableOn_logShift hFderiv ht6 (le_refl _)) hmaps (by norm_num) hball
    (logShift_zero F t)
  refine hbc.trans ?_
  have hpos : (0 : ℝ) < 5 / 2 - ‖z‖ := by linarith
  rw [div_le_div_iff₀ hpos hδ0]
  have key : ‖z‖ * (12 * δ + 60) ≤ 150 := by nlinarith [norm_nonneg z]
  nlinarith [mul_le_mul_of_nonneg_left key hlog.le]

/-! ## The three-circles interpolation -/

/-- **The interpolated bound.**  On the annulus `1/2 ≤ ‖z‖ ≤ 5/2 − δ`, the normalized branch is
`O_δ((log t)^{λ₀})` with `λ₀ = log(5 − 2δ)/log(5 − δ) < 1`. -/
theorem norm_logShift_le_rpow {F : ℂ → ℂ}
    (hFderiv : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt F (deriv zetaPoleFree s / zetaPoleFree s) s)
    (hFexp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (F s) = zetaPoleFree s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {t : ℝ} (ht : 100 ≤ t) {z : ℂ}
    (hz1 : 1 / 2 ≤ ‖z‖) (hz2 : ‖z‖ ≤ 5 / 2 - δ) :
    ‖logShift F t z‖
      ≤ 4 * (60 * Real.log t / δ) ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ)) := by
  have ht6 : (6 : ℝ) ≤ t := by linarith
  have hlogt : (1 : ℝ) < Real.log t := by
    have hexp : Real.exp 1 < t := lt_of_lt_of_le (by linarith [Real.exp_one_lt_d9]) ht
    rwa [Real.lt_log_iff_exp_lt (by linarith)]
  have hB : (1 : ℝ) ≤ 60 * Real.log t / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  -- the two radii
  have hr₁ : (0 : ℝ) < 1 / 2 := by norm_num
  have hr : (1 / 2 : ℝ) < 5 / 2 - δ / 2 := by linarith
  have hquot : (5 / 2 - δ / 2) / (1 / 2 : ℝ) = 5 - δ := by ring
  have hL : (0 : ℝ) < Real.log (5 - δ) := Real.log_pos (by linarith)
  -- analyticity on the closed annulus
  have hana : AnalyticOnNhd ℂ (logShift F t) (closedAnnulus (1 / 2) (5 / 2 - δ / 2)) := by
    intro y hy
    have hy' : ‖y‖ ≤ 5 / 2 - δ / 2 := hy.2
    have hnhds : ball (0 : ℂ) (5 / 2) ∈ nhds y :=
      isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith)
    exact (differentiableOn_logShift hFderiv ht6 (le_refl _)).analyticAt hnhds
  have hmem : z ∈ closedAnnulus (1 / 2) (5 / 2 - δ / 2) := ⟨hz1, by linarith⟩
  have h3 := three_circles hr₁ hr hana
    (fun y hy => norm_logShift_le_four hFderiv hFexp ht (le_of_eq hy))
    (fun y hy => norm_logShift_le_log_div hFderiv hFexp hδ0 hδ1 ht (le_of_eq hy)) hmem
  rw [hquot] at h3
  refine h3.trans ?_
  have hznorm : (0 : ℝ) < ‖z‖ := by linarith
  -- the exponent of the first factor lies in `[0, 1]`
  have he₁_le : Real.log ((5 / 2 - δ / 2) / ‖z‖) / Real.log (5 - δ) ≤ 1 := by
    rw [div_le_one hL, ← hquot]
    refine Real.log_le_log (by positivity) ?_
    gcongr
  have hfirst : (4 : ℝ) ^ (Real.log ((5 / 2 - δ / 2) / ‖z‖) / Real.log (5 - δ)) ≤ 4 := by
    calc (4 : ℝ) ^ (Real.log ((5 / 2 - δ / 2) / ‖z‖) / Real.log (5 - δ))
        ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he₁_le
      _ = 4 := Real.rpow_one 4
  -- the exponent of the second factor is at most `λ₀`
  have hzz : ‖z‖ / (1 / 2 : ℝ) = 2 * ‖z‖ := by ring
  have he₂_le : Real.log (‖z‖ / (1 / 2)) / Real.log (5 - δ)
      ≤ Real.log (5 - 2 * δ) / Real.log (5 - δ) := by
    rw [hzz]
    gcongr
    linarith
  have hsecond : (60 * Real.log t / δ) ^ (Real.log (‖z‖ / (1 / 2)) / Real.log (5 - δ))
      ≤ (60 * Real.log t / δ) ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ)) :=
    Real.rpow_le_rpow_of_exponent_le hB he₂_le
  have hnn : (0 : ℝ) ≤ (60 * Real.log t / δ) ^ (Real.log (‖z‖ / (1 / 2)) / Real.log (5 - δ)) :=
    Real.rpow_nonneg (by linarith) _
  have hnn' : (0 : ℝ) ≤ (4 : ℝ) ^ (Real.log ((5 / 2 - δ / 2) / ‖z‖) / Real.log (5 - δ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc (4 : ℝ) ^ (Real.log ((5 / 2 - δ / 2) / ‖z‖) / Real.log (5 - δ))
        * (60 * Real.log t / δ) ^ (Real.log (‖z‖ / (1 / 2)) / Real.log (5 - δ))
      ≤ 4 * (60 * Real.log t / δ) ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ)) :=
        mul_le_mul hfirst hsecond hnn (by norm_num)

/-! ## The bound for `ζ` -/

/-- Under the Riemann hypothesis, for `1/2 + δ ≤ σ ≤ 5/2` and `t` large,
`‖ζ(σ + i t)‖ ≤ 3 exp(4 (60 log t/δ)^{λ₀})`. -/
theorem norm_riemannZeta_le_exp_of_zetaStripForm (h : ZetaStripForm) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {s : ℂ} (hre : 1 / 2 + δ ≤ s.re) (hre2 : s.re ≤ 5 / 2)
    (ht : 100 ≤ s.im) :
    ‖riemannZeta s‖
      ≤ 3 * Real.exp (4 * (60 * Real.log s.im / δ)
          ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ))) := by
  obtain ⟨F, hFderiv, hFexp⟩ := exists_logBranch_of_zetaStripForm h
  set t : ℝ := s.im with htdef
  set K : ℝ := 4 * (60 * Real.log t / δ) ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ)) with hKdef
  set c : ℂ := (3 : ℂ) + (t : ℂ) * I with hcdef
  set z : ℂ := s - c with hzdef
  have hsz : c + z = s := by rw [hzdef]; ring
  have hzeq : z = ((s.re - 3 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hzdef, hcdef, htdef]
  have hznorm : ‖z‖ = 3 - s.re := by
    rw [hzeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hz1 : 1 / 2 ≤ ‖z‖ := by rw [hznorm]; linarith
  have hz2 : ‖z‖ ≤ 5 / 2 - δ := by rw [hznorm]; linarith
  have hG : ‖logShift F t z‖ ≤ K :=
    norm_logShift_le_rpow hFderiv hFexp hδ0 (by linarith) ht hz1 hz2
  have hreG : (logShift F t z).re ≤ K := le_trans (Complex.re_le_norm _) hG
  -- `‖zetaPoleFree s‖ = exp (re G z) * ‖zetaPoleFree c‖`
  have hnormS : ‖zetaPoleFree s‖ = Real.exp ((F s).re) := by
    rw [← hFexp s (by linarith), Complex.norm_exp]
  have hnormC : ‖zetaPoleFree c‖ = Real.exp ((F c).re) := by
    rw [← hFexp c (by rw [hcdef]; norm_num), Complex.norm_exp]
  have hFsplit : (F s).re = (logShift F t z).re + (F c).re := by
    rw [logShift, ← hcdef, hsz, Complex.sub_re]
    ring
  have hsplit : ‖zetaPoleFree s‖ = Real.exp ((logShift F t z).re) * ‖zetaPoleFree c‖ := by
    rw [hnormS, hnormC, hFsplit, Real.exp_add]
  have hcbound : ‖zetaPoleFree c‖ ≤ 2 * (t + 3) := norm_zetaPoleFree_center_le (by linarith)
  have hexp_pos : (0 : ℝ) < Real.exp K := Real.exp_pos K
  have hZPF : ‖zetaPoleFree s‖ ≤ Real.exp K * (2 * (t + 3)) := by
    rw [hsplit]
    exact mul_le_mul (Real.exp_le_exp.mpr hreG) hcbound (norm_nonneg _) hexp_pos.le
  -- pass from `zetaPoleFree` to `ζ`
  have hs1 : s ≠ 1 := by
    intro hh
    have h0 : s.im = 0 := by rw [hh]; simp
    rw [← htdef] at h0
    linarith
  have hs1norm : t ≤ ‖s - 1‖ := by
    have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have h2 : (s - 1).im = t := by simp [htdef]
    rw [h2, abs_of_nonneg (by linarith)] at him
    exact him
  have hmul : ‖s - 1‖ * ‖riemannZeta s‖ ≤ Real.exp K * (2 * (t + 3)) := by
    rw [← norm_mul, ← zetaPoleFree_of_ne_one hs1]
    exact hZPF
  have hzeta_nonneg : (0 : ℝ) ≤ ‖riemannZeta s‖ := norm_nonneg _
  have htpos : (0 : ℝ) < t := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hs1norm hzeta_nonneg]

/-- **The Lindelöf bound away from the critical line, under the Riemann hypothesis.**  For every
`δ > 0` and every `ε > 0` there are `C` and `T₀` with `‖ζ(s)‖ ≤ C (im s)^ε` whenever
`re s ≥ 1/2 + δ` and `im s ≥ T₀`. -/
theorem exists_bound_riemannZeta_of_zetaStripForm (h : ZetaStripForm) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ ε := by
  set lam : ℝ := Real.log (5 - 2 * δ) / Real.log (5 - δ) with hlamdef
  have hL : (0 : ℝ) < Real.log (5 - δ) := Real.log_pos (by linarith)
  have hL2 : (0 : ℝ) < Real.log (5 - 2 * δ) := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := div_pos hL2 hL
  have hlam1 : lam < 1 := by
    rw [hlamdef, div_lt_one hL]
    exact Real.log_lt_log (by linarith) (by linarith)
  set A : ℝ := 4 * (60 / δ) ^ lam with hAdef
  have hApos : 0 < A := by
    have : (0 : ℝ) < (60 / δ) ^ lam := Real.rpow_pos_of_pos (by positivity) _
    positivity
  -- the threshold beyond which `A (log t)^lam ≤ ε log t`
  set u₀ : ℝ := (A / ε + 1) ^ (1 / (1 - lam)) with hu₀def
  have hu₀pos : 0 < u₀ := Real.rpow_pos_of_pos (by positivity) _
  set T₀ : ℝ := max 100 (Real.exp u₀) with hT₀def
  refine ⟨3, T₀, by norm_num, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro s hre hT
  have ht100 : (100 : ℝ) ≤ s.im := le_trans (le_max_left _ _) hT
  have htpos : (0 : ℝ) < s.im := by linarith
  have hone_le : (1 : ℝ) ≤ s.im ^ ε := Real.one_le_rpow (by linarith) hε.le
  rcases le_or_gt s.re (5 / 2) with hre2 | hre2
  · -- the interesting range
    have hmain := norm_riemannZeta_le_exp_of_zetaStripForm h hδ0 hδ1 hre hre2 ht100
    refine hmain.trans ?_
    have hlogpos : (0 : ℝ) < Real.log s.im := Real.log_pos (by linarith)
    -- `4 (60 log t/δ)^lam = A (log t)^lam`
    have hfactor : 4 * (60 * Real.log s.im / δ) ^ lam = A * Real.log s.im ^ lam := by
      have h1 : 60 * Real.log s.im / δ = (60 / δ) * Real.log s.im := by ring
      rw [h1, Real.mul_rpow (by positivity) hlogpos.le, hAdef]
      ring
    -- the threshold gives `A (log t)^lam ≤ ε log t`
    have hu₀le : u₀ ≤ Real.log s.im := by
      have h1 : Real.exp u₀ ≤ s.im := le_trans (le_max_right _ _) hT
      calc u₀ = Real.log (Real.exp u₀) := (Real.log_exp u₀).symm
        _ ≤ Real.log s.im := Real.log_le_log (Real.exp_pos _) h1
    have hpow : A / ε + 1 ≤ Real.log s.im ^ (1 - lam) := by
      have h1 : u₀ ^ (1 - lam) ≤ Real.log s.im ^ (1 - lam) :=
        Real.rpow_le_rpow hu₀pos.le hu₀le (by linarith)
      have h2 : u₀ ^ (1 - lam) = A / ε + 1 := by
        rw [hu₀def, ← Real.rpow_mul (by positivity), one_div,
          inv_mul_cancel₀ (by linarith), Real.rpow_one]
      linarith [h2 ▸ h1]
    have hsplitpow : Real.log s.im ^ lam * Real.log s.im ^ (1 - lam) = Real.log s.im := by
      rw [← Real.rpow_add hlogpos]
      simp
    have hkey : A * Real.log s.im ^ lam ≤ ε * Real.log s.im := by
      have hpow_pos : (0 : ℝ) < Real.log s.im ^ lam := Real.rpow_pos_of_pos hlogpos _
      have h1 : (A / ε + 1) * Real.log s.im ^ lam
          ≤ Real.log s.im ^ (1 - lam) * Real.log s.im ^ lam :=
        mul_le_mul_of_nonneg_right hpow hpow_pos.le
      rw [mul_comm (Real.log s.im ^ (1 - lam)), hsplitpow] at h1
      have h2 : A / ε * Real.log s.im ^ lam ≤ Real.log s.im := by nlinarith
      have h3 : A * Real.log s.im ^ lam ≤ ε * Real.log s.im := by
        have := mul_le_mul_of_nonneg_left h2 hε.le
        field_simp at this
        linarith
      exact h3
    have hrpow : s.im ^ ε = Real.exp (ε * Real.log s.im) := by
      rw [Real.rpow_def_of_pos htpos]
      ring_nf
    rw [hrpow]
    have : Real.exp (4 * (60 * Real.log s.im / δ) ^ lam) ≤ Real.exp (ε * Real.log s.im) := by
      apply Real.exp_le_exp.mpr
      rw [hfactor]
      exact hkey
    linarith
  · -- far to the right of the strip the Dirichlet series bound suffices
    have hzeta : ‖riemannZeta s‖ ≤ 2 := by
      have hbd := norm_riemannZeta_le_of_one_lt_re (s := s) (by linarith)
      have h1 : 1 / (s.re - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    nlinarith

/-- **The two-sided form**: the same bound with `|im s|` in place of `im s`, obtained from the
conjugation symmetry `ζ(conj s) = conj (ζ s)`. -/
theorem exists_bound_riemannZeta_abs_im_of_zetaStripForm (h : ZetaStripForm) {δ ε : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ε := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := exists_bound_riemannZeta_of_zetaStripForm h hδ0 hδ1 hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro s hre hT
  rcases le_or_gt 0 s.im with him | him
  · rw [abs_of_nonneg him] at hT ⊢
    exact hbound s hre hT
  · have habs : |s.im| = -s.im := abs_of_neg him
    have hconj : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
    have hconj' : ((starRingEnd ℂ) s).im = -s.im := Complex.conj_im s
    have hnorm : ‖riemannZeta ((starRingEnd ℂ) s)‖ = ‖riemannZeta s‖ := by
      rw [riemannZeta_conj, RCLike.norm_conj]
    have := hbound ((starRingEnd ℂ) s) (by rw [hconj]; exact hre)
      (by rw [hconj', ← habs]; exact hT)
    rw [hnorm, hconj', ← habs] at this
    exact this

end RiemannHypothesis
