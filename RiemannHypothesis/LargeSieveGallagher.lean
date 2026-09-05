/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieve
import RiemannHypothesis.GallagherDiscrete

/-!
# The large sieve inequality without a logarithm: Gallagher's form

`RiemannHypothesis.LargeSieve` proves the large sieve inequality

`∑_r ‖∑_{n < N} a n e(n t r)‖² ≤ (N + δ⁻¹ (1 + log (2δ)⁻¹)) ∑_{n < N} ‖a n‖²`

for points `t r` that are `δ`-separated modulo one, by an elementary Schur test on the Dirichlet
kernel.  The logarithm there is the cost of that argument.  This file removes it, by Gallagher's
Sobolev argument; the constant proved here is

`∑_r ‖∑_{n < N} a n e(n t r)‖² ≤ (δ⁻¹ + π N) ∑_{n < N} ‖a n‖²`.

## Main results

* `integral_normSq_expPoly` — Parseval over one period for an exponential polynomial whose
  frequencies are the integers `n` shifted by a fixed real `c`.
* `hasDerivAt_expPoly` — such a polynomial is differentiable, with derivative the polynomial with
  coefficients `2π (n − c) i · a n`.
* `integral_normSq_deriv_le` — for the centred shift `c = (N − 1)/2` the mean square of the
  derivative is at most `(π N)²` times the mean square.
* `sum_normSq_le_of_separated_sharp` — Gallagher's lemma in the form that keeps the cross term:
  `δ ∑_r ‖f (t r)‖² ≤ ∫_A^B ‖f‖² + (δ/2) ∫_A^B 2 ‖f‖ ‖f'‖`.
* `sum_normSq_expPoly_le` — the large sieve for points separated inside `[δ/2, 1 − δ/2]`.
* `large_sieve_gallagher` — **the large sieve inequality with constant `δ⁻¹ + π N`**, for points
  separated modulo one.
* `card_le_of_large_values_gallagher` — the large-values count that follows.

## Scope

The constant is not the sharp one: Selberg and Montgomery–Vaughan prove the large sieve with
`N + δ⁻¹`, and the factor `π` on `N` here is the cost of the Sobolev step — it comes from bounding
the mean square of the derivative of the centred polynomial by `(π N)²` times its own mean square.
What is gained over `RiemannHypothesis.LargeSieve` is the removal of the logarithm from the `δ⁻¹`
term; the two bounds are otherwise incomparable, and a user may take the minimum of the two.  As
in that file, everything here is about exponential sums, not about `ζ`: no zero-density estimate
follows and no zero is located.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace RiemannHypothesis

namespace LargeSieveGallagher

open KusminLandau LargeSieve

/-! ## Exponential polynomials with shifted frequencies -/

/-- The exponential polynomial `θ ↦ ∑_{n < N} a n e((n − c) θ)`.  The shift `c` of the
frequencies does not change the modulus, but the choice `c = (N − 1)/2` centres them and makes
the derivative as small as possible. -/
def expPoly (a : ℕ → ℂ) (N : ℕ) (c : ℝ) (θ : ℝ) : ℂ :=
  ∑ n ∈ range N, a n * e2pi (((n : ℝ) - c) * θ)

/-- The coefficients of the derivative of `expPoly a N c`. -/
def derivCoeff (a : ℕ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ((2 * Real.pi * ((n : ℝ) - c) : ℝ) : ℂ) * Complex.I * a n

theorem continuous_e2pi_mul (lam : ℝ) : Continuous fun θ : ℝ => e2pi (lam * θ) := by
  unfold e2pi
  fun_prop

/-- The derivative of `θ ↦ e(λ θ)`. -/
theorem hasDerivAt_e2pi_mul (lam θ : ℝ) :
    HasDerivAt (fun x : ℝ => e2pi (lam * x))
      (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I * e2pi (lam * θ)) θ := by
  have hfun : (fun x : ℝ => e2pi (lam * x))
      = fun x : ℝ => Complex.exp ((((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I) * (x : ℂ)) := by
    funext x
    simp only [e2pi]
    congr 1
    push_cast
    ring
  have hlin : HasDerivAt (fun x : ℝ => (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I) * (x : ℂ))
      (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I) θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul
      (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I)
  have h2 := hlin.cexp
  rw [hfun]
  convert h2 using 1
  simp only [e2pi]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The derivative of an exponential polynomial is the exponential polynomial with coefficients
`derivCoeff`. -/
theorem hasDerivAt_expPoly (a : ℕ → ℂ) (N : ℕ) (c θ : ℝ) :
    HasDerivAt (expPoly a N c) (expPoly (derivCoeff a c) N c θ) θ := by
  have key : ∀ n ∈ range N, HasDerivAt (fun x : ℝ => a n * e2pi (((n : ℝ) - c) * x))
      (derivCoeff a c n * e2pi (((n : ℝ) - c) * θ)) θ := by
    intro n _
    have h := (hasDerivAt_e2pi_mul ((n : ℝ) - c) θ).const_mul (a n)
    have heq : a n * (((2 * Real.pi * ((n : ℝ) - c) : ℝ) : ℂ) * Complex.I
        * e2pi (((n : ℝ) - c) * θ)) = derivCoeff a c n * e2pi (((n : ℝ) - c) * θ) := by
      simp only [derivCoeff]; ring
    rwa [heq] at h
  have hsum := HasDerivAt.sum key
  have hfun : (∑ i ∈ range N, fun x : ℝ => a i * e2pi (((i : ℝ) - c) * x)) = expPoly a N c := by
    funext x
    simp [expPoly, Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

theorem continuous_expPoly (a : ℕ → ℂ) (N : ℕ) (c : ℝ) : Continuous (expPoly a N c) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_expPoly a N c θ).continuousAt

/-! ## Parseval over one period -/

/-- `∫₀¹ e(k θ) dθ` is `1` for `k = 0` and `0` otherwise. -/
theorem integral_e2pi_int (k : ℤ) :
    (∫ θ in (0:ℝ)..1, e2pi ((k : ℝ) * θ)) = if k = 0 then (1 : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [e2pi]
  · rw [if_neg hk]
    set C : ℂ := ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I with hC
    have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hne : C ≠ 0 := by
      have h1 : (2 * Real.pi * (k : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hkR
      simp only [hC]
      exact mul_ne_zero (by exact_mod_cast Complex.ofReal_ne_zero.mpr h1) Complex.I_ne_zero
    have hfun : (fun θ : ℝ => e2pi ((k : ℝ) * θ)) = fun θ : ℝ => Complex.exp (C * (θ : ℂ)) := by
      funext θ
      simp only [e2pi, hC]
      congr 1
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex hne]
    have h1 : Complex.exp (C * ((1 : ℝ) : ℂ)) = 1 := by
      have hval : C * ((1 : ℝ) : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        simp only [hC]; push_cast; ring
      rw [hval, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (C * ((0 : ℝ) : ℂ)) = 1 := by norm_num
    rw [h1, h0]
    simp

/-- **Parseval over one period.**  The frequencies `n − c` differ by integers, so the cross terms
integrate to zero. -/
theorem integral_normSq_expPoly (a : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    (∫ θ in (0:ℝ)..1, ‖expPoly a N c θ‖ ^ 2) = ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  have hpt : ∀ θ : ℝ, ((‖expPoly a N c θ‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ range N, ∑ n ∈ range N, a m * (starRingEnd ℂ) (a n)
          * e2pi ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by
    intro θ
    have h1 : ((‖expPoly a N c θ‖ ^ 2 : ℝ) : ℂ)
        = expPoly a N c θ * (starRingEnd ℂ) (expPoly a N c θ) := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    rw [h1]
    unfold expPoly
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, conj_e2pi]
    have h2 : e2pi (((m : ℝ) - c) * θ) * e2pi (-(((n : ℝ) - c) * θ))
        = e2pi ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by
      rw [← e2pi_add]
      congr 1
      push_cast
      ring
    calc a m * e2pi (((m : ℝ) - c) * θ) * ((starRingEnd ℂ) (a n) * e2pi (-(((n : ℝ) - c) * θ)))
        = a m * (starRingEnd ℂ) (a n)
            * (e2pi (((m : ℝ) - c) * θ) * e2pi (-(((n : ℝ) - c) * θ))) := by ring
      _ = a m * (starRingEnd ℂ) (a n) * e2pi ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) := by rw [h2]
  have hcomplex : ((∫ θ in (0:ℝ)..1, ‖expPoly a N c θ‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ range N, ‖a n‖ ^ 2 := by
    rw [← intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_congr (g := fun θ => ∑ m ∈ range N, ∑ n ∈ range N,
      a m * (starRingEnd ℂ) (a n) * e2pi ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ))
      (fun θ _ => hpt θ)]
    rw [intervalIntegral.integral_finsetSum]
    · have hterm : ∀ m ∈ range N, (∫ θ in (0:ℝ)..1, ∑ n ∈ range N, a m * (starRingEnd ℂ) (a n)
          * e2pi ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ)) = ‖a m‖ ^ 2 := by
        intro m hm
        rw [intervalIntegral.integral_finsetSum]
        · rw [Finset.sum_eq_single m]
          · rw [intervalIntegral.integral_const_mul, integral_e2pi_int]
            simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          · intro n _ hnm
            rw [intervalIntegral.integral_const_mul, integral_e2pi_int]
            have hne : ((m : ℤ) - (n : ℤ)) ≠ 0 := by
              simp only [sub_ne_zero, ne_eq, Nat.cast_inj]
              exact fun h => hnm h.symm
            simp [hne]
          · intro h; exact absurd hm h
        · intro n _
          exact (continuous_const.mul (continuous_e2pi_mul _)).intervalIntegrable _ _
      rw [Finset.sum_congr rfl hterm]
      push_cast
      rfl
    · intro m _
      exact (continuous_finsetSum _ fun n _ =>
        continuous_const.mul (continuous_e2pi_mul _)).intervalIntegrable _ _
  exact_mod_cast hcomplex

/-- For the centred shift `c = (N − 1)/2` the mean square of the derivative is at most `(π N)²`
times the mean square. -/
theorem integral_normSq_deriv_le (a : ℕ → ℂ) (N : ℕ) :
    (∫ θ in (0:ℝ)..1, ‖expPoly (derivCoeff a (((N : ℝ) - 1) / 2)) N (((N : ℝ) - 1) / 2) θ‖ ^ 2)
      ≤ (Real.pi * N) ^ 2 * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  set c : ℝ := ((N : ℝ) - 1) / 2 with hc
  rw [integral_normSq_expPoly, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnN : (n : ℝ) ≤ (N : ℝ) - 1 := by
    have : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have habs : |(n : ℝ) - c| ≤ ((N : ℝ) - 1) / 2 := by
    rw [abs_le, hc]
    constructor <;> linarith
  have hnorm : ‖derivCoeff a c n‖ = |2 * Real.pi * ((n : ℝ) - c)| * ‖a n‖ := by
    rw [derivCoeff, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hbound : |2 * Real.pi * ((n : ℝ) - c)| ≤ Real.pi * N := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    have := mul_le_mul_of_nonneg_left habs (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    calc 2 * Real.pi * |(n : ℝ) - c| ≤ 2 * Real.pi * (((N : ℝ) - 1) / 2) := this
      _ ≤ Real.pi * N := by nlinarith [Real.pi_pos]
  rw [hnorm, mul_pow]
  have hsq : |2 * Real.pi * ((n : ℝ) - c)| ^ 2 ≤ (Real.pi * N) ^ 2 := by
    have h0 : (0:ℝ) ≤ |2 * Real.pi * ((n : ℝ) - c)| := abs_nonneg _
    nlinarith [hbound, h0]
  nlinarith [sq_nonneg ‖a n‖, hsq, norm_nonneg (a n)]

/-! ## Gallagher's lemma with the cross term -/

/-- **Gallagher's lemma**, in the form that keeps the cross term: for `δ`-separated points
`t i` in `[A + δ/2, B − δ/2]`,
`δ ∑ ‖f (t i)‖² ≤ ∫_A^B ‖f‖² + (δ/2) ∫_A^B 2 ‖f‖ ‖f'‖`. -/
theorem sum_normSq_le_of_separated_sharp {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ)
    (hAB : A ≤ B) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ (∫ x in A..B, ‖f x‖ ^ 2) + (δ / 2) * ∫ x in A..B, 2 * ‖f x‖ * ‖f' x‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hnormsq : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by fun_prop
  have hcross : Continuous fun x : ℝ => 2 * ‖f x‖ * ‖f' x‖ := by fun_prop
  have hpt : ∀ i ∈ s, δ * ‖f (t i)‖ ^ 2
      ≤ (∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
        + (δ / 2) * ∫ x in (t i - δ / 2)..(t i + δ / 2), 2 * ‖f x‖ * ‖f' x‖ := by
    intro i _
    have hL := Gallagher.mul_normSq_le_integral_of_mem_Icc hf hf' (u := t i - δ / 2) (v := t i)
      (c := t i) (by linarith) ⟨by linarith, le_rfl⟩
    have hR := Gallagher.mul_normSq_le_integral_of_mem_Icc hf hf' (u := t i) (v := t i + δ / 2)
      (c := t i) (by linarith) ⟨le_rfl, by linarith⟩
    rw [show t i - (t i - δ / 2) = δ / 2 by ring] at hL
    rw [show t i + δ / 2 - t i = δ / 2 by ring] at hR
    have hadd1 : (∫ x in (t i - δ / 2)..(t i), ‖f x‖ ^ 2)
        + (∫ x in (t i)..(t i + δ / 2), ‖f x‖ ^ 2)
        = ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        (hnormsq.intervalIntegrable _ _) (hnormsq.intervalIntegrable _ _)
    have hadd2 : (∫ x in (t i - δ / 2)..(t i), 2 * ‖f x‖ * ‖f' x‖)
        + (∫ x in (t i)..(t i + δ / 2), 2 * ‖f x‖ * ‖f' x‖)
        = ∫ x in (t i - δ / 2)..(t i + δ / 2), 2 * ‖f x‖ * ‖f' x‖ :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcross.intervalIntegrable _ _) (hcross.intervalIntegrable _ _)
    have hsum := add_le_add hL hR
    rw [show δ * ‖f (t i)‖ ^ 2 = δ / 2 * ‖f (t i)‖ ^ 2 + δ / 2 * ‖f (t i)‖ ^ 2 by ring]
    refine hsum.trans (le_of_eq ?_)
    rw [← hadd1, ← hadd2]
    ring
  calc δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2 = ∑ i ∈ s, δ * ‖f (t i)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, ((∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
          + (δ / 2) * ∫ x in (t i - δ / 2)..(t i + δ / 2), 2 * ‖f x‖ * ‖f' x‖) :=
        Finset.sum_le_sum hpt
    _ = (∑ i ∈ s, ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
          + (δ / 2) * ∑ i ∈ s, ∫ x in (t i - δ / 2)..(t i + δ / 2), 2 * ‖f x‖ * ‖f' x‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (∫ x in A..B, ‖f x‖ ^ 2) + (δ / 2) * ∫ x in A..B, 2 * ‖f x‖ * ‖f' x‖ := by
        have h1 :=
          Gallagher.sum_integral_window_le hnormsq (fun x => by positivity) hδ hAB hsep hmem
        have h2 :=
          Gallagher.sum_integral_window_le hcross (fun x => by positivity) hδ hAB hsep hmem
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ δ / 2)
        linarith

/-! ## The large sieve -/

/-- The large sieve for points that are `δ`-separated inside `[δ/2, 1 − δ/2]`. -/
theorem sum_normSq_expPoly_le {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (1 - δ / 2))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖expPoly a N (((N : ℝ) - 1) / 2) (t i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  set c : ℝ := ((N : ℝ) - 1) / 2 with hc
  set f : ℝ → ℂ := expPoly a N c with hf
  set g : ℝ → ℂ := expPoly (derivCoeff a c) N c with hg
  set A : ℝ := ∑ n ∈ range N, ‖a n‖ ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hzero : ∀ θ : ℝ, f θ = 0 := by
      intro θ; simp [hf, expPoly]
    simp only [hzero, norm_zero]
    simp [hA]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpiN : 0 < Real.pi * N := by positivity
  have hgall := sum_normSq_le_of_separated_sharp (f := f) (f' := g)
    (hasDerivAt_expPoly a N c) (continuous_expPoly _ _ _) hδ (by norm_num : (0:ℝ) ≤ 1) hsep
    (fun i hi => by simpa using hmem i hi)
  have hParseval : (∫ θ in (0:ℝ)..1, ‖f θ‖ ^ 2) = A := integral_normSq_expPoly a N c
  have hderiv : (∫ θ in (0:ℝ)..1, ‖g θ‖ ^ 2) ≤ (Real.pi * N) ^ 2 * A :=
    integral_normSq_deriv_le a N
  have hfc : Continuous f := continuous_expPoly _ _ _
  have hgc : Continuous g := continuous_expPoly _ _ _
  have hcross : (∫ θ in (0:ℝ)..1, 2 * ‖f θ‖ * ‖g θ‖) ≤ 2 * (Real.pi * N) * A := by
    have hpt : ∀ θ ∈ Set.Icc (0:ℝ) 1, 2 * ‖f θ‖ * ‖g θ‖
        ≤ (Real.pi * N) * ‖f θ‖ ^ 2 + (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2 := by
      intro θ _
      have hk := hpiN
      have hsq : 0 ≤ ((Real.pi * N) * ‖f θ‖ - ‖g θ‖) ^ 2 := sq_nonneg _
      rw [← sub_nonneg]
      have hexp : (Real.pi * N) * ‖f θ‖ ^ 2 + (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2
          - 2 * ‖f θ‖ * ‖g θ‖ = (Real.pi * N)⁻¹ * ((Real.pi * N) * ‖f θ‖ - ‖g θ‖) ^ 2 := by
        field_simp
        ring
      rw [hexp]
      positivity
    have hi1 : IntervalIntegrable (fun θ : ℝ => 2 * ‖f θ‖ * ‖g θ‖) volume 0 1 := by
      have : Continuous fun θ : ℝ => 2 * ‖f θ‖ * ‖g θ‖ := by fun_prop
      exact this.intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun θ : ℝ => (Real.pi * N) * ‖f θ‖ ^ 2 + (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2) volume 0 1 := by
      have : Continuous fun θ : ℝ =>
          (Real.pi * N) * ‖f θ‖ ^ 2 + (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2 := by fun_prop
      exact this.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi1 hi2 hpt
    have hI1 : IntervalIntegrable (fun θ : ℝ => (Real.pi * N) * ‖f θ‖ ^ 2) volume 0 1 :=
      (continuous_const.mul (by fun_prop : Continuous fun θ : ℝ => ‖f θ‖ ^ 2)).intervalIntegrable
        _ _
    have hI2 : IntervalIntegrable (fun θ : ℝ => (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2) volume 0 1 :=
      (continuous_const.mul (by fun_prop : Continuous fun θ : ℝ => ‖g θ‖ ^ 2)).intervalIntegrable
        _ _
    have hsplit : (∫ θ in (0:ℝ)..1, (Real.pi * N) * ‖f θ‖ ^ 2 + (Real.pi * N)⁻¹ * ‖g θ‖ ^ 2)
        = (Real.pi * N) * (∫ θ in (0:ℝ)..1, ‖f θ‖ ^ 2)
          + (Real.pi * N)⁻¹ * ∫ θ in (0:ℝ)..1, ‖g θ‖ ^ 2 := by
      rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hsplit, hParseval] at hmono
    have hstep : (Real.pi * N)⁻¹ * (∫ θ in (0:ℝ)..1, ‖g θ‖ ^ 2)
        ≤ (Real.pi * N)⁻¹ * ((Real.pi * N) ^ 2 * A) :=
      mul_le_mul_of_nonneg_left hderiv (by positivity)
    have hval : (Real.pi * N)⁻¹ * ((Real.pi * N) ^ 2 * A) = (Real.pi * N) * A := by
      field_simp
    rw [hval] at hstep
    linarith
  rw [hParseval] at hgall
  have hfinal : δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2 ≤ A + δ * (Real.pi * N) * A := by
    have hstep := mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ δ / 2)
    have : (δ / 2) * (2 * (Real.pi * N) * A) = δ * (Real.pi * N) * A := by ring
    linarith [hgall, hstep, this ▸ hstep]
  have hδ0 : 0 < δ := hδ
  rw [← le_div_iff₀' hδ0] at hfinal
  refine hfinal.trans (le_of_eq ?_)
  field_simp

/-- **The large sieve inequality, Gallagher's form.**  For points `t i` that are `δ`-separated
modulo one, `∑_i ‖∑_{n < N} a n e(n t i)‖² ≤ (δ⁻¹ + π N) ∑_{n < N} ‖a n‖²`. -/
theorem large_sieve_gallagher {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  classical
  have hA0 : (0:ℝ) ≤ ∑ n ∈ range N, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => by positivity
  have hconst : (0:ℝ) ≤ δ⁻¹ + Real.pi * N := by positivity
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simpa using mul_nonneg hconst hA0
  set c : ℝ := ((N : ℝ) - 1) / 2 with hc
  set v : ι → ℝ := fun i => Int.fract (t i - t i₀) + δ / 2 with hv
  set a' : ℕ → ℂ := fun n => a n * e2pi ((n : ℝ) * (t i₀ - δ / 2)) with ha'
  -- the shifted points are separated
  have hsep' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |v i - v j| := by
    intro i hi j hj hij
    have hdiff : v i - v j
        = (t i - t j) - ((⌊ t i - t i₀ ⌋ : ℤ) - (⌊ t j - t i₀ ⌋ : ℤ) : ℤ) := by
      simp only [hv, Int.fract]
      push_cast
      ring
    rw [hdiff]
    exact (hsep i hi j hj hij).trans (intDist_le_abs_sub_int _ _)
  -- and they lie in the window
  have hmem' : ∀ i ∈ s, v i ∈ Set.Icc (δ / 2) (1 - δ / 2) := by
    intro i hi
    have hfr0 : 0 ≤ Int.fract (t i - t i₀) := Int.fract_nonneg _
    have hfr1 : Int.fract (t i - t i₀) ≤ 1 - δ := by
      rcases eq_or_ne i i₀ with rfl | hne
      · simp only [sub_self, Int.fract_zero]
        linarith
      · have hd := hsep i hi i₀ hi₀ hne
        have hle : intDist (t i - t i₀) ≤ |(t i - t i₀) - ((⌊ t i - t i₀ ⌋ + 1 : ℤ) : ℝ)| :=
          intDist_le_abs_sub_int _ _
        have hfrlt : Int.fract (t i - t i₀) < 1 := Int.fract_lt_one _
        have heq : (t i - t i₀) - ((⌊ t i - t i₀ ⌋ + 1 : ℤ) : ℝ)
            = Int.fract (t i - t i₀) - 1 := by
          simp only [Int.fract]
          push_cast
          ring
        rw [heq, abs_of_nonpos (by linarith)] at hle
        linarith
    constructor
    · simp only [hv]; linarith
    · simp only [hv]; linarith
  have hkey := sum_normSq_expPoly_le hδ hsep' hmem' a' N
  -- the values are the original exponential sums
  have hterm : ∀ i ∈ s, ‖expPoly a' N c (v i)‖ = ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ := by
    intro i _
    have hfact : expPoly a' N c (v i)
        = e2pi (-(c * v i)) * ∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hsum : ((n : ℝ) * (t i₀ - δ / 2)) + ((n : ℝ) - c) * v i
          = ((n : ℝ) * t i + -(c * v i)) - ((n * ⌊ t i - t i₀ ⌋ : ℤ) : ℝ) := by
        simp only [hv, Int.fract]
        push_cast
        ring
      calc a' n * e2pi (((n : ℝ) - c) * v i)
          = a n * (e2pi ((n : ℝ) * (t i₀ - δ / 2)) * e2pi (((n : ℝ) - c) * v i)) := by
            simp only [ha']; ring
        _ = a n * e2pi (((n : ℝ) * (t i₀ - δ / 2)) + ((n : ℝ) - c) * v i) := by
            rw [e2pi_add]
        _ = a n * e2pi (((n : ℝ) * t i + -(c * v i)) - ((n * ⌊ t i - t i₀ ⌋ : ℤ) : ℝ)) := by
            rw [hsum]
        _ = a n * e2pi ((n : ℝ) * t i + -(c * v i)) := by rw [e2pi_sub_int]
        _ = a n * (e2pi ((n : ℝ) * t i) * e2pi (-(c * v i))) := by rw [e2pi_add]
        _ = e2pi (-(c * v i)) * (a n * e2pi ((n : ℝ) * t i)) := by ring
    rw [hfact, norm_mul, norm_e2pi, one_mul]
  have hcoeff : ∑ n ∈ range N, ‖a' n‖ ^ 2 = ∑ n ∈ range N, ‖a n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha', norm_mul, norm_e2pi, mul_one]
  rw [hcoeff] at hkey
  refine le_trans (le_of_eq ?_) hkey
  exact (Finset.sum_congr rfl fun i hi => by rw [hterm i hi]).symm

/-- The large-values count that follows from `large_sieve_gallagher`. -/
theorem card_le_of_large_values_gallagher {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ V : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ i ∈ s, V ≤ ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖) :
    (s.card : ℝ) ≤ (δ⁻¹ + Real.pi * N) * (∑ n ∈ range N, ‖a n‖ ^ 2) / V ^ 2 := by
  have hsum := large_sieve_gallagher hδ hδ2 hsep a N
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ i ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _i ∈ s, V ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => by
          have := hbig i hi
          nlinarith [norm_nonneg (∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)), hV]
  rw [le_div_iff₀ (by positivity)]
  linarith

end LargeSieveGallagher

end RiemannHypothesis

end
