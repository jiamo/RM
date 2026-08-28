/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Xi
import RiemannHypothesis.ZeroCountLocal
import RiemannHypothesis.ZeroSum
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.Algebra.Order.Floor

/-!
# `ζ` has a nontrivial zero

Every other result in this repository about the zeroes of `ζ` inside the critical strip is an
upper bound, a symmetry, or a convergence statement: each of them is compatible with the strip
containing no zero at all.  Here that gap is closed.

The argument is Hadamard's, in the minimal form needed for the existence of a single zero:

* `exists_exp_of_ne_zero` : an entire function without zeroes is `exp ∘ g` for an entire `g`
  (integrate `f'/f`, which is entire, over the convex set `ℂ`);
* `linear_of_re_le` : an entire `g` whose real part is at most `C(1+‖z‖)log(2+‖z‖) + D` is
  **linear** — Borel–Carathéodory converts the bound on `re g` into `‖g‖ = O(R^{3/2})` on the
  ball of radius `R/2`, and Cauchy's estimate for the second derivative then gives `g'' ≡ 0`;
* `factorial_le_norm_xiFn` : on the real axis `ξ` grows faster than any exponential, because
  `ξ(2n+2) = (n+1)(2n+1)π^{-(n+1)} n! ζ(2n+2)` and `‖ζ‖ ≥ 1/2` there;
* `exists_xiFn_eq_zero` : hence `ξ` cannot be `exp` of a linear function, so it has a zero;
* `nontrivialZeroSet_nonempty`, `exists_riemannZeta_eq_zero_of_mem_strip` : a zero of `ξ` is a
  zero of `ζ` in the open critical strip.

Nothing here locates the zero: the argument is a contradiction and produces no bound on its
height, and of course says nothing about its real part.
-/

noncomputable section

open Complex Metric Filter

namespace RiemannHypothesis

/-! ## Two lemmas of complex analysis -/

/-- `log x ≤ 2 √x` for `x > 0`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  linarith

/-- **An entire function without zeroes is an exponential.**  Since `ℂ` is convex, the entire
function `f'/f` has a primitive `G`, and `f e^{-G}` is constant. -/
theorem exists_exp_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hderiv : Differentiable ℂ (deriv f) := by
    have h1 : AnalyticOnNhd ℂ f Set.univ := (hf.differentiableOn).analyticOnNhd isOpen_univ
    exact fun z => (h1.deriv z (Set.mem_univ z)).differentiableAt
  set F : ℂ → ℂ := fun z => deriv f z / f z with hF
  have hFdiff : Differentiable ℂ F := fun z => (hderiv z).div (hf z) (hne z)
  obtain ⟨G, hG⟩ := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).exists_forall_hasDerivWithinAt
    hFdiff.differentiableOn
  have hG' : ∀ z, HasDerivAt G (F z) z := fun z => by
    have := hG z (Set.mem_univ z); rwa [hasDerivWithinAt_univ] at this
  have hGdiff : Differentiable ℂ G := fun z => (hG' z).differentiableAt
  set h : ℂ → ℂ := fun z => f z * Complex.exp (-G z) with hh
  have hderiv0 : ∀ z, HasDerivAt h 0 z := by
    intro z
    have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have h2 : HasDerivAt (fun z => Complex.exp (-G z)) (-(Complex.exp (-G z) * F z)) z := by
      simpa using ((hG' z).neg).cexp
    have h3 := h1.mul h2
    have hz : deriv f z * Complex.exp (-G z) + f z * -(Complex.exp (-G z) * F z) = 0 := by
      rw [hF]
      field_simp
      rw [div_self (hne z)]
      ring
    rw [hz] at h3
    exact h3
  have hconst : ∀ z, h z = h 0 := by
    intro z
    have hd : Differentiable ℂ h := fun w => (hderiv0 w).differentiableAt
    exact is_const_of_deriv_eq_zero hd (fun w => (hderiv0 w).deriv) z 0
  have h0ne : h 0 ≠ 0 := mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => Complex.log (h 0) + G z, (differentiable_const _).add hGdiff, fun z => ?_⟩
  have hz := hconst z
  rw [Complex.exp_add, Complex.exp_log h0ne, ← hz, hh]
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  simp

/-- **An entire function whose real part grows at most like `C‖z‖ log ‖z‖` is linear.**
Borel–Carathéodory turns the one-sided bound on `re g` into a two-sided bound on `‖g‖`, and
Cauchy's estimate for the second derivative then forces `g'' ≡ 0`. -/
theorem linear_of_re_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hre : ∀ z : ℂ, (g z).re ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) + D) :
    ∃ a b : ℂ, ∀ z, g z = a + b * z := by
  set K : ℝ := 16 * C + 2 * D + 2 + 3 * ‖g 0‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  -- Step 1: the Borel–Carathéodory bound on the ball of radius `R/2`
  have hBC : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖g z‖ ≤ K * (R * Real.sqrt R) := by
    intro R hR z hz
    set M : ℝ := C * (1 + R) * Real.log (2 + R) + D + 1 with hM
    have hlogpos : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
    have hM0 : 0 < M := by positivity
    have hmaps : Set.MapsTo g (ball 0 R) {w : ℂ | w.re ≤ M} := by
      intro w hw
      have hwn : ‖w‖ < R := by simpa using hw
      have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
      have h1 : Real.log (2 + ‖w‖) ≤ Real.log (2 + R) :=
        Real.log_le_log (by linarith) (by linarith)
      have h2 : C * (1 + ‖w‖) * Real.log (2 + ‖w‖) ≤ C * (1 + R) * Real.log (2 + R) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC) h1
          (Real.log_nonneg (by linarith)) (by positivity)
      have := hre w
      simp only [Set.mem_setOf_eq, hM]
      linarith
    have hzball : z ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right]
      linarith
    have hbc := Complex.borelCaratheodory hM0 hg.differentiableOn hmaps (by linarith) hzball
    -- simplify the two quotients
    have hden : R / 2 ≤ R - ‖z‖ := by linarith
    have hden0 : 0 < R - ‖z‖ := by linarith
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hq1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
      rw [div_le_iff₀ hden0]
      nlinarith
    have hq2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
      rw [div_le_iff₀ hden0]
      nlinarith [norm_nonneg (g 0)]
    have hsum : ‖g z‖ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
    -- and bound `2M + 3‖g 0‖` by `K R √R`
    have hsq : 1 ≤ Real.sqrt R := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hR
    have hlog : Real.log (2 + R) ≤ 4 * Real.sqrt R := by
      have h1 : Real.log (2 + R) ≤ 2 * Real.sqrt (2 + R) := log_le_two_mul_sqrt (by linarith)
      have h2 : Real.sqrt (2 + R) ≤ 2 * Real.sqrt R := by
        have h3 : Real.sqrt (2 + R) ≤ Real.sqrt (4 * R) := Real.sqrt_le_sqrt (by linarith)
        have h4 : Real.sqrt (4 * R) = 2 * Real.sqrt R := by
          rw [show (4 : ℝ) * R = 2 ^ 2 * R by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
        linarith [h4 ▸ h3]
      linarith
    have hbig : 2 * M + 3 * ‖g 0‖ ≤ K * (R * Real.sqrt R) := by
      have h1 : C * (1 + R) * Real.log (2 + R) ≤ 8 * C * (R * Real.sqrt R) := by
        have hone : (1 : ℝ) + R ≤ 2 * R := by linarith
        have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC (by linarith : (0:ℝ) ≤ 1 + R))
        nlinarith [Real.sqrt_nonneg R, mul_nonneg hC (Real.sqrt_nonneg R)]
      have h2 : (1 : ℝ) ≤ R * Real.sqrt R := by nlinarith
      have h3 : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg _
      rw [hM, hK]
      nlinarith
    linarith
  -- Step 2: the second derivative vanishes
  have hsecond : ∀ w : ℂ, iteratedDeriv 2 g w = 0 := by
    intro w
    have hbound : ∀ R : ℝ, 1 ≤ R → 4 * ‖w‖ ≤ R →
        ‖iteratedDeriv 2 g w‖ ≤ 32 * K / Real.sqrt R := by
      intro R hR hwR
      have hR0 : 0 < R / 4 := by linarith
      have hsphere : ∀ z ∈ sphere w (R / 4), ‖g z‖ ≤ K * (R * Real.sqrt R) := by
        intro z hz
        have hd : ‖z - w‖ = R / 4 := by
          have : dist z w = R / 4 := hz
          rwa [Complex.dist_eq] at this
        have : ‖z‖ ≤ ‖w‖ + R / 4 := by
          have := norm_le_norm_add_norm_sub' z w
          linarith [hd.le]
        exact hBC R hR z (by linarith)
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR0
        (hg.diffContOnCl) hsphere
      have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
      have hRsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt (by linarith)
      have hkey : (2 : ℝ) * (K * (R * Real.sqrt R)) / (R / 4) ^ 2 = 32 * K / Real.sqrt R := by
        field_simp
        nlinarith [hRsq, Real.sqrt_nonneg R]
      calc ‖iteratedDeriv 2 g w‖
          ≤ (Nat.factorial 2 : ℝ) * (K * (R * Real.sqrt R)) / (R / 4) ^ 2 := hcauchy
        _ = 2 * (K * (R * Real.sqrt R)) / (R / 4) ^ 2 := by norm_num
        _ = 32 * K / Real.sqrt R := hkey
    -- let `R → ∞`
    by_contra hne
    have hpos : 0 < ‖iteratedDeriv 2 g w‖ := norm_pos_iff.mpr hne
    set ε : ℝ := ‖iteratedDeriv 2 g w‖ with hε
    set R : ℝ := max (max 1 (4 * ‖w‖)) ((32 * K / ε) ^ 2 + 1) with hRdef
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    have hR2 : 4 * ‖w‖ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
    have hR3 : (32 * K / ε) ^ 2 + 1 ≤ R := le_max_right _ _
    have hsqrt : 32 * K / ε < Real.sqrt R := by
      have h1 : (32 * K / ε) ^ 2 < R := by linarith
      have h2 : 0 < 32 * K / ε := by positivity
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ R by linarith), Real.sqrt_nonneg R]
    have hlt : 32 * K / Real.sqrt R < ε := by
      have hs0 : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
      rw [div_lt_iff₀ hs0]
      have h := (div_lt_iff₀ hpos).mp hsqrt
      nlinarith
    have := hbound R hR1 hR2
    linarith
  -- Step 3: from `g'' ≡ 0` to linearity
  have hderiv2 : ∀ w : ℂ, deriv (deriv g) w = 0 := by
    intro w
    have := hsecond w
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hderivdiff : Differentiable ℂ (deriv g) := by
    have h1 : AnalyticOnNhd ℂ g Set.univ := (hg.differentiableOn).analyticOnNhd isOpen_univ
    exact fun z => (h1.deriv z (Set.mem_univ z)).differentiableAt
  set b : ℂ := deriv g 0 with hb
  have hderivconst : ∀ z, deriv g z = b :=
    fun z => is_const_of_deriv_eq_zero hderivdiff hderiv2 z 0
  set u : ℂ → ℂ := fun z => g z - b * z with hu
  have hudiff : Differentiable ℂ u := hg.sub ((differentiable_id).const_mul b)
  have huderiv : ∀ z, deriv u z = 0 := by
    intro z
    have h1 : HasDerivAt g (deriv g z) z := (hg z).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => b * z) b z := by
      simpa using (hasDerivAt_id z).const_mul b
    have hd : HasDerivAt u (deriv g z - b) z := h1.sub h2
    rw [hd.deriv, hderivconst z, sub_self]
  refine ⟨g 0, b, fun z => ?_⟩
  have h := is_const_of_deriv_eq_zero hudiff huderiv z 0
  have hz : u z = g z - b * z := rfl
  have h0 : u 0 = g 0 := by rw [hu]; simp
  rw [hz, h0] at h
  linear_combination h

/-! ## `ξ` grows faster than any exponential on the real axis -/

/-- The exact value `‖Γ_ℝ(2(n+1))‖ = π^{-(n+1)} n!`. -/
lemma norm_Gammaℝ_even (n : ℕ) :
    ‖Gammaℝ (2 * ((n : ℂ) + 1))‖ = (Real.pi)⁻¹ ^ (n + 1) * (Nat.factorial n : ℝ) := by
  have hexp : -(2 * ((n : ℂ) + 1)) / 2 = ((-((n : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hhalf : (2 * ((n : ℂ) + 1)) / 2 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [Gammaℝ_def, hexp, hhalf, Complex.Gamma_ofReal,
    ← Complex.ofReal_cpow Real.pi_pos.le, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, Real.Gamma_nat_eq_factorial n]
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hpow : Real.pi ^ (-((n : ℝ) + 1)) = (Real.pi)⁻¹ ^ (n + 1) := by
    rw [Real.rpow_neg Real.pi_pos.le, hcast, Real.rpow_natCast, inv_pow]
  rw [hpow, abs_of_nonneg (by positivity)]

/-- **`ξ` grows faster than any exponential along the real axis**: `‖ξ(2(n+1))‖ ≥ π^{-(n+1)} n!`
for `n ≥ 1`. -/
theorem factorial_le_norm_xiFn (n : ℕ) (hn : 1 ≤ n) :
    (Real.pi)⁻¹ ^ (n + 1) * (Nat.factorial n : ℝ) ≤ ‖xiFn (2 * ((n : ℂ) + 1))‖ := by
  set s : ℂ := 2 * ((n : ℂ) + 1) with hs
  have hsre : s.re = 2 * (n + 1) := by
    rw [hs]
    simp
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hre3 : (3 : ℝ) ≤ s.re := by rw [hsre]; linarith
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hsre
    simp at hsre
    linarith
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    simp at hsre
    linarith
  have hzeta : (1 : ℝ) / 2 ≤ ‖riemannZeta s‖ := half_le_norm_riemannZeta_of_three_le_re hre3
  have hnorms : ‖s‖ = 2 * ((n : ℝ) + 1) := by
    rw [hs, ← Complex.ofReal_natCast]
    rw [show (2 : ℂ) * ((n : ℝ) + 1) = ((2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorms1 : ‖s - 1‖ = 2 * (n : ℝ) + 1 := by
    rw [hs, ← Complex.ofReal_natCast]
    rw [show (2 : ℂ) * ((n : ℝ) + 1) - 1 = ((2 * (n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [xiFn_eq_completed h0 h1, completedRiemannZeta_eq_Gammaℝ_mul (by linarith)]
  rw [show s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s)
      = (s * (s - 1) / 2) * Gammaℝ s * riemannZeta s by ring]
  rw [norm_mul, norm_mul, norm_div, norm_mul]
  rw [hnorms, hnorms1, hs, norm_Gammaℝ_even n]
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpip : (0 : ℝ) < (Real.pi)⁻¹ ^ (n + 1) := by positivity
  have hcoef : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / ‖(2 : ℂ)‖ * (1 / 2) := by
    rw [Complex.norm_ofNat]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hzeta
    (le_of_lt (mul_pos hpip hfac))
  nlinarith [mul_pos hpip hfac, norm_nonneg (riemannZeta s)]

/-! ## The existence of a zero -/

/-- **`‖ξ‖` beats every exponential along the real axis.**  There is no pair of constants with
`‖ξ(2(n+1))‖ ≤ B·Lⁿ` for all `n ≥ 1`, because `‖ξ(2(n+1))‖ ≥ π^{-(n+1)}·n!` and `n!` outgrows
every geometric sequence. -/
theorem xiFn_growth_contradiction {B L : ℝ} (hB : 0 < B)
    (h : ∀ n : ℕ, 1 ≤ n → ‖xiFn (2 * ((n : ℂ) + 1))‖ ≤ B * L ^ n) : False := by
  set B' : ℝ := B * Real.pi with hB'
  set L' : ℝ := Real.pi * L with hL'
  have hB'0 : 0 < B' := by positivity
  have hkey : ∀ n : ℕ, 1 ≤ n → (Nat.factorial n : ℝ) ≤ B' * L' ^ n := by
    intro n hn
    have hstep : (Real.pi)⁻¹ ^ (n + 1) * (Nat.factorial n : ℝ) ≤ B * L ^ n :=
      le_trans (factorial_le_norm_xiFn n hn) (h n hn)
    have hpip : (0 : ℝ) < Real.pi ^ (n + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hstep hpip.le
    have hinv : Real.pi ^ (n + 1) * ((Real.pi)⁻¹ ^ (n + 1) * (Nat.factorial n : ℝ))
        = (Nat.factorial n : ℝ) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt Real.pi_pos), one_pow, one_mul]
    have hrhs : Real.pi ^ (n + 1) * (B * L ^ n) = B' * L' ^ n := by
      rw [hB', hL', mul_pow, pow_succ]; ring
    rw [hinv, hrhs] at hmul
    exact hmul
  -- but `L'^n / n!` tends to zero
  have htend := FloorSemiring.tendsto_pow_div_factorial_atTop L'
  have hev : ∀ᶠ n : ℕ in atTop, L' ^ n / (Nat.factorial n : ℝ) < 1 / (B' + 1) :=
    Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 / (B' + 1) by positivity) htend
  obtain ⟨n, hn1, hn2⟩ := ((eventually_ge_atTop 1).and hev).exists
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 := hkey n hn1
  rw [div_lt_iff₀ hfac] at hn2
  have hBn : B' * L' ^ n < B' * (1 / (B' + 1) * (Nat.factorial n : ℝ)) :=
    mul_lt_mul_of_pos_left hn2 hB'0
  have hlast : B' * (1 / (B' + 1) * (Nat.factorial n : ℝ)) < (Nat.factorial n : ℝ) := by
    rw [← mul_assoc]
    have hlt1 : B' * (1 / (B' + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]
      linarith
    nlinarith
  linarith

/-- **`ξ` has a zero.**  If it had none, it would be `exp` of an entire function whose real part
is `O(‖z‖ log ‖z‖)`, hence of a *linear* function, and `‖ξ‖` would grow at most exponentially
along the real axis — contradicting `factorial_le_norm_xiFn`. -/
theorem exists_xiFn_eq_zero : ∃ s : ℂ, xiFn s = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC0, hC⟩ := norm_xiFn_le
  obtain ⟨g, hgdiff, hg⟩ := exists_exp_of_ne_zero differentiable_xiFn hcon
  have hre : ∀ z : ℂ, (g z).re ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) + 0 := by
    intro z
    have h1 : Real.exp ((g z).re) = ‖xiFn z‖ := by
      rw [hg z, Complex.norm_exp]
    have h2 : Real.exp ((g z).re) ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
      rw [h1]; exact hC z
    have := Real.exp_le_exp.mp h2
    linarith
  obtain ⟨a, b, hab⟩ := linear_of_re_le hgdiff hC0.le le_rfl hre
  -- the exponential upper bound along the real axis
  set A : ℝ := Real.exp ‖a‖ with hA
  have hupper : ∀ n : ℕ, ‖xiFn (2 * ((n : ℂ) + 1))‖ ≤ A * Real.exp (2 * ‖b‖ * ((n : ℝ) + 1)) := by
    intro n
    have hz : ‖(2 * ((n : ℂ) + 1) : ℂ)‖ = 2 * ((n : ℝ) + 1) := by
      rw [← Complex.ofReal_natCast]
      rw [show (2 : ℂ) * ((n : ℝ) + 1) = ((2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hg, Complex.norm_exp, hab]
    have h1 : (a + b * (2 * ((n : ℂ) + 1))).re ≤ ‖a‖ + 2 * ‖b‖ * ((n : ℝ) + 1) := by
      have h2 : (a + b * (2 * ((n : ℂ) + 1))).re ≤ ‖a + b * (2 * ((n : ℂ) + 1))‖ :=
        Complex.re_le_norm _
      have h3 : ‖a + b * (2 * ((n : ℂ) + 1))‖ ≤ ‖a‖ + ‖b‖ * ‖(2 * ((n : ℂ) + 1) : ℂ)‖ := by
        calc ‖a + b * (2 * ((n : ℂ) + 1))‖ ≤ ‖a‖ + ‖b * (2 * ((n : ℂ) + 1))‖ :=
              norm_add_le _ _
          _ = ‖a‖ + ‖b‖ * ‖(2 * ((n : ℂ) + 1) : ℂ)‖ := by rw [norm_mul]
      rw [hz] at h3
      linarith
    calc Real.exp ((a + b * (2 * ((n : ℂ) + 1))).re)
        ≤ Real.exp (‖a‖ + 2 * ‖b‖ * ((n : ℝ) + 1)) := Real.exp_le_exp.mpr h1
      _ = A * Real.exp (2 * ‖b‖ * ((n : ℝ) + 1)) := by rw [hA, ← Real.exp_add]
  -- the factorial beats it
  refine xiFn_growth_contradiction (B := A * Real.exp (2 * ‖b‖)) (L := Real.exp (2 * ‖b‖))
    (by positivity) fun n _ => ?_
  refine le_trans (hupper n) (le_of_eq ?_)
  have hexp : Real.exp (2 * ‖b‖ * ((n : ℝ) + 1))
      = Real.exp (2 * ‖b‖) * (Real.exp (2 * ‖b‖)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, mul_assoc]


/-- **The critical strip contains a zero of `ζ`.** -/
theorem nontrivialZeroSet_nonempty : nontrivialZeroSet.Nonempty := by
  obtain ⟨s, hs⟩ := exists_xiFn_eq_zero
  have hxi : riemannXi (-I * (s - 1 / 2)) = 0 := by
    rw [riemannXi_eq_xiFn, xiPoint_neg_I_mul_sub]
    exact hs
  obtain ⟨h0, h1, hz⟩ := riemannXi_eq_zero_iff.mp hxi
  rw [xiPoint_neg_I_mul_sub] at h0 h1 hz
  exact ⟨s, hz, h0, h1⟩

/-- **`ζ` has a zero in the open critical strip.** -/
theorem exists_riemannZeta_eq_zero_of_mem_strip :
    ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  obtain ⟨s, hs⟩ := nontrivialZeroSet_nonempty
  exact ⟨s, hs.1, hs.2.1, hs.2.2⟩

end RiemannHypothesis
