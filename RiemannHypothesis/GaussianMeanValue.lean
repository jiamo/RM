/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Dist
import RiemannHypothesis.MollifiedMeanSquare

/-!
# The mean value theorem for Dirichlet polynomials, in Montgomery–Vaughan shape

`RiemannHypothesis/DirichletPolyMeanValue.lean` proves the elementary mean value theorem

`∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`,

whose error term `N log N` sits *outside* the sum.  For the density arguments what one needs is
the Montgomery–Vaughan shape, with the error term *inside* the sum:

`∫₋ᵀᵀ ‖D(σ + i t)‖² dt ≤ C ∑_{n ≤ N} ‖a n‖² n^(-2σ) (T + n)`.

This is proved here, with an explicit (but not optimal) constant, by the Gaussian majorant
method rather than by Montgomery and Vaughan's generalized Hilbert inequality: on `[-T, T]` the
indicator is at most `e · exp (-t²/T²)`, and the Gaussian weight turns the mean square into the
absolutely convergent bilinear form

`√π T ∑_{m, n} c_m c_n exp (-T² (log n - log m)² / 4)`,

whose row sums are bounded by `1 + 6 · 2m/T` because the integers `n` with `log n` within `1/L`
of `log m` number `O(1 + m/L)`.

## Main results

* `integral_exp_mul_I_gaussian` — `∫ exp (i θ t) exp (-b t²) dt = √(π/b) exp (-θ²/(4b))`.
* `integral_normSq_dirichletPoly_gaussian_le` — the Gaussian-weighted mean square is at most
  `√(π/b)` times the bilinear form above.
* `sum_exp_neg_sq_log_sub_le` — the row sum bound `∑_{n ≤ N} exp (-L² (log n - log m)²)
  ≤ 1 + 6 m / L` for `L ≥ 3`.
* `integral_normSq_dirichletPoly_le_mv` — the mean value theorem in Montgomery–Vaughan shape,
  over `[-T, T]`, and `integral_Icc_normSq_dirichletPoly_le_mv`, its corollary over `[0, T]`.

## Scope

The constant obtained here is `58`, not the sharp `1 + o(1)` of Montgomery and Vaughan (whose
theorem gives `∫₀ᵀ = ∑ ‖a n‖² n^(-2σ) (T + O(n))` with an asymptotically optimal main term).
Only the *shape* of the error term matters for the applications, and no sharp constant is
claimed.
-/

noncomputable section

open Complex MeasureTheory Finset

namespace RiemannHypothesis

/-! ## The Gaussian oscillatory integral -/

/-- `∫_ℝ exp (i θ t) exp (-b t²) dt = √(π/b) exp (-θ²/(4b))` for `b > 0`. -/
theorem integral_exp_mul_I_gaussian (b θ : ℝ) (hb : 0 < b) :
    ∫ t : ℝ, Complex.exp ((t : ℂ) * θ * I) * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)
      = ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have hb' : (0 : ℝ) < ((b : ℂ)).re := by simpa using hb
  have h := fourierIntegral_gaussian (b := (b : ℂ)) hb' (θ : ℂ)
  rw [show (fun x : ℝ => Complex.exp ((x : ℂ) * θ * I) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) =
      (fun x : ℝ => Complex.exp (I * (θ : ℂ) * x) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) by
    funext x; ring_nf]
  rw [h]
  have h2 : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow,
      show ((Real.pi : ℂ) / (b : ℂ)) = (((Real.pi / b : ℝ)) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
  rw [h2, show (-(θ : ℂ) ^ 2 / (4 * (b : ℂ))) = (((-θ ^ 2 / (4 * b) : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  push_cast
  ring

/-- The Gaussian-weighted oscillating factor is integrable. -/
theorem integrable_exp_mul_I_gaussian {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((t : ℂ) * θ * I) * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) := by
  have hb' : (0 : ℝ) < ((b : ℂ)).re := by simpa using hb
  have h := integrable_cexp_quadratic (b := (b : ℂ)) hb' ((θ : ℂ) * I) 0
  refine h.congr ?_
  filter_upwards with t
  rw [← Complex.exp_add]
  ring_nf

/-! ## The Gaussian-weighted mean square -/

/-- The Gaussian-weighted term of the expanded square, as the real part of a constant times the
Gaussian-weighted oscillating factor. -/
theorem meanSquareTerm_mul_gaussian_re (a : ℕ → ℂ) (σ b : ℝ) (m n : ℕ) (t : ℝ) :
    (meanSquareTerm a σ m n t).re * Real.exp (-(b * t ^ 2))
      = ((a m * (starRingEnd ℂ) (a n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)) *
          (Complex.exp ((t : ℂ) * ((Real.log n - Real.log m : ℝ)) * I) *
            Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re := by
  have hre : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r := by intro z r; simp
  have hgauss : Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2) = ((Real.exp (-(b * t ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have h1 : meanSquareTerm a σ m n t
      = (a m * (starRingEnd ℂ) (a n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)) *
        Complex.exp ((t : ℂ) * ((Real.log n - Real.log m : ℝ)) * I) := rfl
  rw [h1, hgauss, ← mul_assoc, hre]

/-- Each Gaussian-weighted term of the expanded square is integrable. -/
theorem integrable_meanSquareTerm_gaussian (a : ℕ → ℂ) (σ : ℝ) {b : ℝ} (hb : 0 < b) (m n : ℕ) :
    Integrable (fun t : ℝ => (meanSquareTerm a σ m n t).re * Real.exp (-(b * t ^ 2))) := by
  rw [funext (meanSquareTerm_mul_gaussian_re a σ b m n)]
  exact ((integrable_exp_mul_I_gaussian hb (Real.log n - Real.log m)).const_mul _).re

/-- The Gaussian-weighted contribution of a single pair `(m, n)`. -/
theorem integral_meanSquareTerm_gaussian_le (a : ℕ → ℂ) (σ : ℝ) {b : ℝ} (hb : 0 < b) (m n : ℕ) :
    (∫ t : ℝ, (meanSquareTerm a σ m n t).re * Real.exp (-(b * t ^ 2)))
      ≤ Real.sqrt (Real.pi / b) * ((‖a m‖ * (m : ℝ) ^ (-σ)) * (‖a n‖ * (n : ℝ) ^ (-σ)) *
          Real.exp (-(Real.log n - Real.log m) ^ 2 / (4 * b))) := by
  set K : ℂ := a m * (starRingEnd ℂ) (a n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hK
  set θ : ℝ := Real.log n - Real.log m with hθ
  rw [funext (meanSquareTerm_mul_gaussian_re a σ b m n)]
  have hint : Integrable (fun t : ℝ => K * (Complex.exp ((t : ℂ) * θ * I) *
      Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))) := (integrable_exp_mul_I_gaussian hb θ).const_mul K
  rw [show (∫ t : ℝ, (K * (Complex.exp ((t : ℂ) * θ * I) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re)
      = (∫ t : ℝ, K * (Complex.exp ((t : ℂ) * θ * I) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re by
    simpa using (Complex.reCLM.integral_comp_comm hint)]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_I_gaussian b θ hb]
  calc (K * ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ)).re
      ≤ ‖K * ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ)‖ :=
        Complex.re_le_norm _
    _ = ‖K‖ * (Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = _ := by
        have h1 : ‖(((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)‖
            = (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hK, norm_mul, norm_mul, h1, RCLike.norm_conj]
        ring

/-- The Gaussian-weighted mean square of a Dirichlet polynomial is at most `√(π/b)` times the
bilinear form with kernel `exp (-(log n - log m)²/(4b))`. -/
theorem integral_normSq_dirichletPoly_gaussian_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {b : ℝ}
    (hb : 0 < b) :
    (∫ t : ℝ, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * Real.exp (-(b * t ^ 2)))
      ≤ Real.sqrt (Real.pi / b) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (‖a m‖ * (m : ℝ) ^ (-σ)) * (‖a n‖ * (n : ℝ) ^ (-σ)) *
            Real.exp (-(Real.log n - Real.log m) ^ 2 / (4 * b)) := by
  have hexp : ∀ t : ℝ, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * Real.exp (-(b * t ^ 2))
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          ((meanSquareTerm a σ m n t).re * Real.exp (-(b * t ^ 2))) := by
    intro t
    rw [normSq_dirichletPoly_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_mul _ _ _
  rw [funext hexp]
  rw [MeasureTheory.integral_finsetSum _ fun m _ =>
    MeasureTheory.integrable_finsetSum _ fun n _ => integrable_meanSquareTerm_gaussian a σ hb m n]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun n _ => integrable_meanSquareTerm_gaussian a σ hb m n,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => integral_meanSquareTerm_gaussian_le a σ hb m n

/-! ## The row sums of the Gaussian kernel -/

/-- The integral test for the Gaussian: `∑_{k = 1}^{K} exp (-α k²) ≤ √(π/α)/2`. -/
theorem sum_Icc_exp_neg_mul_sq_le {α : ℝ} (hα : 0 < α) (K : ℕ) :
    ∑ k ∈ Icc 1 K, Real.exp (-(α * (k : ℝ) ^ 2)) ≤ Real.sqrt (Real.pi / α) / 2 := by
  have hrw : ∑ k ∈ Icc 1 K, Real.exp (-(α * (k : ℝ) ^ 2))
      = ∑ i ∈ Finset.range K, Real.exp (-(α * ((i : ℕ) + 1 : ℕ) ^ 2)) := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  set f : ℝ → ℝ := fun x => Real.exp (-(α * x ^ 2)) with hf
  have hanti : AntitoneOn f (Set.Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    simp only [hf]
    refine Real.exp_le_exp.2 ?_
    have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith
  have hint : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_exp_neg_mul_sq hα).integrableOn (s := Set.Ioi (0 : ℝ))
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro x _; simp only [hf]; ring_nf
  have hstep := (hanti.mono (by
    intro x hx
    exact Set.mem_Ici.2 hx.1 : Set.Icc (0 : ℝ) (0 + (K : ℕ)) ⊆ Set.Ici (0 : ℝ))).sum_le_integral
  have hle : ∫ x in (0 : ℝ)..(0 + (K : ℕ) : ℝ), f x ≤ ∫ x in Set.Ioi (0 : ℝ), f x := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact setIntegral_mono_set hint (.of_forall fun x => (Real.exp_pos _).le)
      (LE.le.eventuallyLE Set.Ioc_subset_Ioi_self)
  have hgauss : ∫ x in Set.Ioi (0 : ℝ), f x = Real.sqrt (Real.pi / α) / 2 := by
    rw [show (fun x : ℝ => f x) = (fun x : ℝ => Real.exp (-α * x ^ 2)) by
      funext x; simp only [hf]; ring_nf]
    exact integral_gaussian_Ioi α
  rw [hrw]
  refine le_trans ?_ (hstep.trans (hle.trans hgauss.le))
  refine Finset.sum_le_sum fun i _ => le_of_eq ?_
  simp only [hf]
  norm_num

/-- A lower bound for the separation of logarithms in terms of the separation of the points. -/
theorem abs_log_sub_log_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |y - x| / max x y ≤ |Real.log y - Real.log x| := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonneg (by linarith), abs_of_nonneg
      (by simpa using Real.log_le_log hx h)]
    have hlog := Real.log_le_sub_one_of_pos (x := x / y) (by positivity)
    rw [Real.log_div hx.ne' hy.ne'] at hlog
    rw [div_le_iff₀ hy]
    have hxy : x / y * y = x := div_mul_cancel₀ _ hy.ne'
    nlinarith [hlog]
  · rw [max_eq_left h, abs_of_nonpos (by linarith), abs_of_nonpos
      (by simpa using Real.log_le_log hy h)]
    have hlog := Real.log_le_sub_one_of_pos (x := y / x) (by positivity)
    rw [Real.log_div hy.ne' hx.ne'] at hlog
    rw [div_le_iff₀ hx]
    have hxy : y / x * x = y := div_mul_cancel₀ _ hx.ne'
    nlinarith [hlog]

/-- The natural distance, cast to `ℝ`, is the absolute difference. -/
theorem cast_natDist (n m : ℕ) : ((Nat.dist n m : ℕ) : ℝ) = |(n : ℝ) - (m : ℝ)| := by
  rcases le_total n m with h | h
  · have h' : (n : ℝ) ≤ m := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, abs_of_nonpos (by linarith), Nat.cast_sub h]; ring
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, abs_of_nonneg (by linarith), Nat.cast_sub h]

/-- The telescoping bound for the tail of `∑ 1/n²`. -/
theorem sum_Ioc_inv_sq_le' {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((max M N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rcases le_or_gt (N + 1) M with h | h
      · rw [Finset.Ioc_eq_empty (by omega), max_eq_left h]
        simp
      · have hMN : M ≤ N := by omega
        have hN1 : 1 ≤ N := le_trans hM hMN
        rw [Finset.sum_Ioc_succ_top (by omega), max_eq_right (by omega)]
        rw [max_eq_right hMN] at ih
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
        have hstep : 1 / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith [hNpos]
        push_cast
        linarith

/-- `∑_{M < n ≤ N} 1/n² ≤ 1/M`. -/
theorem sum_Ioc_inv_sq_le {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  have h := sum_Ioc_inv_sq_le' hM N
  have h2 : (0 : ℝ) ≤ 1 / ((max M N : ℕ) : ℝ) := by positivity
  linarith

/-! ### The near range `n ≤ 2m` -/

/-- Summing a Gaussian in the natural distance to a fixed point `m`. -/
theorem sum_dist_sq_le {α : ℝ} (hα : 0 < α) (m K : ℕ) :
    ∑ n ∈ Ioc 0 K, Real.exp (-(α * ((Nat.dist n m : ℕ) : ℝ) ^ 2))
      ≤ 1 + Real.sqrt (Real.pi / α) := by
  set s : Finset ℕ := Ioc 0 K with hs
  set g : ℕ → ℝ := fun n => Real.exp (-(α * ((Nat.dist n m : ℕ) : ℝ) ^ 2)) with hg
  have hgnn : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hdisj : Disjoint (s.filter (· < m)) (s.filter (fun n => m < n)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_filter] at hx hx2
    omega
  have hsub : s ⊆ insert m (s.filter (· < m) ∪ s.filter (fun n => m < n)) := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    rcases lt_trichotomy n m with h | h | h
    · exact Or.inr (Or.inl ⟨hn, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hn, h⟩)
  have hmem : m ∉ s.filter (· < m) ∪ s.filter (fun n => m < n) := by
    simp only [Finset.mem_union, Finset.mem_filter]
    omega
  have hsplit : ∑ n ∈ s, g n ≤ g m + (∑ n ∈ s.filter (· < m), g n
      + ∑ n ∈ s.filter (fun n => m < n), g n) := by
    calc ∑ n ∈ s, g n ≤ ∑ n ∈ insert m (s.filter (· < m) ∪ s.filter (fun n => m < n)), g n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hgnn i)
      _ = g m + ∑ n ∈ (s.filter (· < m) ∪ s.filter (fun n => m < n)), g n :=
          Finset.sum_insert hmem
      _ = _ := by rw [Finset.sum_union hdisj]
  have hgm : g m = 1 := by simp [hg]
  have h1 : ∑ n ∈ s.filter (· < m), g n ≤ Real.sqrt (Real.pi / α) / 2 := by
    have hinj : ∀ x ∈ s.filter (· < m), ∀ y ∈ s.filter (· < m), m - x = m - y → x = y := by
      intro x hx y hy h
      simp only [Finset.mem_filter] at hx hy
      omega
    have hrw : ∑ n ∈ s.filter (· < m), g n
        = ∑ k ∈ (s.filter (· < m)).image (fun n => m - n),
            Real.exp (-(α * (k : ℝ) ^ 2)) := by
      rw [Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_filter] at hn
      simp only [hg, show Nat.dist n m = m - n by simp only [Nat.dist]; omega]
    rw [hrw]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (Real.exp_pos _).le))
      (sum_Icc_exp_neg_mul_sq_le hα m)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter] at hk
    obtain ⟨n, ⟨hn, hnm⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]
    omega
  have h2 : ∑ n ∈ s.filter (fun n => m < n), g n ≤ Real.sqrt (Real.pi / α) / 2 := by
    have hinj : ∀ x ∈ s.filter (fun n => m < n), ∀ y ∈ s.filter (fun n => m < n),
        x - m = y - m → x = y := by
      intro x hx y hy h
      simp only [Finset.mem_filter] at hx hy
      omega
    have hrw : ∑ n ∈ s.filter (fun n => m < n), g n
        = ∑ k ∈ (s.filter (fun n => m < n)).image (fun n => n - m),
            Real.exp (-(α * (k : ℝ) ^ 2)) := by
      rw [Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_filter] at hn
      simp only [hg, show Nat.dist n m = n - m by simp only [Nat.dist]; omega]
    rw [hrw]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (Real.exp_pos _).le))
      (sum_Icc_exp_neg_mul_sq_le hα K)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, hs, Finset.mem_Ioc] at hk
    obtain ⟨n, ⟨hn, hnm⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]
    omega
  rw [hgm] at hsplit
  linarith

/-- In the near range the logarithmic separation dominates `dist n m / (2m)`. -/
theorem exp_neg_sq_log_sub_le_near {L : ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn0 : 0 < n)
    (hn : n ≤ 2 * m) :
    Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ Real.exp (-(L ^ 2 / (4 * (m : ℝ) ^ 2) * ((Nat.dist n m : ℕ) : ℝ) ^ 2)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnle : (n : ℝ) ≤ 2 * m := by exact_mod_cast hn
  refine Real.exp_le_exp.2 ?_
  have hkey := abs_log_sub_log_ge hmpos hnpos
  have hmax : max (m : ℝ) (n : ℝ) ≤ 2 * m := max_le (by linarith) hnle
  have hd : ((Nat.dist n m : ℕ) : ℝ) = |(n : ℝ) - (m : ℝ)| := cast_natDist n m
  have h1 : ((Nat.dist n m : ℕ) : ℝ) / (2 * m) ≤ |Real.log n - Real.log m| := by
    rw [hd]
    refine le_trans ?_ hkey
    exact div_le_div_of_nonneg_left (abs_nonneg _)
      (lt_of_lt_of_le hmpos (le_max_left _ _)) hmax
  have h2 : (((Nat.dist n m : ℕ) : ℝ) / (2 * m)) ^ 2 ≤ (Real.log n - Real.log m) ^ 2 := by
    calc (((Nat.dist n m : ℕ) : ℝ) / (2 * m)) ^ 2
        ≤ |Real.log n - Real.log m| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = (Real.log n - Real.log m) ^ 2 := sq_abs _
  have hL2 : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  have h3 : L ^ 2 / (4 * (m : ℝ) ^ 2) * ((Nat.dist n m : ℕ) : ℝ) ^ 2
      = L ^ 2 * (((Nat.dist n m : ℕ) : ℝ) / (2 * m)) ^ 2 := by
    field_simp; ring
  rw [h3]
  have h4 := mul_le_mul_of_nonneg_left h2 hL2
  linarith

/-- The near part of the row sum. -/
theorem sum_near_le {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 1 ≤ m) {K : ℕ} (hK : K ≤ 2 * m) :
    ∑ n ∈ Ioc 0 K, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ 1 + 2 * Real.sqrt Real.pi * m / L := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set α : ℝ := L ^ 2 / (4 * (m : ℝ) ^ 2) with hαdef
  have hα : 0 < α := by rw [hαdef]; positivity
  have step1 : ∑ n ∈ Ioc 0 K, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ ∑ n ∈ Ioc 0 K, Real.exp (-(α * ((Nat.dist n m : ℕ) : ℝ) ^ 2)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    exact exp_neg_sq_log_sub_le_near hm hn.1 (le_trans hn.2 hK)
  have hsqrt : Real.sqrt (Real.pi / α) = 2 * Real.sqrt Real.pi * m / L := by
    have h : Real.pi / α = Real.pi * (2 * m / L) ^ 2 := by
      rw [hαdef]; field_simp; ring
    rw [h, Real.sqrt_mul Real.pi_nonneg, Real.sqrt_sq (by positivity)]
    ring
  have hmain := sum_dist_sq_le hα m K
  rw [hsqrt] at hmain
  linarith

/-! ### The far range `n > 2m` -/

/-- In the far range the Gaussian kernel is dominated by `m²/n²` times a constant. -/
theorem exp_neg_sq_log_sub_le_far {L : ℝ} (hL : 3 ≤ L) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 2 * m < n) :
    Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) *
          Real.exp (-(L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set u : ℝ := Real.log n - Real.log m with hu
  have hlog2 : Real.log 2 < u := by
    have h1 : Real.log (2 * m) < Real.log n := by
      apply Real.log_lt_log (by positivity)
      exact_mod_cast hn
    rw [Real.log_mul (by norm_num) hmpos.ne'] at h1
    simp only [hu]; linarith
  have e1 : Real.exp (2 * Real.log m) = (m : ℝ) ^ 2 := by
    rw [show (2 : ℝ) * Real.log m = Real.log m + Real.log m by ring, Real.exp_add,
      Real.exp_log hmpos]; ring
  have e2 : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
    rw [show (2 : ℝ) * Real.log n = Real.log n + Real.log n by ring, Real.exp_add,
      Real.exp_log hnpos]; ring
  have hratio : ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) = Real.exp (-(2 * u)) := by
    rw [hu, show -(2 * (Real.log n - Real.log m)) = 2 * Real.log m - 2 * Real.log n by ring,
      Real.exp_sub, e1, e2]
  rw [hratio, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : 0 ≤ (u - Real.log 2) * (L ^ 2 * (u + Real.log 2) - 2) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [Real.log_two_gt_d9]
  nlinarith [hkey]

/-- The constant appearing in the far-range bound is at most `4/L`. -/
theorem exp_far_const_bound {L : ℝ} (hL : 3 ≤ L) :
    Real.exp (-(L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)) ≤ 4 / L := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hsq2 : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith [Real.log_two_gt_d9]
  have hlt : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hx : L / 4 ≤ Real.exp (L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2) := by
    have h1 : 1 + (L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)
        ≤ Real.exp (L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2) := by
      have h := Real.add_one_le_exp (L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)
      linarith
    nlinarith [sq_nonneg L, hsq2, hlt]
  have hpos := Real.exp_pos (L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos hLpos]
  linarith

/-- The far part of the row sum. -/
theorem sum_far_le {L : ℝ} (hL : 3 ≤ L) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ n ∈ Ioc (2 * m) N, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ 2 * m / L := by
  set C : ℝ := Real.exp (-(L ^ 2 * Real.log 2 ^ 2 - 2 * Real.log 2)) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hLpos : (0 : ℝ) < L := by linarith
  have step1 : ∑ n ∈ Ioc (2 * m) N, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ ∑ n ∈ Ioc (2 * m) N, ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) * C :=
    Finset.sum_le_sum fun n hn =>
      exp_neg_sq_log_sub_le_far hL hm (Finset.mem_Ioc.mp hn).1
  have step2 : ∑ n ∈ Ioc (2 * m) N, ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) * C
      = (m : ℝ) ^ 2 * C * ∑ n ∈ Ioc (2 * m) N, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have step3 : ∑ n ∈ Ioc (2 * m) N, 1 / (n : ℝ) ^ 2 ≤ 1 / ((2 * m : ℕ) : ℝ) :=
    sum_Ioc_inv_sq_le (by omega) N
  have hCle : C ≤ 4 / L := exp_far_const_bound hL
  have h4 : (m : ℝ) ^ 2 * C * (1 / ((2 * m : ℕ) : ℝ)) = m * C / 2 := by
    push_cast
    field_simp
  calc ∑ n ∈ Ioc (2 * m) N, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ (m : ℝ) ^ 2 * C * ∑ n ∈ Ioc (2 * m) N, 1 / (n : ℝ) ^ 2 := by rw [← step2]; exact step1
    _ ≤ (m : ℝ) ^ 2 * C * (1 / ((2 * m : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left step3 (by positivity)
    _ = m * C / 2 := h4
    _ ≤ m * (4 / L) / 2 := by gcongr
    _ = 2 * m / L := by field_simp; ring

/-- The Gaussian row sum: at most `1 + 6 m / L` integers `n` contribute, in the weighted sense,
to `∑_n exp (-L² (log n - log m)²)`. -/
theorem sum_exp_neg_sq_log_sub_le {L : ℝ} (hL : 3 ≤ L) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ 1 + 6 * m / L := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  have hIcc : Icc 1 N = Ioc 0 N := by ext x; simp [Nat.lt_iff_add_one_le]
  rw [hIcc]
  have hA : 2 * Real.sqrt Real.pi * (m : ℝ) + 2 * m ≤ 6 * m := by nlinarith [hpi, hmpos]
  have hB : (2 * Real.sqrt Real.pi * (m : ℝ) + 2 * m) / L ≤ 6 * m / L := by gcongr
  have heq : 2 * Real.sqrt Real.pi * (m : ℝ) / L + 2 * m / L
      = (2 * Real.sqrt Real.pi * (m : ℝ) + 2 * m) / L := by ring
  rcases le_total (2 * m) N with h | h
  · rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) h]
    have h1 := sum_near_le hLpos hm (le_refl (2 * m))
    have h2 := sum_far_le hL hm N
    linarith
  · have h1 := sum_near_le hLpos hm h
    have h2 : (0 : ℝ) ≤ 2 * m / L := by positivity
    linarith

/-! ## The Schur bound for the bilinear form -/

/-- **Schur's test** for the symmetric Gaussian kernel: the bilinear form is bounded by the
diagonal weighted by the row sums. -/
theorem bilinear_gaussian_kernel_le {L : ℝ} (hL : 3 ≤ L) (c : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        c m * c n * Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ ∑ m ∈ Icc 1 N, c m ^ 2 * (1 + 6 * m / L) := by
  have hLpos : (0 : ℝ) < L := by linarith
  set K : ℕ → ℕ → ℝ := fun m n => Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2)) with hK
  have hKsymm : ∀ m n : ℕ, K m n = K n m := by
    intro m n; simp only [hK]; ring_nf
  have hKnn : ∀ m n : ℕ, 0 ≤ K m n := fun m n => (Real.exp_pos _).le
  have hstep : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * K m n
      ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (c m ^ 2 * K m n + c n ^ 2 * K m n) / 2 := by
    refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
    nlinarith [sq_nonneg (c m - c n), hKnn m n]
  have hsplit : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (c m ^ 2 * K m n + c n ^ 2 * K m n) / 2
      = (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m ^ 2 * K m n) / 2
        + (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c n ^ 2 * K m n) / 2 := by
    have e1 : ∀ m, ∑ n ∈ Icc 1 N, (c m ^ 2 * K m n + c n ^ 2 * K m n) / 2
        = (∑ n ∈ Icc 1 N, c m ^ 2 * K m n) / 2 + (∑ n ∈ Icc 1 N, c n ^ 2 * K m n) / 2 := by
      intro m
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [Finset.sum_congr rfl (fun m _ => e1 m), Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
  have hrow : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c n ^ 2 * K m n
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m ^ 2 * K m n := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by rw [hKsymm]
  have hdiag : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m ^ 2 * K m n
      ≤ ∑ m ∈ Icc 1 N, c m ^ 2 * (1 + 6 * m / L) := by
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (c m))
    exact sum_exp_neg_sq_log_sub_le hL (Finset.mem_Icc.mp hm).1 N
  rw [hsplit, hrow] at hstep
  linarith

/-! ## The mean value theorem -/

/-- The Gaussian-weighted mean square is integrable on the whole line. -/
theorem integrable_normSq_dirichletPoly_gaussian (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {b : ℝ}
    (hb : 0 < b) :
    Integrable (fun t : ℝ =>
      ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * Real.exp (-(b * t ^ 2))) := by
  have hexp : ∀ t : ℝ, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * Real.exp (-(b * t ^ 2))
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          ((meanSquareTerm a σ m n t).re * Real.exp (-(b * t ^ 2))) := by
    intro t
    rw [normSq_dirichletPoly_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_mul _ _ _
  rw [funext hexp]
  exact MeasureTheory.integrable_finsetSum _ fun m _ =>
    MeasureTheory.integrable_finsetSum _ fun n _ =>
      integrable_meanSquareTerm_gaussian a σ hb m n

/-- The numerical constant: `e √π ≤ 4.8182`. -/
theorem exp_one_mul_sqrt_pi_le : Real.exp 1 * Real.sqrt Real.pi ≤ 4.8182 := by
  have he : Real.exp 1 ≤ 2.7183 := le_of_lt (by linarith [Real.exp_one_lt_d9])
  have hpi : Real.sqrt Real.pi ≤ 1.7725 := by
    rw [show (1.7725 : ℝ) = Real.sqrt (1.7725 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d6])
  have h0 : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  nlinarith [Real.exp_pos 1]

/-- **The mean value theorem for Dirichlet polynomials, in Montgomery–Vaughan shape.**  For
`T ≥ 6`,
`∫₋ᵀᵀ ‖D(σ + i t)‖² dt ≤ 58 ∑_{n ≤ N} ‖a n‖² n^(-2σ) (T + n)`. -/
theorem integral_normSq_dirichletPoly_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hT0 : T ≠ 0 := ne_of_gt hTpos
  have hb : (0 : ℝ) < 1 / T ^ 2 := by positivity
  have hL : (3 : ℝ) ≤ T / 2 := by linarith
  have hFint : Integrable (fun t : ℝ =>
      ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * Real.exp (-(1 / T ^ 2 * t ^ 2))) :=
    integrable_normSq_dirichletPoly_gaussian a N σ hb
  have hFnn : ∀ t : ℝ, 0 ≤ ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
      Real.exp (-(1 / T ^ 2 * t ^ 2)) := fun t => by positivity
  have hcont := continuous_normSq_dirichletPoly_line' a N σ
  have step1 : (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ Real.exp 1 * ∫ t : ℝ, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          Real.exp (-(1 / T ^ 2 * t ^ 2)) := by
    have hmono : (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ ∫ t in (-T)..T, Real.exp 1 * (‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
            Real.exp (-(1 / T ^ 2 * t ^ 2))) := by
      refine intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        (hFint.const_mul (Real.exp 1)).intervalIntegrable ?_
      intro t ht
      simp only [Set.mem_Icc] at ht
      have habs : 1 / T ^ 2 * t ^ 2 ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        nlinarith [ht.1, ht.2]
      have h1 : (1 : ℝ) ≤ Real.exp 1 * Real.exp (-(1 / T ^ 2 * t ^ 2)) := by
        rw [← Real.exp_add]
        have h := Real.add_one_le_exp (1 + -(1 / T ^ 2 * t ^ 2))
        linarith
      have hnn : (0 : ℝ) ≤ ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hnn]
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le)
    rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
    exact MeasureTheory.setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
  have step2 := integral_normSq_dirichletPoly_gaussian_le a N σ hb
  have hker : ∀ x : ℝ, -x ^ 2 / (4 * (1 / T ^ 2)) = -((T / 2) ^ 2 * x ^ 2) := by
    intro x; field_simp; ring
  have hsq : Real.sqrt (Real.pi / (1 / T ^ 2)) = Real.sqrt Real.pi * T := by
    rw [show Real.pi / (1 / T ^ 2) = Real.pi * T ^ 2 by field_simp,
      Real.sqrt_mul Real.pi_nonneg, Real.sqrt_sq hTpos.le]
  simp only [hker, hsq] at step2
  have step3 := bilinear_gaussian_kernel_le hL (fun m => ‖a m‖ * (m : ℝ) ^ (-σ)) N
  have step4 : Real.exp 1 * (Real.sqrt Real.pi * T *
      ∑ m ∈ Icc 1 N, (‖a m‖ * (m : ℝ) ^ (-σ)) ^ 2 * (1 + 6 * m / (T / 2)))
      ≤ 58 * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hpow : ((m : ℝ) ^ (-σ)) ^ 2 = (m : ℝ) ^ (-2 * σ) := by
      rw [sq, ← Real.rpow_add hmpos]
      congr 1
      ring
    have hA : (0 : ℝ) ≤ ‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) := by positivity
    have hfin : Real.exp 1 * Real.sqrt Real.pi * (T + 12 * m) ≤ 58 * (T + m) := by
      nlinarith [exp_one_mul_sqrt_pi_le, hmpos, hTpos, Real.sqrt_nonneg Real.pi,
        Real.exp_pos 1]
    calc Real.exp 1 * (Real.sqrt Real.pi * T *
          ((‖a m‖ * (m : ℝ) ^ (-σ)) ^ 2 * (1 + 6 * m / (T / 2))))
        = (Real.exp 1 * Real.sqrt Real.pi * (T + 12 * m)) *
            (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)) := by
          rw [mul_pow, hpow]; field_simp; ring
      _ ≤ (58 * (T + m)) * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)) :=
          mul_le_mul_of_nonneg_right hfin hA
      _ = 58 * (‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) * (T + m)) := by ring
  refine step1.trans (le_trans (mul_le_mul_of_nonneg_left step2 (Real.exp_pos 1).le) ?_)
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left step3 (by positivity)) (Real.exp_pos 1).le) step4

/-- The same over `[0, T]`. -/
theorem integral_Icc_normSq_dirichletPoly_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hcont := continuous_normSq_dirichletPoly_line' a N σ
  have hadd : (∫ t in (-T)..(0 : ℝ), ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      + (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      = ∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hnn : (0 : ℝ) ≤ ∫ t in (-T)..(0 : ℝ), ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hmain := integral_normSq_dirichletPoly_le_mv a N σ hT
  linarith

end RiemannHypothesis
