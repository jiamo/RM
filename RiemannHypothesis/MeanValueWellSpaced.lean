/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.GaussianMeanValue

/-!
# The mean value theorem for exponential sums with well-spaced frequencies

`RiemannHypothesis/GaussianMeanValue.lean` proves the Montgomery–Vaughan *shape* of the mean
value theorem for the particular frequencies `log n` of a Dirichlet polynomial.  The estimate
that the density arguments and the discrete large sieve actually need is the same bound for an
*arbitrary* family of `δ`-separated real frequencies: this is the role played in the literature
by Montgomery and Vaughan's generalized Hilbert inequality.

For `λ_r` real with `|λ_r − λ_s| ≥ δ` whenever `r ≠ s`, and arbitrary complex `x_r`,

`∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ 18 (T + 1/δ) ∑_r ‖x_r‖²`.

The proof is the Gaussian majorant method, not the Hilbert inequality: on `[-T, T]` the
indicator is at most `e · exp (−t²/T²)`, the Gaussian weight turns the mean square into the
absolutely convergent bilinear form

`√π T ∑_{r, s} x_r x̄_s exp (−T² (λ_r − λ_s)²/4)`,

and the separation makes each row sum of that kernel at most `1 + 2√π/(δT)`: the frequencies
whose distance to `λ_r` lies in `[k δ, (k+1) δ)` number at most two, one on each side.

## Main results

* `RiemannHypothesis.WellSpaced.Separated` — the separation hypothesis.
* `RiemannHypothesis.WellSpaced.expSum` — the exponential sum `∑_r x_r e^{i λ_r t}`.
* `RiemannHypothesis.WellSpaced.card_fiber_le_two` — at most two frequencies in an annulus.
* `RiemannHypothesis.WellSpaced.rowSum_le` — the row sum bound
  `∑_s exp (−(λ_r − λ_s)²/(4b)) ≤ 1 + 2 √(π b)/δ`.
* `RiemannHypothesis.WellSpaced.integral_normSq_expSum_le` — **the mean value theorem**, in the
  explicit form `e (√π T + 2π/δ) ∑ ‖x_r‖²`.
* `RiemannHypothesis.WellSpaced.integral_normSq_expSum_le_mv` — the same with the round constant
  `18 (T + 1/δ)`, and `integral_Ioc_normSq_expSum_le_mv` over `[0, T]`.
* `RiemannHypothesis.WellSpaced.bilinear_le_of_rowSum_le` — Schur's test, the elementary
  ingredient that converts the row sum bound into the bound for the bilinear form.

## Scope

The constant is explicit but not optimal; Montgomery and Vaughan's theorem gives the main term
`T ∑ ‖x_r‖²` with the sharp constant `1`, and their generalized Hilbert inequality
`|∑_{r ≠ s} x_r x̄_s/(λ_r − λ_s)| ≤ π δ⁻¹ ∑ ‖x_r‖²` is *not* proved here.  Only the shape of the
bound — main term proportional to `T`, error proportional to `1/δ`, with no logarithm — is
claimed, and that is what the applications use.
-/

noncomputable section

open Complex MeasureTheory Finset

namespace RiemannHypothesis

namespace WellSpaced

variable {ι : Type*}

/-- The exponential sum `∑_{r ∈ S} x r e^{i (λ r) t}`. -/
def expSum (S : Finset ι) (lam : ι → ℝ) (x : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ r ∈ S, x r * Complex.exp ((t : ℂ) * (lam r : ℂ) * I)

/-- The frequencies `λ r`, `r ∈ S`, are `δ`-separated. -/
def Separated (S : Finset ι) (lam : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|

/-! ## Expanding the square -/

/-- The expansion of `‖∑_r x_r e^{i λ_r t}‖²` as a double sum of real parts. -/
theorem normSq_expSum_eq (S : Finset ι) (lam : ι → ℝ) (x : ι → ℂ) (t : ℝ) :
    ‖expSum S lam x t‖ ^ 2 = ∑ r ∈ S, ∑ s ∈ S,
      ((x r * (starRingEnd ℂ) (x s)) *
        Complex.exp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)).re := by
  have hnorm : ‖expSum S lam x t‖ ^ 2
      = (expSum S lam x t * (starRingEnd ℂ) (expSum S lam x t)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hnorm, expSum, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have hconj : (starRingEnd ℂ) (x s * Complex.exp ((t : ℂ) * (lam s : ℂ) * I))
      = (starRingEnd ℂ) (x s) * Complex.exp (-((t : ℂ) * (lam s : ℂ) * I)) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  have hsplit : Complex.exp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)
      = Complex.exp ((t : ℂ) * (lam r : ℂ) * I) * Complex.exp (-((t : ℂ) * (lam s : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hconj, hsplit]
  ring

/-! ## One Gaussian-weighted term -/

/-- The Gaussian-weighted oscillating term, as a real part. -/
theorem term_gaussian_re (K : ℂ) (θ b : ℝ) (t : ℝ) :
    (K * Complex.exp ((t : ℂ) * (θ : ℂ) * I)).re * Real.exp (-(b * t ^ 2))
      = (K * (Complex.exp ((t : ℂ) * (θ : ℂ) * I) *
          Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re := by
  have hre : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r := by intro z r; simp
  have hgauss : Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2) = ((Real.exp (-(b * t ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hgauss, ← mul_assoc, hre]

/-- Each Gaussian-weighted term is integrable. -/
theorem integrable_term_gaussian (K : ℂ) (θ : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ =>
      (K * Complex.exp ((t : ℂ) * (θ : ℂ) * I)).re * Real.exp (-(b * t ^ 2))) := by
  rw [funext (term_gaussian_re K θ b)]
  exact ((integrable_exp_mul_I_gaussian hb θ).const_mul K).re

/-- The Gaussian-weighted contribution of a single pair of frequencies. -/
theorem integral_term_gaussian_le (K : ℂ) (θ : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, (K * Complex.exp ((t : ℂ) * (θ : ℂ) * I)).re * Real.exp (-(b * t ^ 2)))
      ≤ Real.sqrt (Real.pi / b) * (‖K‖ * Real.exp (-θ ^ 2 / (4 * b))) := by
  rw [funext (term_gaussian_re K θ b)]
  have hint : Integrable (fun t : ℝ => K * (Complex.exp ((t : ℂ) * (θ : ℂ) * I) *
      Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))) := (integrable_exp_mul_I_gaussian hb θ).const_mul K
  rw [show (∫ t : ℝ, (K * (Complex.exp ((t : ℂ) * (θ : ℂ) * I) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re)
      = (∫ t : ℝ, K * (Complex.exp ((t : ℂ) * (θ : ℂ) * I) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2))).re by
    simpa using (Complex.reCLM.integral_comp_comm hint)]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_I_gaussian b θ hb]
  calc (K * ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ)).re
      ≤ ‖K * ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ)‖ :=
        Complex.re_le_norm _
    _ = ‖K‖ * (Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = _ := by ring

/-! ## The Gaussian-weighted mean square -/

/-- The Gaussian-weighted mean square is integrable. -/
theorem integrable_normSq_expSum_gaussian (S : Finset ι) (lam : ι → ℝ) (x : ι → ℂ) {b : ℝ}
    (hb : 0 < b) :
    Integrable (fun t : ℝ => ‖expSum S lam x t‖ ^ 2 * Real.exp (-(b * t ^ 2))) := by
  have hexp : ∀ t : ℝ, ‖expSum S lam x t‖ ^ 2 * Real.exp (-(b * t ^ 2))
      = ∑ r ∈ S, ∑ s ∈ S, ((x r * (starRingEnd ℂ) (x s)) *
          Complex.exp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)).re *
            Real.exp (-(b * t ^ 2)) := by
    intro t
    rw [normSq_expSum_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_mul _ _ _
  rw [funext hexp]
  exact MeasureTheory.integrable_finsetSum _ fun r _ =>
    MeasureTheory.integrable_finsetSum _ fun s _ =>
      integrable_term_gaussian (x r * (starRingEnd ℂ) (x s)) (lam r - lam s) hb

/-- The Gaussian-weighted mean square is at most `√(π/b)` times the bilinear form with kernel
`exp (−(λ_r − λ_s)²/(4b))`. -/
theorem integral_normSq_expSum_gaussian_le (S : Finset ι) (lam : ι → ℝ) (x : ι → ℂ) {b : ℝ}
    (hb : 0 < b) :
    (∫ t : ℝ, ‖expSum S lam x t‖ ^ 2 * Real.exp (-(b * t ^ 2)))
      ≤ Real.sqrt (Real.pi / b) * ∑ r ∈ S, ∑ s ∈ S,
          ‖x r‖ * ‖x s‖ * Real.exp (-(lam r - lam s) ^ 2 / (4 * b)) := by
  have hexp : ∀ t : ℝ, ‖expSum S lam x t‖ ^ 2 * Real.exp (-(b * t ^ 2))
      = ∑ r ∈ S, ∑ s ∈ S, ((x r * (starRingEnd ℂ) (x s)) *
          Complex.exp ((t : ℂ) * ((lam r - lam s : ℝ) : ℂ) * I)).re *
            Real.exp (-(b * t ^ 2)) := by
    intro t
    rw [normSq_expSum_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_mul _ _ _
  rw [funext hexp]
  rw [MeasureTheory.integral_finsetSum _ fun r _ =>
    MeasureTheory.integrable_finsetSum _ fun s _ =>
      integrable_term_gaussian (x r * (starRingEnd ℂ) (x s)) (lam r - lam s) hb]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun s _ =>
    integrable_term_gaussian (x r * (starRingEnd ℂ) (x s)) (lam r - lam s) hb, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  refine (integral_term_gaussian_le (x r * (starRingEnd ℂ) (x s)) (lam r - lam s) hb).trans ?_
  rw [norm_mul, RCLike.norm_conj]

/-! ## The row sums of the Gaussian kernel -/

/-- The frequencies at a given distance scale from a fixed one are at most two: one on each
side.  This is the only place the separation is used. -/
theorem card_fiber_le_two [DecidableEq ι] {S : Finset ι} {lam : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : Separated S lam δ) (r : ι) (k : ℕ) :
    ((S.erase r).filter (fun s => ⌊|lam r - lam s| / δ⌋₊ = k)).card ≤ 2 := by
  classical
  set F := (S.erase r).filter (fun s => ⌊|lam r - lam s| / δ⌋₊ = k) with hF
  have key : ∀ s ∈ F, (k : ℝ) * δ ≤ |lam r - lam s| ∧ |lam r - lam s| < ((k : ℝ) + 1) * δ := by
    intro s hs
    have hs' : ⌊|lam r - lam s| / δ⌋₊ = k := (Finset.mem_filter.mp hs).2
    have hnn : (0 : ℝ) ≤ |lam r - lam s| / δ := by positivity
    have h1 : (k : ℝ) ≤ |lam r - lam s| / δ := by
      rw [← hs']; exact Nat.floor_le hnn
    have h2 : |lam r - lam s| / δ < (k : ℝ) + 1 := by
      rw [← hs']; exact Nat.lt_floor_add_one _
    exact ⟨(le_div_iff₀ hδ).mp h1, (div_lt_iff₀ hδ).mp h2⟩
  have hmemS : ∀ s ∈ F, s ∈ S ∧ s ≠ r := by
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).1
    exact ⟨Finset.mem_of_mem_erase hs', Finset.ne_of_mem_erase hs'⟩
  have hpos : (F.filter (fun s => lam r < lam s)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun s hs s' hs' => ?_
    by_contra hne
    have hsF := Finset.mem_filter.mp hs
    have hs'F := Finset.mem_filter.mp hs'
    obtain ⟨h1, h2⟩ := key s hsF.1
    obtain ⟨h1', h2'⟩ := key s' hs'F.1
    rw [abs_of_nonpos (by linarith [hsF.2] : lam r - lam s ≤ 0)] at h1 h2
    rw [abs_of_nonpos (by linarith [hs'F.2] : lam r - lam s' ≤ 0)] at h1' h2'
    have hsp := hsep s (hmemS s hsF.1).1 s' (hmemS s' hs'F.1).1 hne
    rcases abs_cases (lam s - lam s') with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hsp <;> linarith
  have hneg : (F.filter (fun s => ¬ (lam r < lam s))).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun s hs s' hs' => ?_
    by_contra hne
    have hsF := Finset.mem_filter.mp hs
    have hs'F := Finset.mem_filter.mp hs'
    have hle : lam s ≤ lam r := not_lt.mp hsF.2
    have hle' : lam s' ≤ lam r := not_lt.mp hs'F.2
    obtain ⟨h1, h2⟩ := key s hsF.1
    obtain ⟨h1', h2'⟩ := key s' hs'F.1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam r - lam s)] at h1 h2
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam r - lam s')] at h1' h2'
    have hsp := hsep s (hmemS s hsF.1).1 s' (hmemS s' hs'F.1).1 hne
    rcases abs_cases (lam s - lam s') with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hsp <;> linarith
  have hcard := Finset.card_filter_add_card_filter_not (s := F)
    (p := fun s => lam r < lam s)
  omega

/-- **The row sum bound.**  For `δ`-separated frequencies the Gaussian kernel has row sums at
most `1 + 2 √(π b)/δ`. -/
theorem rowSum_le {S : Finset ι} {lam : ι → ℝ} {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hsep : Separated S lam δ) {r : ι} (hr : r ∈ S) :
    ∑ s ∈ S, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
      ≤ 1 + 2 * Real.sqrt (Real.pi * b) / δ := by
  classical
  set α : ℝ := δ ^ 2 / (4 * b) with hα
  have hαpos : 0 < α := by positivity
  -- split off the diagonal term
  have hsplit : ∑ s ∈ S, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
      = 1 + ∑ s ∈ S.erase r, Real.exp (-(lam r - lam s) ^ 2 / (4 * b)) := by
    rw [← Finset.add_sum_erase _ _ hr]
    simp
  rw [hsplit]
  have hmain : ∑ s ∈ S.erase r, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
      ≤ 2 * Real.sqrt (Real.pi * b) / δ := by
    set g : ι → ℕ := fun s => ⌊|lam r - lam s| / δ⌋₊ with hg
    -- every off-diagonal frequency has `g s ≥ 1`
    have hg1 : ∀ s ∈ S.erase r, 1 ≤ g s := by
      intro s hs
      have hsS : s ∈ S := Finset.mem_of_mem_erase hs
      have hne : s ≠ r := Finset.ne_of_mem_erase hs
      have := hsep r hr s hsS (Ne.symm hne)
      have h1 : (1 : ℝ) ≤ |lam r - lam s| / δ := (one_le_div hδ).mpr this
      exact_mod_cast Nat.le_floor (by exact_mod_cast h1 : ((1 : ℕ) : ℝ) ≤ |lam r - lam s| / δ)
    set K : ℕ := (S.erase r).sup g with hK
    have hgK : ∀ s ∈ S.erase r, g s ∈ Finset.Icc 1 K := by
      intro s hs
      exact Finset.mem_Icc.mpr ⟨hg1 s hs, Finset.le_sup hs⟩
    -- the kernel is dominated by the value at the rounded distance
    have hdom : ∀ s ∈ S.erase r, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
        ≤ Real.exp (-(α * (g s : ℝ) ^ 2)) := by
      intro s hs
      refine Real.exp_le_exp.mpr ?_
      have hnn : (0 : ℝ) ≤ |lam r - lam s| / δ := by positivity
      have hfl : (g s : ℝ) ≤ |lam r - lam s| / δ := Nat.floor_le hnn
      have hge : (g s : ℝ) * δ ≤ |lam r - lam s| := by
        rw [← le_div_iff₀ hδ]; exact hfl
      have hsq : ((g s : ℝ) * δ) ^ 2 ≤ (lam r - lam s) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (g s : ℝ) * δ := by positivity
        calc ((g s : ℝ) * δ) ^ 2 ≤ |lam r - lam s| ^ 2 := by nlinarith
          _ = (lam r - lam s) ^ 2 := sq_abs _
      have h4b : (0 : ℝ) < 4 * b := by linarith
      rw [hα, neg_div, neg_le_neg_iff, div_mul_eq_mul_div,
        div_le_div_iff_of_pos_right h4b]
      nlinarith
    calc ∑ s ∈ S.erase r, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
        ≤ ∑ s ∈ S.erase r, Real.exp (-(α * (g s : ℝ) ^ 2)) := Finset.sum_le_sum hdom
      _ = ∑ k ∈ Finset.Icc 1 K, ∑ s ∈ (S.erase r).filter (fun s => g s = k),
            Real.exp (-(α * (g s : ℝ) ^ 2)) :=
          (Finset.sum_fiberwise_of_maps_to hgK _).symm
      _ ≤ ∑ k ∈ Finset.Icc 1 K, 2 * Real.exp (-(α * (k : ℝ) ^ 2)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hcard := card_fiber_le_two (S := S) (lam := lam) hδ hsep r k
          have heq : ∀ s ∈ (S.erase r).filter (fun s => g s = k),
              Real.exp (-(α * (g s : ℝ) ^ 2)) = Real.exp (-(α * (k : ℝ) ^ 2)) := by
            intro s hs
            rw [(Finset.mem_filter.mp hs).2]
          rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
          have hle : (((S.erase r).filter (fun s => g s = k)).card : ℝ) ≤ 2 := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = 2 * ∑ k ∈ Finset.Icc 1 K, Real.exp (-(α * (k : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (Real.sqrt (Real.pi / α) / 2) := by
          have := sum_Icc_exp_neg_mul_sq_le hαpos K
          linarith
      _ = 2 * Real.sqrt (Real.pi * b) / δ := by
          have hrw : Real.pi / α = (2 * Real.sqrt (Real.pi * b) / δ) ^ 2 := by
            rw [hα]
            rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
            field_simp
            ring
          rw [hrw, Real.sqrt_sq (by positivity)]
          ring
  linarith

/-! ## Schur's test -/

/-- **Schur's test** for a symmetric nonnegative kernel: the bilinear form is bounded by the
diagonal weighted by the row sums. -/
theorem bilinear_le_of_rowSum_le {S : Finset ι} (c : ι → ℝ) (Kf : ι → ι → ℝ) (Δ : ℝ)
    (hsymm : ∀ r s, Kf r s = Kf s r) (hnn : ∀ r s, 0 ≤ Kf r s)
    (hrow : ∀ r ∈ S, ∑ s ∈ S, Kf r s ≤ Δ) :
    ∑ r ∈ S, ∑ s ∈ S, c r * c s * Kf r s ≤ Δ * ∑ r ∈ S, c r ^ 2 := by
  have hstep : ∑ r ∈ S, ∑ s ∈ S, c r * c s * Kf r s
      ≤ ∑ r ∈ S, ∑ s ∈ S, (c r ^ 2 * Kf r s + c s ^ 2 * Kf r s) / 2 := by
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => ?_
    nlinarith [sq_nonneg (c r - c s), hnn r s]
  have hsplit : ∑ r ∈ S, ∑ s ∈ S, (c r ^ 2 * Kf r s + c s ^ 2 * Kf r s) / 2
      = (∑ r ∈ S, ∑ s ∈ S, c r ^ 2 * Kf r s) / 2 + (∑ r ∈ S, ∑ s ∈ S, c s ^ 2 * Kf r s) / 2 := by
    have e1 : ∀ r, ∑ s ∈ S, (c r ^ 2 * Kf r s + c s ^ 2 * Kf r s) / 2
        = (∑ s ∈ S, c r ^ 2 * Kf r s) / 2 + (∑ s ∈ S, c s ^ 2 * Kf r s) / 2 := by
      intro r
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl (fun r _ => e1 r), Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
  have hrow' : ∑ r ∈ S, ∑ s ∈ S, c s ^ 2 * Kf r s = ∑ r ∈ S, ∑ s ∈ S, c r ^ 2 * Kf r s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by rw [hsymm]
  have hdiag : ∑ r ∈ S, ∑ s ∈ S, c r ^ 2 * Kf r s ≤ Δ * ∑ r ∈ S, c r ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [← Finset.mul_sum, mul_comm Δ (c r ^ 2)]
    exact mul_le_mul_of_nonneg_left (hrow r hr) (sq_nonneg (c r))
  rw [hsplit, hrow'] at hstep
  linarith

/-! ## The mean value theorem -/

/-- **The mean value theorem for well-spaced frequencies.**  For `δ`-separated real frequencies
and every `T > 0`,
`∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ e (√π T + 2π/δ) ∑_r ‖x_r‖²`. -/
theorem integral_normSq_expSum_le {S : Finset ι} {lam : ι → ℝ} (x : ι → ℂ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (hsep : Separated S lam δ) :
    (∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2)
      ≤ Real.exp 1 * (Real.sqrt Real.pi * T + 2 * Real.pi / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  classical
  have hb : (0 : ℝ) < 1 / T ^ 2 := by positivity
  have hFint : Integrable (fun t : ℝ =>
      ‖expSum S lam x t‖ ^ 2 * Real.exp (-(1 / T ^ 2 * t ^ 2))) :=
    integrable_normSq_expSum_gaussian S lam x hb
  have hcont : Continuous fun t : ℝ => ‖expSum S lam x t‖ ^ 2 := by
    refine (Continuous.norm ?_).pow 2
    refine continuous_finsetSum _ fun r _ => ?_
    exact continuous_const.mul ((Complex.continuous_exp.comp (by fun_prop)))
  have hFnn : ∀ t : ℝ, 0 ≤ ‖expSum S lam x t‖ ^ 2 * Real.exp (-(1 / T ^ 2 * t ^ 2)) := by
    intro t; positivity
  -- Step 1: the Gaussian majorant of the indicator of `[-T, T]`
  have step1 : (∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2)
      ≤ Real.exp 1 * ∫ t : ℝ, ‖expSum S lam x t‖ ^ 2 * Real.exp (-(1 / T ^ 2 * t ^ 2)) := by
    have hmono : (∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2)
        ≤ ∫ t in (-T)..T, Real.exp 1 * (‖expSum S lam x t‖ ^ 2 *
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
      have hnn : (0 : ℝ) ≤ ‖expSum S lam x t‖ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hnn]
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le)
    rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
    exact MeasureTheory.setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
  -- Step 2: the bilinear form
  have step2 := integral_normSq_expSum_gaussian_le S lam x hb
  -- Step 3: Schur's test with the row sum bound
  have hrow : ∀ r ∈ S, ∑ s ∈ S, Real.exp (-(lam r - lam s) ^ 2 / (4 * (1 / T ^ 2)))
      ≤ 1 + 2 * Real.sqrt (Real.pi * (1 / T ^ 2)) / δ := fun r hr =>
    rowSum_le hδ hb hsep hr
  have step3 : ∑ r ∈ S, ∑ s ∈ S,
      ‖x r‖ * ‖x s‖ * Real.exp (-(lam r - lam s) ^ 2 / (4 * (1 / T ^ 2)))
      ≤ (1 + 2 * Real.sqrt (Real.pi * (1 / T ^ 2)) / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 :=
    bilinear_le_of_rowSum_le (fun r => ‖x r‖)
      (fun r s => Real.exp (-(lam r - lam s) ^ 2 / (4 * (1 / T ^ 2)))) _
      (fun r s => by rw [show (lam r - lam s) ^ 2 = (lam s - lam r) ^ 2 by ring])
      (fun r s => (Real.exp_pos _).le) hrow
  -- Step 4: assemble
  have hsqrtb : Real.sqrt (Real.pi / (1 / T ^ 2)) = Real.sqrt Real.pi * T := by
    rw [show Real.pi / (1 / T ^ 2) = Real.pi * T ^ 2 by field_simp,
      Real.sqrt_mul Real.pi_nonneg, Real.sqrt_sq hT.le]
  have hsqrtb2 : Real.sqrt (Real.pi * (1 / T ^ 2)) = Real.sqrt Real.pi / T := by
    rw [show Real.pi * (1 / T ^ 2) = Real.pi / T ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hT.le]
  have hnnsum : (0 : ℝ) ≤ ∑ r ∈ S, ‖x r‖ ^ 2 := Finset.sum_nonneg fun r _ => by positivity
  have hfinal : Real.sqrt Real.pi * T * ((1 + 2 * (Real.sqrt Real.pi / T) / δ) *
      ∑ r ∈ S, ‖x r‖ ^ 2) ≤ (Real.sqrt Real.pi * T + 2 * Real.pi / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 := by
    have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
      Real.mul_self_sqrt Real.pi_nonneg
    have : Real.sqrt Real.pi * T * (1 + 2 * (Real.sqrt Real.pi / T) / δ)
        = Real.sqrt Real.pi * T + 2 * Real.pi / δ := by
      field_simp
      nlinarith [hpi]
    rw [← mul_assoc, this]
  rw [hsqrtb] at step2
  rw [hsqrtb2] at step3
  calc (∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2)
      ≤ Real.exp 1 * ∫ t : ℝ, ‖expSum S lam x t‖ ^ 2 * Real.exp (-(1 / T ^ 2 * t ^ 2)) := step1
    _ ≤ Real.exp 1 * (Real.sqrt Real.pi * T * ∑ r ∈ S, ∑ s ∈ S,
          ‖x r‖ * ‖x s‖ * Real.exp (-(lam r - lam s) ^ 2 / (4 * (1 / T ^ 2)))) :=
        mul_le_mul_of_nonneg_left step2 (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (Real.sqrt Real.pi * T *
          ((1 + 2 * (Real.sqrt Real.pi / T) / δ) * ∑ r ∈ S, ‖x r‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step3 (by positivity))
          (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * ((Real.sqrt Real.pi * T + 2 * Real.pi / δ) * ∑ r ∈ S, ‖x r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hfinal (Real.exp_pos 1).le
    _ = Real.exp 1 * (Real.sqrt Real.pi * T + 2 * Real.pi / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 := by ring

/-- **The mean value theorem for well-spaced frequencies**, with a round constant:
`∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ 18 (T + 1/δ) ∑_r ‖x_r‖²`. -/
theorem integral_normSq_expSum_le_mv {S : Finset ι} {lam : ι → ℝ} (x : ι → ℂ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (hsep : Separated S lam δ) :
    (∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2) ≤ 18 * (T + 1 / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  refine (integral_normSq_expSum_le x hδ hT hsep).trans ?_
  have hnnsum : (0 : ℝ) ≤ ∑ r ∈ S, ‖x r‖ ^ 2 := Finset.sum_nonneg fun r _ => by positivity
  refine mul_le_mul_of_nonneg_right ?_ hnnsum
  have he : Real.exp 1 ≤ 2.7183 := le_of_lt (by linarith [Real.exp_one_lt_d9])
  have hsq : Real.sqrt Real.pi ≤ 1.7725 := by
    rw [show (1.7725 : ℝ) = Real.sqrt (1.7725 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d6])
  have hpi : Real.pi ≤ 3.1416 := by linarith [Real.pi_lt_d6]
  have h1 : (0 : ℝ) < 1 / δ := by positivity
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsqnn : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hd : 2 * Real.pi / δ = (2 * Real.pi) * (1 / δ) := by ring
  rw [hd]
  have hA : Real.exp 1 * (Real.sqrt Real.pi * T) ≤ 18 * T := by
    nlinarith [exp_one_mul_sqrt_pi_le, hT.le]
  have hep : Real.exp 1 * Real.pi ≤ 8.54 := by
    have := mul_le_mul he hpi Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 2.7183)
    linarith
  have hB : Real.exp 1 * (2 * Real.pi * (1 / δ)) ≤ 18 * (1 / δ) := by
    nlinarith [hep, h1.le]
  nlinarith [hA, hB]

/-- The same over `[0, T]`. -/
theorem integral_Ioc_normSq_expSum_le_mv {S : Finset ι} {lam : ι → ℝ} (x : ι → ℂ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (hsep : Separated S lam δ) :
    (∫ t in (0 : ℝ)..T, ‖expSum S lam x t‖ ^ 2) ≤ 18 * (T + 1 / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  have hcont : Continuous fun t : ℝ => ‖expSum S lam x t‖ ^ 2 := by
    refine (Continuous.norm ?_).pow 2
    refine continuous_finsetSum _ fun r _ => ?_
    exact continuous_const.mul ((Complex.continuous_exp.comp (by fun_prop)))
  have hadd : (∫ t in (-T)..(0 : ℝ), ‖expSum S lam x t‖ ^ 2)
      + (∫ t in (0 : ℝ)..T, ‖expSum S lam x t‖ ^ 2)
      = ∫ t in (-T)..T, ‖expSum S lam x t‖ ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hnn : (0 : ℝ) ≤ ∫ t in (-T)..(0 : ℝ), ‖expSum S lam x t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ 0)]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
  have := integral_normSq_expSum_le_mv x hδ hT hsep
  linarith

end WellSpaced

end RiemannHypothesis
