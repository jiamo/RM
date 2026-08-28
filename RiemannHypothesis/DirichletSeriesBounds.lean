/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Real Dirichlet-series bounds for `ζ` and for `-ζ'/ζ`

This file collects the elementary, *sharp* bounds on the right of the line `re s = 1` that the
classical de la Vallée Poussin zero-free region needs.  Everything here is proved from the
Dirichlet series; nothing is assumed.

## Main results

* `zetaSeries_le` : `ζ(σ) ≤ 1/(σ-1) + 1` for real `σ > 1`;
* `le_zetaSeries` : `1/(σ-1) ≤ ζ(σ)` for real `σ > 1`;
* `negReLogDerivZeta_real_le` : `-ζ'/ζ(σ) ≤ 1/(σ-1-a) + (σ-1)/a` for `0 < a < σ - 1`.
  Letting `a` tend to `0` slowly this is the sharp bound `-ζ'/ζ(σ) ≤ (1 + o(1))/(σ-1)`, and the
  constant `1` in front of `1/(σ-1)` is what makes the `3-4-1` argument work (it needs a constant
  smaller than `4/3`);
* `three_four_one` : `0 ≤ 3·(-ζ'/ζ)(σ) + 4·Re(-ζ'/ζ)(σ+it) + Re(-ζ'/ζ)(σ+2it)` for `σ > 1`,
  the logarithmic-derivative form of Mertens' `3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`.
-/

noncomputable section

open Complex ArithmeticFunction Filter
open scoped LSeries.notation

namespace RiemannHypothesis

/-! ## Summability -/

/-- `log x ≤ (x^a - 1)/a` for `x > 0` and `a > 0`: the elementary comparison behind both the
summability of `∑ log n · n^{-σ}` and the sharp bound `logSeries_le`. -/
lemma log_le_rpow_sub_one_div {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ (x ^ a - 1) / a := by
  have h := Real.add_one_le_exp (a * Real.log x)
  have hx' : Real.exp (a * Real.log x) = x ^ a := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [hx'] at h
  rw [le_div_iff₀ ha]
  nlinarith

lemma summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  simpa [Real.rpow_neg, ← one_div] using (Real.summable_one_div_nat_rpow (p := σ)).2 hσ

lemma summable_log_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-σ)) := by
  set a : ℝ := (σ - 1) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hsum : Summable (fun n : ℕ => (1 / a) * (n : ℝ) ^ (-(σ - a))) :=
    (summable_rpow_neg (by rw [ha_def]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : 0 ≤ Real.log n := Real.log_nonneg this
      positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [CharP.cast_eq_zero, Real.log_zero, zero_mul, one_div, neg_sub]
      positivity
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hlog : Real.log n ≤ (1 / a) * (n : ℝ) ^ a := by
        have := log_le_rpow_sub_one_div hn0 ha
        have hpos : (0 : ℝ) ≤ (n : ℝ) ^ a := Real.rpow_nonneg hn0.le _
        have hainv : 0 < a⁻¹ := inv_pos.2 ha
        rw [div_eq_inv_mul] at this
        rw [one_div]
        nlinarith [this, hainv, hpos]
      have hrpow : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
      calc Real.log n * (n : ℝ) ^ (-σ) ≤ ((1 / a) * (n : ℝ) ^ a) * (n : ℝ) ^ (-σ) := by
            exact mul_le_mul_of_nonneg_right hlog hrpow.le
        _ = (1 / a) * (n : ℝ) ^ (-(σ - a)) := by
            rw [mul_assoc, ← Real.rpow_add hn0]
            ring_nf

lemma summable_vonMangoldt_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_log_mul_rpow_neg hσ)
  · exact mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact mul_le_mul_of_nonneg_right (vonMangoldt_le_log)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_vonMangoldt_rpow_neg_cos {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
  refine (summable_vonMangoldt_rpow_neg hσ).of_norm_bounded (fun n => ?_)
  have h0 : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  calc Λ n * (n : ℝ) ^ (-σ) * |Real.cos (t * Real.log n)|
      ≤ Λ n * (n : ℝ) ^ (-σ) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h0
    _ = Λ n * (n : ℝ) ^ (-σ) := mul_one _

/-! ## The zeta series on the real axis -/

/-- The Riemann zeta function at a real point `σ > 1` is the real Dirichlet series. -/
lemma riemannZeta_ofReal_eq {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = ((∑' n : ℕ, (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have h1 : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  rw [← LSeries_one_eq_riemannZeta h1, LSeries, Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp [LSeries.term_of_ne_zero (show n ≠ 0 by omega), Real.rpow_neg hn0.le,
      Complex.ofReal_cpow hn0.le]

private lemma antitoneOn_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (1 : ℝ)) := by
  intro x hx y _ hxy
  exact Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.1 hx]) hxy (by linarith)

private lemma integral_Ioi_one_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    ∫ x in Set.Ioi (1 : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num), Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring]
  field_simp

private lemma integrableOn_Ioi_one_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi (1 : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)

private lemma nonneg_rpow_neg (σ : ℝ) : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ t ^ (-σ) :=
  fun t ht => Real.rpow_nonneg (by linarith [Set.mem_Ioi.1 ht]) _

/-- Sum-integral comparison, upper form: for an antitone nonnegative integrable `f` on `[1, ∞)`,
the tail sum `∑ f(n + 2)` is at most `∫_1^∞ f`.  (The corresponding Mathlib lemma for infinite
sums is not available in the version this repository is built against.) -/
private lemma tsum_add_two_le_integral_Ioi_one {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Set.Ici (1 : ℝ)))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)))
    (hpos : ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ f x)
    (hsum : Summable fun n : ℕ => f ((n : ℝ) + 2)) :
    ∑' n : ℕ, f ((n : ℝ) + 2) ≤ ∫ x in Set.Ioi (1 : ℝ), f x := by
  refine hsum.tsum_le_of_sum_range_le fun N => ?_
  have hanti' : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ)) := by
    refine hanti.mono ?_
    simpa using (Set.Icc_subset_Ici_self : Set.Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) ⊆ _)
  have h1 := AntitoneOn.sum_le_integral_Ico (a := 1) (b := N + 1) (by omega) hanti'
  have h2 : (∑ i ∈ Finset.Ico 1 (N + 1), f ((i + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.range N, f ((i : ℝ) + 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) fun i _ => ?_
    push_cast
    ring_nf
  rw [h2] at h1
  refine h1.trans ?_
  rw [intervalIntegral.integral_of_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N])]
  refine MeasureTheory.setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall fun x hx => ?_)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx using
      hpos x (le_of_lt (Set.mem_Ioi.1 hx))
  · exact Set.mem_Ioi.mpr (by exact_mod_cast hx.1)

/-- Sum-integral comparison, lower form: for an antitone nonnegative integrable `f` on `[1, ∞)`,
`∫_1^∞ f` is at most the sum `∑ f(n + 1)`. -/
private lemma integral_Ioi_one_le_tsum_add_one {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Set.Ici (1 : ℝ)))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)))
    (hpos : ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ f x)
    (hsum : Summable fun n : ℕ => f ((n : ℝ) + 1)) :
    (∫ x in Set.Ioi (1 : ℝ), f x) ≤ ∑' n : ℕ, f ((n : ℝ) + 1) := by
  have htend : Filter.Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), f x) Filter.atTop
      (nhds (∫ x in Set.Ioi (1 : ℝ), f x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop
  refine le_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hanti' : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    refine hanti.mono ?_
    simpa using (Set.Icc_subset_Ici_self : Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ) ⊆ _)
  have h1 := AntitoneOn.integral_le_sum_Ico (a := 1) (b := N) hN hanti'
  have h2 : (∑ i ∈ Finset.Ico 1 N, f ((i : ℕ) : ℝ))
      = ∑ i ∈ Finset.range (N - 1), f ((i : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  rw [h2] at h1
  refine le_trans (by simpa using h1) ?_
  exact hsum.sum_le_tsum _ fun i _ => hpos _ (by simp [Set.Ici])

private lemma nonneg_rpow_neg_Ici (σ : ℝ) : ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ x ^ (-σ) :=
  fun x hx => Real.rpow_nonneg (by linarith [Set.mem_Ici.1 hx]) _

/-- `ζ(σ) ≤ 1/(σ - 1) + 1`. -/
lemma zetaSeries_le {σ : ℝ} (hσ : 1 < σ) : (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 / (σ - 1) + 1 := by
  have hsum := summable_rpow_neg hσ
  have hsum2 : Summable fun n : ℕ => ((n : ℝ) + 2) ^ (-σ) := by
    have h := (summable_nat_add_iff 2).2 hsum
    refine h.congr fun n => ?_
    push_cast
    ring_nf
  have hkey := tsum_add_two_le_integral_Ioi_one (f := fun x : ℝ => x ^ (-σ))
    (antitoneOn_rpow_neg hσ) (integrableOn_Ioi_one_rpow_neg hσ) (nonneg_rpow_neg_Ici σ) hsum2
  rw [integral_Ioi_one_rpow_neg hσ] at hkey
  have hA : (1 : ℝ) + ∑' n : ℕ, ((n : ℝ) + 2) ^ (-σ) = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
    have h := hsum.sum_add_tsum_nat_add 2
    rw [show (∑ i ∈ Finset.range 2, (i : ℝ) ^ (-σ)) = 1 by
      simp [Finset.sum_range_succ, Real.zero_rpow (by linarith : -σ ≠ 0)]] at h
    rw [← h]
    congr 1
    exact tsum_congr fun n => by push_cast; ring_nf
  rw [← hA]
  linarith

/-- `1/(σ - 1) ≤ ζ(σ)`. -/
lemma le_zetaSeries {σ : ℝ} (hσ : 1 < σ) : 1 / (σ - 1) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  have hsum := summable_rpow_neg hσ
  have hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) := by
    have h := (summable_nat_add_iff 1).2 hsum
    refine h.congr fun n => ?_
    push_cast
    ring_nf
  have hkey := integral_Ioi_one_le_tsum_add_one (f := fun x : ℝ => x ^ (-σ))
    (antitoneOn_rpow_neg hσ) (integrableOn_Ioi_one_rpow_neg hσ) (nonneg_rpow_neg_Ici σ) hsum1
  rw [integral_Ioi_one_rpow_neg hσ] at hkey
  have hA : (0 : ℝ) + ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
    have h := hsum.sum_add_tsum_nat_add 1
    rw [show (∑ i ∈ Finset.range 1, (i : ℝ) ^ (-σ)) = 0 by
      simp [Real.zero_rpow (by linarith : -σ ≠ 0)]] at h
    rw [← h]
    congr 1
    exact tsum_congr fun n => by push_cast; ring_nf
  rw [← hA]
  linarith

lemma zetaSeries_pos {σ : ℝ} (hσ : 1 < σ) : 0 < ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
  lt_of_lt_of_le (div_pos one_pos (by linarith)) (le_zetaSeries hσ)

/-! ## The von Mangoldt series -/

/-- `-Re ζ'/ζ(s)`, the quantity the zero-free region argument estimates. -/
def negReLogDerivZeta (s : ℂ) : ℝ := (-(deriv riemannZeta s / riemannZeta s)).re

/-- The real part of `x^{-s}` for real `x > 0`. -/
private lemma re_ofReal_cpow_neg {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (((x : ℝ) : ℂ) ^ (-s)).re = x ^ (-s.re) * Real.cos (s.im * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    Complex.exp_re]
  simp [Real.rpow_def_of_pos hx]
  ring_nf

/-- For `re s > 1`, `-Re ζ'/ζ(s) = ∑ Λ(n) n^{-σ} cos(t log n)`. -/
lemma negReLogDerivZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    negReLogDerivZeta s
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hL : LSeries ↗Λ s = -(deriv riemannZeta s / riemannZeta s) := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div]
  have hsum : Summable (LSeries.term ↗Λ s) := LSeriesSummable_vonMangoldt hs
  have hterm : ∀ n : ℕ, (LSeries.term ↗Λ s n).re
      = Λ n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero (show n ≠ 0 by omega)]
      have hcpow : ((n : ℂ) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
        have h := re_ofReal_cpow_neg hn0 s
        rwa [Complex.ofReal_natCast] at h
      have hdiv : (↗Λ) n / (n : ℂ) ^ s = ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
        rw [Complex.cpow_neg, div_eq_mul_inv]
      rw [hdiv, Complex.re_ofReal_mul, hcpow]
      ring
  rw [negReLogDerivZeta, ← hL, LSeries, Complex.re_tsum hsum]
  exact tsum_congr hterm

/-- A real Dirichlet series, read as an `LSeries`. -/
private lemma LSeries_ofReal_eq (f : ℕ → ℝ) {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => ((f n : ℝ) : ℂ)) (σ : ℂ)
      = ((∑' n : ℕ, f n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp [LSeries.term_of_ne_zero (show n ≠ 0 by omega), Real.rpow_neg hn0.le,
      Complex.ofReal_cpow hn0.le, div_eq_mul_inv]

/-- On the real axis the von Mangoldt series is the ratio of the two positive series. -/
lemma negReLogDerivZeta_real_eq {σ : ℝ} (hσ : 1 < σ) :
    negReLogDerivZeta (σ : ℂ)
      = (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ)) / (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
  have hs : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have habs : LSeries.abscissaOfAbsConv 1 < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hlog : (LSeries.logMul 1 : ℕ → ℂ) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.logMul]
    · simp [LSeries.logMul]
  have hderiv :
      deriv (LSeries 1) (σ : ℂ) = -((∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [LSeries_deriv habs, hlog, LSeries_ofReal_eq _ hσ]
  have hzeta : riemannZeta (σ : ℂ) = ((∑' n : ℕ, (n : ℝ) ^ (-σ) : ℝ) : ℂ) :=
    riemannZeta_ofReal_eq hσ
  have hderiv' :
      deriv riemannZeta (σ : ℂ) = -((∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← hderiv]
    refine Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_iff_exists_mem.mpr ?_)
    exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
      fun _ hz => (LSeries_one_eq_riemannZeta hz).symm⟩
  rw [negReLogDerivZeta, hderiv', hzeta, neg_div, neg_neg, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- The elementary comparison `log n ≤ (n^a - 1)/a`, summed: `-ζ'(σ) ≤ (ζ(σ-a) - ζ(σ))/a`. -/
lemma logSeries_le {σ a : ℝ} (ha : 0 < a) (hσ : 1 + a < σ) :
    (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ))
      ≤ ((∑' n : ℕ, (n : ℝ) ^ (-(σ - a))) - ∑' n : ℕ, (n : ℝ) ^ (-σ)) / a := by
  have hσ1 : 1 < σ := by linarith
  have hσa : 1 < σ - a := by linarith
  have hS1 := summable_rpow_neg hσa
  have hS2 := summable_rpow_neg hσ1
  have hrhs : ((∑' n : ℕ, (n : ℝ) ^ (-(σ - a))) - ∑' n : ℕ, (n : ℝ) ^ (-σ)) / a
      = ∑' n : ℕ, ((n : ℝ) ^ (-(σ - a)) - (n : ℝ) ^ (-σ)) / a := by
    rw [← hS1.tsum_sub hS2, ← tsum_div_const]
  rw [hrhs]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_log_mul_rpow_neg hσ1)
    ((hS1.sub hS2).div_const a)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : -σ ≠ 0), Real.zero_rpow (by linarith : a - σ ≠ 0)]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog := log_le_rpow_sub_one_div hn0 ha
    have hpow : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
    have hmul : ((n : ℝ) ^ a - 1) / a * (n : ℝ) ^ (-σ)
        = ((n : ℝ) ^ (-(σ - a)) - (n : ℝ) ^ (-σ)) / a := by
      rw [show -(σ - a) = a + -σ by ring, Real.rpow_add hn0]
      field_simp
    calc Real.log n * (n : ℝ) ^ (-σ) ≤ ((n : ℝ) ^ a - 1) / a * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlog hpow.le
      _ = ((n : ℝ) ^ (-(σ - a)) - (n : ℝ) ^ (-σ)) / a := hmul

/-- **The sharp bound on the real axis.**  For `0 < a < σ - 1`,
`-ζ'/ζ(σ) ≤ 1/(σ - 1 - a) + (σ - 1)/a`.  With `a` a small multiple of `σ - 1` the leading
constant is as close to `1` as we please. -/
lemma negReLogDerivZeta_real_le {σ a : ℝ} (ha : 0 < a) (hσ : 1 + a < σ) :
    negReLogDerivZeta (σ : ℂ) ≤ 1 / (σ - 1 - a) + (σ - 1) / a := by
  have hσ1 : 1 < σ := by linarith
  have hu : 0 < σ - 1 := by linarith
  have hua : 0 < σ - 1 - a := by linarith
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-σ) with hZdef
  set Za := ∑' n : ℕ, (n : ℝ) ^ (-(σ - a)) with hZadef
  set S := ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ) with hSdef
  have hZpos : 0 < Z := zetaSeries_pos hσ1
  have hZge : 1 / (σ - 1) ≤ Z := le_zetaSeries hσ1
  have hZu : 1 ≤ Z * (σ - 1) := by
    rw [div_le_iff₀ hu] at hZge
    linarith
  have hZale : Za ≤ 1 / (σ - a - 1) + 1 := zetaSeries_le (by linarith)
  have hSle : S ≤ (Za - Z) / a := logSeries_le ha hσ
  have hW : 1 / (σ - 1 - a) * (σ - 1 - a) = 1 := by field_simp
  have hZale' : Za ≤ 1 / (σ - 1 - a) + 1 := by
    rw [show σ - a - 1 = σ - 1 - a by ring] at hZale
    exact hZale
  rw [negReLogDerivZeta_real_eq hσ1, ← hSdef, ← hZdef, div_le_iff₀ hZpos]
  have hkey : (Za - Z) / a ≤ (1 / (σ - 1 - a) + (σ - 1) / a) * Z := by
    rw [div_le_iff₀ ha]
    have hexp : (1 / (σ - 1 - a) + (σ - 1) / a) * Z * a
        = 1 / (σ - 1 - a) * Z * a + (σ - 1) * Z := by
      field_simp
    rw [hexp]
    nlinarith [mul_pos hZpos hua, hW, hZu, hZale']
  linarith

/-! ## The 3-4-1 inequality -/

/-- **Mertens' `3-4-1` inequality**, in logarithmic-derivative form. -/
theorem three_four_one {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * negReLogDerivZeta (σ : ℂ) + 4 * negReLogDerivZeta ((σ : ℂ) + (t : ℂ) * I)
      + negReLogDerivZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
  have hre : ∀ u : ℝ, ((σ : ℂ) + (u : ℂ) * I).re = σ := by intro u; simp
  have him : ∀ u : ℝ, ((σ : ℂ) + (u : ℂ) * I).im = u := by intro u; simp
  set a : ℕ → ℝ := fun n => Λ n * (n : ℝ) ^ (-σ) * Real.cos (0 * Real.log n) with ha
  set b : ℕ → ℝ := fun n => Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) with hb
  set c : ℕ → ℝ := fun n => Λ n * (n : ℝ) ^ (-σ) * Real.cos (2 * t * Real.log n) with hc
  have hs0 : Summable a := summable_vonMangoldt_rpow_neg_cos hσ 0
  have hs1 : Summable b := summable_vonMangoldt_rpow_neg_cos hσ t
  have hs2 : Summable c := summable_vonMangoldt_rpow_neg_cos hσ (2 * t)
  have h0 : negReLogDerivZeta (σ : ℂ) = ∑' n : ℕ, a n := by
    rw [negReLogDerivZeta_eq_tsum (by simpa using hσ)]
    simp [ha]
  have h1 : negReLogDerivZeta ((σ : ℂ) + (t : ℂ) * I) = ∑' n : ℕ, b n := by
    rw [negReLogDerivZeta_eq_tsum (by rw [hre]; exact hσ), hre, him]
  have h2 : negReLogDerivZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = ∑' n : ℕ, c n := by
    rw [negReLogDerivZeta_eq_tsum (by rw [hre]; exact hσ), hre, him]
  have key : (∑' n : ℕ, (3 * a n + 4 * b n + c n))
      = 3 * (∑' n : ℕ, a n) + 4 * (∑' n : ℕ, b n) + ∑' n : ℕ, c n := by
    rw [Summable.tsum_add ((hs0.mul_left 3).add (hs1.mul_left 4)) hs2,
      Summable.tsum_add (hs0.mul_left 3) (hs1.mul_left 4), tsum_mul_left, tsum_mul_left]
  rw [h0, h1, h2, ← key]
  refine tsum_nonneg (fun n => ?_)
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcos : Real.cos (2 * t * Real.log n) = 2 * Real.cos (t * Real.log n) ^ 2 - 1 := by
    rw [mul_assoc, Real.cos_two_mul]
  simp only [ha, hb, hc, hcos, zero_mul, Real.cos_zero, mul_one]
  nlinarith [mul_nonneg (mul_nonneg hΛ hp) (sq_nonneg (1 + Real.cos (t * Real.log n)))]

end RiemannHypothesis
