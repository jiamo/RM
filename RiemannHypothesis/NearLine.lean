/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Continuation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A logarithmic bound for `ζ` just to the *left* of the line `re s = 1`

`RiemannHypothesis.EulerMaclaurin` proves `‖ζ(s)‖ ≤ 6 + log(1 + |t|)` on the strip
`1 ≤ re s ≤ 2`.  Now that the Euler–Maclaurin representation is available on the whole
punctured right half-plane (`RiemannHypothesis.Continuation`), the same computation gives a
logarithmic bound slightly to the *left* of the line `re s = 1`, on the region

`1 - 1/(2 log|t|) ≤ re s ≤ 2`,  `|t| ≥ 3`,

which is the region the classical zero-free-region argument needs.  (The bound is genuinely
restricted to a neighbourhood of the line of width `≍ 1/log|t|`: further to the left the
first-order Euler–Maclaurin representation only gives `O(|t|^{1-σ})`.)

## Main results

* `tsum_shift_rpow_neg_le_rpow` : the tail bound `∑' n, (n + N + 1)^(-p) ≤ N^(1-p)/(p-1)`
  for `1 < p` and `1 ≤ N`, by comparison with the integral;
* `norm_riemannZeta_le_log_near_line` : `‖ζ(s)‖ ≤ 18 log|t|` on the region above.
-/

noncomputable section

open Complex Filter Finset

namespace RiemannHypothesis

/-! ## Elementary estimates -/

/-- `1 ≤ log t` for `3 ≤ t`. -/
lemma one_le_log_of_three_le {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have he : Real.exp 1 ≤ 3 := by nlinarith [Real.exp_one_lt_d9]
  have h := Real.log_le_log (by positivity) ht
  have h1 : Real.log (Real.exp 1) ≤ Real.log t :=
    Real.log_le_log (Real.exp_pos 1) (le_trans he ht)
  rwa [Real.log_exp] at h1

/-- `log (t + 2) ≤ 2 log t` for `3 ≤ t`. -/
lemma log_add_two_le_two_log {t : ℝ} (ht : 3 ≤ t) : Real.log (t + 2) ≤ 2 * Real.log t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsq : t + 2 ≤ t ^ 2 := by nlinarith
  calc Real.log (t + 2) ≤ Real.log (t ^ 2) := Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log t := by
        rw [Real.log_pow]
        norm_num

/-- If `log x ≤ 2 L`, `1 ≤ L` and `1 - 1/(2L) ≤ σ ≤ 1`, then `x ^ (1 - σ) ≤ 3`. -/
lemma rpow_one_sub_le_three {x L sigma : ℝ} (hx : 1 ≤ x) (hlog : Real.log x ≤ 2 * L)
    (hL : 1 ≤ L) (hσ : 1 - 1 / (2 * L) ≤ sigma) (hσ1 : sigma ≤ 1) : x ^ (1 - sigma) ≤ 3 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL0 : (0 : ℝ) < 2 * L := by linarith
  have hsub : 1 - sigma ≤ 1 / (2 * L) := by linarith
  have hsub0 : 0 ≤ 1 - sigma := by linarith
  have hprod : Real.log x * (1 - sigma) ≤ 1 := by
    have h1 : Real.log x * (1 - sigma) ≤ (2 * L) * (1 / (2 * L)) := by
      apply mul_le_mul hlog hsub hsub0 (by linarith)
    rwa [mul_one_div, div_self hL0.ne'] at h1
  calc x ^ (1 - sigma) = Real.exp (Real.log x * (1 - sigma)) := Real.rpow_def_of_pos hx0 _
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hprod
    _ ≤ 3 := by nlinarith [Real.exp_one_lt_d9]

/-! ## The `p`-series tail, by comparison with the integral -/

/-- The tail bound `∑' n, (n + N + 1)^(-p) ≤ N^(1-p)/(p-1)` for `1 < p` and `1 ≤ N`. -/
lemma tsum_shift_rpow_neg_le_rpow {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-p) ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc (N : ℝ) ((N : ℝ) + (M : ℕ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have h0 : (0 : ℝ) ∉ Set.uIcc (N : ℝ) ((N : ℝ) + (M : ℕ)) := by
    have hle : (N : ℝ) ≤ (N : ℝ) + (M : ℕ) := le_add_of_nonneg_right (Nat.cast_nonneg M)
    rw [Set.uIcc_of_le hle]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hint : ∫ x in (N : ℝ)..((N : ℝ) + (M : ℕ)), x ^ (-p)
      = (((N : ℝ) + (M : ℕ)) ^ (-p + 1) - (N : ℝ) ^ (-p + 1)) / (-p + 1) := by
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hintle : (∫ x in (N : ℝ)..((N : ℝ) + (M : ℕ)), x ^ (-p)) ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
    rw [hint]
    have hpos : 0 ≤ ((N : ℝ) + (M : ℕ)) ^ (-p + 1) := Real.rpow_nonneg (by positivity) _
    have hrw : (((N : ℝ) + (M : ℕ)) ^ (-p + 1) - (N : ℝ) ^ (-p + 1)) / (-p + 1)
        = ((N : ℝ) ^ (1 - p) - ((N : ℝ) + (M : ℕ)) ^ (-p + 1)) / (p - 1) := by
      rw [show (-p + 1) = -(p - 1) by ring, div_neg, show (1 - p) = -(p - 1) by ring]
      ring
    rw [hrw]
    exact (div_le_div_iff_of_pos_right hp1).mpr (by linarith)
  refine le_trans ?_ hintle
  refine le_trans (le_of_eq ?_) hsum
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  ring

/-! ## The bound -/

/-- **A logarithmic bound for `ζ` in a neighbourhood of the line `re s = 1`.**
For `|t| ≥ 3` and `1 - 1/(2 log|t|) ≤ re s ≤ 2`, `‖ζ(s)‖ ≤ 18 log|t|`. -/
theorem norm_riemannZeta_le_log_near_line {s : ℂ} (ht : 3 ≤ |s.im|)
    (h1 : 1 - 1 / (2 * Real.log |s.im|) ≤ s.re) (h2 : s.re ≤ 2) :
    ‖riemannZeta s‖ ≤ 18 * Real.log |s.im| := by
  set t : ℝ := |s.im| with htdef
  set L : ℝ := Real.log t with hLdef
  have hL1 : 1 ≤ L := one_le_log_of_three_le ht
  have hlog12 : Real.log (t + 1) ≤ 2 * L :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) (log_add_two_le_two_log ht)
  have hlog2 : Real.log (t + 2) ≤ 2 * L := log_add_two_le_two_log ht
  rcases le_or_gt 1 s.re with hge | hlt
  · -- to the right of the line: the bound already proved in `EulerMaclaurin`
    have h := norm_riemannZeta_le_log hge h2 (by linarith)
    have hlog : Real.log (1 + t) ≤ 2 * L := by rw [add_comm]; exact hlog12
    linarith
  · -- to the left of the line: the Euler–Maclaurin computation, now valid there
    have hσ1 : s.re < 1 := hlt
    have hσhalf : (1 : ℝ) / 2 ≤ s.re := by
      have : 1 / (2 * L) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le <;> linarith
      linarith
    have hσ0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hσ1 h1
      simp at hσ1
    set N : ℕ := ⌈t⌉₊ with hNdef
    have hNle : t ≤ (N : ℝ) := Nat.le_ceil t
    have hNlt : (N : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    have hNnat : 1 ≤ N := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    rw [riemannZeta_eq_zetaApprox_of_pos_re N hσ0 hs1]
    unfold zetaApprox
    -- the truncated Dirichlet sum
    have hNbound : (N : ℝ) ^ (1 - s.re) ≤ 3 := by
      refine rpow_one_sub_le_three hN1 ?_ hL1 h1 hσ1.le
      exact le_trans (Real.log_le_log hNpos hNlt.le) hlog12
    have hA : ‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ 3 + 6 * L := by
      have hterm : ∀ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re)
          ≤ (N : ℝ) ^ (1 - s.re) * ((n : ℝ) + 1) ^ (-(1 : ℝ)) := by
        intro n hn
        have hnN : ((n : ℝ) + 1) ≤ (N : ℝ) := by
          have := Finset.mem_range.mp hn
          have : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
          exact this
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hsplit : ((n : ℝ) + 1) ^ (-s.re)
            = ((n : ℝ) + 1) ^ (1 - s.re) * ((n : ℝ) + 1) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hn1]
          ring_nf
        rw [hsplit]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn1.le _)
        exact Real.rpow_le_rpow hn1.le hnN (by linarith)
      calc ‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
          ≤ ∑ n ∈ Finset.range N, ‖((n + 1 : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
            simp
        _ ≤ ∑ n ∈ Finset.range N, (N : ℝ) ^ (1 - s.re) * ((n : ℝ) + 1) ^ (-(1 : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = (N : ℝ) ^ (1 - s.re) * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(1 : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ 3 * (1 + Real.log (N : ℝ)) := by
            refine mul_le_mul hNbound
              (sum_range_natAddOne_rpow_neg_le_one_add_log (le_refl 1) N) ?_ (by norm_num)
            exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
        _ ≤ 3 + 6 * L := by
            have : Real.log (N : ℝ) ≤ 2 * L :=
              le_trans (Real.log_le_log hNpos hNlt.le) hlog12
            linarith
    -- the pole term
    have hden : t ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at h
      exact h
    have hB : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have hnum : ((N : ℝ) + 1) ^ (1 - s).re ≤ 3 := by
        rw [Complex.sub_re, Complex.one_re]
        refine rpow_one_sub_le_three (by linarith) ?_ hL1 h1 hσ1.le
        exact le_trans (Real.log_le_log (by linarith) (by linarith : (N : ℝ) + 1 ≤ t + 2)) hlog2
      have hpos : (0 : ℝ) < ‖s - 1‖ := by linarith
      rw [div_le_one hpos]
      linarith
    -- the Euler–Maclaurin tail
    have hC : ‖∑' n : ℕ, eulerTerm (n + N) s‖ ≤ 8 := by
      have hbd : ∀ n : ℕ, ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
        fun n => norm_eulerTerm_le (n + N) hσ0.le hs1
      have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))) :=
        (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by linarith))
      have hsummable := hsh.mul_left ‖s‖
      have hnorms : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
        hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
      have hnorm_s : ‖s‖ ≤ 1 + t := by
        have h := Complex.norm_le_abs_re_add_abs_im s
        rw [abs_of_pos hσ0] at h
        linarith
      have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))
          ≤ (N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1) :=
        tsum_shift_rpow_neg_le_rpow (by linarith) hNnat
      have hNneg : (N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1) ≤ 6 / t := by
        have hEq : (1 : ℝ) - (1 + s.re) = -s.re := by ring
        have hEq2 : (1 + s.re) - 1 = s.re := by ring
        rw [hEq, hEq2]
        have hsplit : (N : ℝ) ^ (-s.re) = (N : ℝ) ^ (1 - s.re) * (N : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hNpos]
          ring_nf
        have hNinv : (N : ℝ) ^ (-(1 : ℝ)) = ((N : ℝ))⁻¹ := by
          rw [Real.rpow_neg_one]
        have h3 : (N : ℝ) ^ (-s.re) ≤ 3 / t := by
          rw [hsplit, hNinv]
          have hinv : ((N : ℝ))⁻¹ ≤ 1 / t := by
            rw [← one_div]
            exact one_div_le_one_div_of_le (by linarith) hNle
          calc (N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹ ≤ 3 * (1 / t) := by
                refine mul_le_mul hNbound hinv (by positivity) (by norm_num)
            _ = 3 / t := by ring
        have hdiv : (N : ℝ) ^ (-s.re) / s.re ≤ (3 / t) / (1 / 2) :=
          div_le_div₀ (by positivity) h3 (by norm_num) hσhalf
        calc (N : ℝ) ^ (-s.re) / s.re ≤ (3 / t) / (1 / 2) := hdiv
          _ = 6 / t := by ring
      have hfinal : ‖s‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))
          ≤ (1 + t) * (6 / t) := by
        have h1' : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
          tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
        exact mul_le_mul hnorm_s (le_trans htail hNneg) h1' (by linarith)
      calc ‖∑' n : ℕ, eulerTerm (n + N) s‖
          ≤ ∑' n : ℕ, ‖eulerTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
        _ ≤ ∑' n : ℕ, ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
            hnorms.tsum_le_tsum hbd hsummable
        _ = ‖s‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) := tsum_mul_left
        _ ≤ (1 + t) * (6 / t) := hfinal
        _ ≤ 8 := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < t)]
            linarith
    calc ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
          + ∑' n : ℕ, eulerTerm (n + N) s‖
        ≤ ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
            + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ + ‖∑' n : ℕ, eulerTerm (n + N) s‖ :=
          norm_add_le _ _
      _ ≤ (‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
            + ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖) + ‖∑' n : ℕ, eulerTerm (n + N) s‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((3 + 6 * L) + 1) + 8 := by gcongr
      _ ≤ 18 * L := by linarith

end RiemannHypothesis

end
