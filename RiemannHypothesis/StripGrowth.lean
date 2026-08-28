/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.NearLine

/-!
# The trivial convexity bound for `ζ` inside the critical strip

`RiemannHypothesis.Growth` bounds `ζ` inside the strip by `C(σ) (1 + |t|)`, which is linear
in `|t|` for every `σ`.  With the Euler–Maclaurin representation now available on the whole
punctured right half-plane (`RiemannHypothesis.Continuation`), the classical *trivial bound*

`‖ζ(σ + it)‖ ≤ (8/σ) |t|^(1-σ) (1 + log|t|)`

follows for `0 < σ ≤ 1` and `|t| ≥ 3`.  It is a genuine improvement: at `σ = 1/2` it is
`O(√|t| log|t|)` instead of `O(|t|)`.  The convexity bound `O(|t|^((1-σ)/2 + ε))` of the
approximate functional equation is stronger still and is *not* proved here.

## Main result

* `norm_riemannZeta_le_strip` : `‖ζ(s)‖ ≤ (8/re s) |t|^(1-re s) (1 + log|t|)` for
  `0 < re s ≤ 1` and `|im s| ≥ 3`.
-/

noncomputable section

open Complex Filter Finset

namespace RiemannHypothesis

/-- The elementary inequality behind the final assembly of the strip bound:
`2T(2+L) + T + (2/σ)T ≤ (8/σ) T (1+L)` for `0 < σ ≤ 1`, `1 ≤ L` and `0 ≤ T`. -/
lemma strip_bound_arith {sig L T : ℝ} (h0 : 0 < sig) (h1 : sig ≤ 1) (hL : 1 ≤ L) (hT : 0 ≤ T) :
    2 * T * (2 + L) + T + 2 / sig * T ≤ 8 / sig * T * (1 + L) := by
  have hscalar : 2 * (2 + L) + 1 + 2 / sig ≤ 8 / sig * (1 + L) := by
    have hexp : 8 / sig * (1 + L) = 2 / sig + 6 / sig + 8 / sig * L := by
      field_simp
      ring
    have h6 : (6 : ℝ) ≤ 6 / sig := by
      rw [le_div_iff₀ h0]
      linarith
    have h2 : (2 : ℝ) ≤ 8 / sig := by
      rw [le_div_iff₀ h0]
      linarith
    have h8 : 2 * L ≤ 8 / sig * L :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    rw [hexp]
    linarith
  calc 2 * T * (2 + L) + T + 2 / sig * T
      = (2 * (2 + L) + 1 + 2 / sig) * T := by ring
    _ ≤ (8 / sig * (1 + L)) * T := mul_le_mul_of_nonneg_right hscalar hT
    _ = 8 / sig * T * (1 + L) := by ring

/-- **The trivial convexity bound inside the critical strip.**
For `0 < re s ≤ 1` and `|im s| ≥ 3`,
`‖ζ(s)‖ ≤ (8 / re s) · |im s|^(1 - re s) · (1 + log |im s|)`. -/
theorem norm_riemannZeta_le_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 / s.re * |s.im| ^ (1 - s.re) * (1 + Real.log |s.im|) := by
  set t : ℝ := |s.im| with htdef
  have ht0 : (0 : ℝ) < t := by linarith
  have hL1 : 1 ≤ Real.log t := one_le_log_of_three_le ht
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have him : s.im = 0 := by rw [h]; simp
    rw [htdef, him] at ht
    simp at ht
    linarith
  set N : ℕ := ⌈t⌉₊ with hNdef
  have hNle : t ≤ (N : ℝ) := Nat.le_ceil t
  have hNlt : (N : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hpow0 : (0 : ℝ) < t ^ (1 - s.re) := Real.rpow_pos_of_pos ht0 _
  -- `N^(1-σ) ≤ 2 t^(1-σ)`
  have hNrpow : (N : ℝ) ^ (1 - s.re) ≤ 2 * t ^ (1 - s.re) := by
    have hNle2 : (N : ℝ) ≤ 2 * t := by linarith
    calc (N : ℝ) ^ (1 - s.re) ≤ (2 * t) ^ (1 - s.re) :=
          Real.rpow_le_rpow hNpos.le hNle2 (by linarith)
      _ = 2 ^ (1 - s.re) * t ^ (1 - s.re) := Real.mul_rpow (by norm_num) ht0.le
      _ ≤ 2 * t ^ (1 - s.re) := by
          have h2 : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
            calc (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right h2 hpow0.le
  -- `log N ≤ 1 + log t`
  have hlogN : Real.log (N : ℝ) ≤ 1 + Real.log t := by
    calc Real.log (N : ℝ) ≤ Real.log (2 * t) := Real.log_le_log hNpos (by linarith)
      _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
      _ ≤ 1 + Real.log t := by linarith
  rw [riemannZeta_eq_zetaApprox_of_pos_re N h0 hs1]
  unfold zetaApprox
  -- the truncated Dirichlet sum
  have hA : ‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
      ≤ 2 * t ^ (1 - s.re) * (2 + Real.log t) := by
    have hterm : ∀ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s.re)
        ≤ (N : ℝ) ^ (1 - s.re) * ((n : ℝ) + 1) ^ (-(1 : ℝ)) := by
      intro n hn
      have hnN : ((n : ℝ) + 1) ≤ (N : ℝ) := by
        have h := Finset.mem_range.mp hn
        have : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h
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
      _ ≤ (2 * t ^ (1 - s.re)) * (1 + Real.log (N : ℝ)) := by
          refine mul_le_mul hNrpow
            (sum_range_natAddOne_rpow_neg_le_one_add_log (le_refl 1) N) ?_ (by positivity)
          exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
      _ ≤ 2 * t ^ (1 - s.re) * (2 + Real.log t) := by
          have : (1 : ℝ) + Real.log (N : ℝ) ≤ 2 + Real.log t := by linarith
          exact mul_le_mul_of_nonneg_left this (by positivity)
  -- the pole term
  have hden : t ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact h
  have htneg : t ^ (1 - s.re) = t ^ (-s.re) * t := by
    rw [show (1 - s.re) = (-s.re) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
  have hB : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ t ^ (1 - s.re) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hnum : ((N : ℝ) + 1) ^ (1 - s).re ≤ 2 * t ^ (1 - s.re) := by
      rw [Complex.sub_re, Complex.one_re]
      have hNle2 : (N : ℝ) + 1 ≤ 2 * t := by linarith
      calc ((N : ℝ) + 1) ^ (1 - s.re) ≤ (2 * t) ^ (1 - s.re) :=
            Real.rpow_le_rpow (by positivity) hNle2 (by linarith)
        _ = 2 ^ (1 - s.re) * t ^ (1 - s.re) := Real.mul_rpow (by norm_num) ht0.le
        _ ≤ 2 * t ^ (1 - s.re) := by
            have h2 : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
              calc (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 := Real.rpow_one 2
            exact mul_le_mul_of_nonneg_right h2 hpow0.le
    have hpos : (0 : ℝ) < ‖s - 1‖ := by linarith
    rw [div_le_iff₀ hpos]
    calc ((N : ℝ) + 1) ^ (1 - s).re ≤ 2 * t ^ (1 - s.re) := hnum
      _ ≤ t ^ (1 - s.re) * t := by nlinarith
      _ ≤ t ^ (1 - s.re) * ‖s - 1‖ := by nlinarith
  -- the Euler–Maclaurin tail
  have hC : ‖∑' n : ℕ, eulerTerm (n + N) s‖ ≤ 2 / s.re * t ^ (1 - s.re) := by
    have hbd : ∀ n : ℕ, ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
      fun n => norm_eulerTerm_le (n + N) h0.le hs1
    have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by linarith))
    have hsummable := hsh.mul_left ‖s‖
    have hnorms : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
      hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
    have hnorm_s : ‖s‖ ≤ 1 + t := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos h0] at h
      linarith
    have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))
        ≤ (N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1) :=
      tsum_shift_rpow_neg_le_rpow (by linarith) hNnat
    have hNtail : (N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1)
        ≤ t ^ (1 - s.re) / (s.re * t) := by
      have hEq : (1 : ℝ) - (1 + s.re) = -s.re := by ring
      have hEq2 : (1 + s.re) - 1 = s.re := by ring
      rw [hEq, hEq2]
      have hNt : (N : ℝ) ^ (-s.re) ≤ t ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos ht0 hNle (by linarith)
      rw [div_le_div_iff₀ h0 (by positivity)]
      calc (N : ℝ) ^ (-s.re) * (s.re * t) ≤ t ^ (-s.re) * (s.re * t) :=
            mul_le_mul_of_nonneg_right hNt (by positivity)
        _ = t ^ (1 - s.re) * s.re := by rw [htneg]; ring
    calc ‖∑' n : ℕ, eulerTerm (n + N) s‖
        ≤ ∑' n : ℕ, ‖eulerTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
          hnorms.tsum_le_tsum hbd hsummable
      _ = ‖s‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) := tsum_mul_left
      _ ≤ (1 + t) * (t ^ (1 - s.re) / (s.re * t)) := by
          have h1' : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
            tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
          exact mul_le_mul hnorm_s (le_trans htail hNtail) h1' (by linarith)
      _ ≤ 2 / s.re * t ^ (1 - s.re) := by
          have hfrac : (1 + t) / (s.re * t) ≤ 2 / s.re := by
            rw [div_le_div_iff₀ (by positivity) h0]
            nlinarith
          calc (1 + t) * (t ^ (1 - s.re) / (s.re * t))
              = ((1 + t) / (s.re * t)) * t ^ (1 - s.re) := by ring
            _ ≤ (2 / s.re) * t ^ (1 - s.re) :=
                mul_le_mul_of_nonneg_right hfrac hpow0.le
  -- combine
  calc ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        + ∑' n : ℕ, eulerTerm (n + N) s‖
      ≤ ‖(∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
          + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ + ‖∑' n : ℕ, eulerTerm (n + N) s‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)‖
          + ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖) + ‖∑' n : ℕ, eulerTerm (n + N) s‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (2 * t ^ (1 - s.re) * (2 + Real.log t) + t ^ (1 - s.re))
          + 2 / s.re * t ^ (1 - s.re) := by gcongr
    _ ≤ 8 / s.re * t ^ (1 - s.re) * (1 + Real.log t) :=
        strip_bound_arith h0 h1 hL1 hpow0.le

end RiemannHypothesis

end
