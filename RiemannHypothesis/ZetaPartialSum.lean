/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.VanDerCorputSumIntegral
import RiemannHypothesis.Continuation

/-!
# `ζ` and its partial sums (Titchmarsh, Theorem 4.11)

For `s = σ + it` with `σ > 0`, `s ≠ 1`, and real `x > 0` with `|t| ≤ x`,

  `‖ζ(s) − ∑_{n ≤ x} n^(-s) + x^(1-s)/(1 − s)‖ ≤ 11 x^(-σ)`
  (`norm_riemannZeta_sub_partialSum_le`; on the critical line,
  `norm_riemannZeta_criticalLine_sub_partialSum_le`).

This is Titchmarsh's Theorem 4.11 (*The Theory of the Riemann Zeta-Function*) with `C = 2π`
in his hypothesis `x ≥ C|t|/(2π)`, an explicit constant, and no threshold on `t`.  In
particular a Dirichlet polynomial of length `x ≍ |t|` approximates `ζ(1/2 + it)` with error
`O(x^(-1/2))`: the approximate functional equation is not needed for this.

## The argument (Titchmarsh's)

* `riemannZeta_eq_zetaApprox_of_pos_re` (`RiemannHypothesis/Continuation.lean`) writes
  `ζ(s) = ∑_{n ≤ M} n^(-s) + (M+1)^(1-s)/(s − 1) + (Euler–Maclaurin tail)` for every `M`, and
  the tail tends to `0` as `M → ∞`.
* For `M ≥ x`, `ζ(s) − ∑_{n ≤ x} n^(-s) + x^(1-s)/(1 − s)` is therefore
  `∑_{x < n ≤ M} n^(-s) − ∫_x^{M+1} u^(-s) du` plus the tail.
* With `n^(-s) = n^(-σ) e(−(t/2π) log n)`, the phase has derivative `−t/(2πu)`, monotone and of
  size at most `1/(2π)` for `u ≥ x ≥ |t|`, and the weight `u^(-σ)` decreases; the weighted
  sum-versus-integral lemma of `RiemannHypothesis/VanDerCorputSumIntegral.lean` bounds the
  difference by `(9/2 + 5κ/2) x^(-σ)` with `κ = κ(1/(2π)) = 2 − cot(1/2) < 2`
  (`norm_sum_cpow_sub_integral_le`), and the piece `∫_x^{⌊x⌋+1}` adds at most `x^(-σ)`.
* Letting `M → ∞` gives the constant `11/2 + 5κ/2 < 11`.

No hypothesis is assumed.
-/

noncomputable section

open Complex Real Finset Filter MeasureTheory intervalIntegral

namespace RiemannHypothesis

namespace ZetaPartialSum

open KusminLandau VdcSumIntegral

/-- `u^(-s) = u^(-σ) e(−(t/2π) log u)` for `u > 0`, `s = σ + it`. -/
theorem cpow_neg_eq_rpow_mul_e2pi {u : ℝ} (hu : 0 < u) (s : ℂ) :
    (u : ℂ) ^ (-s) = ((u ^ (-s.re) : ℝ) : ℂ) * e2pi (-(s.im / (2 * Real.pi)) * Real.log u) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
    Real.rpow_def_of_pos hu, e2pi, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im s]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- The constant of the sum-versus-integral lemma at `θ = 1/(2π)`:
`5/2 + 4π · 1/(2π) + 5κ/2 = 9/2 + 5κ(1/(2π))/2`. -/
theorem vdcKappa_half_inv_pi_lt_two : vdcKappa (1 / (2 * Real.pi)) < 2 := by
  have hpi := Real.pi_pos
  have h1 : Real.pi * (1 / (2 * Real.pi)) = 1 / 2 := by field_simp
  have hs : 0 < Real.sin (1 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hc : 0 < Real.cos (1 / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  rw [vdcKappa, cotDefect, cotpi, h1]
  have : 0 < Real.cos (1 / 2) / Real.sin (1 / 2) := div_pos hc hs
  norm_num
  linarith

/-- **The sum-versus-integral lemma for `u^(-s)`**: for `a > 0` with `|t| ≤ a`, `σ ≥ 0`,
`‖∑_{j < L} (a+j)^(-s) − ∫_a^{a+L} u^(-s) du‖ ≤ (9/2 + 5κ/2) a^(-σ)` with
`κ = κ(1/(2π)) < 2`. -/
theorem norm_sum_cpow_sub_integral_le {s : ℂ} (hs : 0 ≤ s.re) {a : ℝ} (ha : 0 < a)
    (hta : |s.im| ≤ a) (L : ℕ) :
    ‖∑ j ∈ range L, (((a + j : ℝ)) : ℂ) ^ (-s) - ∫ u in a..a + L, (u : ℂ) ^ (-s)‖
      ≤ (9 / 2 + 5 / 2 * vdcKappa (1 / (2 * Real.pi))) * a ^ (-s.re) := by
  have hpi := Real.pi_pos
  set c : ℝ := s.im / (2 * Real.pi) with hcdef
  set f : ℝ → ℝ := fun u => -c * Real.log u with hfdef
  set f' : ℝ → ℝ := fun u => -c * u⁻¹ with hf'def
  set g : ℝ → ℝ := fun u => u ^ (-s.re) with hgdef
  have hpos : ∀ u ∈ Set.Icc a (a + L), 0 < u := fun u hu => ha.trans_le hu.1
  have hf : ∀ u ∈ Set.Icc a (a + L), HasDerivAt f (f' u) u := fun u hu =>
    (Real.hasDerivAt_log (hpos u hu).ne').const_mul (-c)
  have hbd : ∀ u ∈ Set.Icc a (a + L), |f' u| ≤ 1 / (2 * Real.pi) := by
    intro u hu
    have hu0 := hpos u hu
    simp only [hf'def, hcdef]
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hu0, abs_div,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : |s.im| ≤ u := hta.trans hu.1
    calc |s.im| * u⁻¹ * (2 * Real.pi) ≤ u * u⁻¹ * (2 * Real.pi) := by gcongr
      _ = 2 * Real.pi := by field_simp
  have hθ : 1 / (2 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]; linarith [Real.pi_gt_three]
  have hg : ContinuousOn g (Set.Icc a (a + L)) := fun u hu =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (hpos u hu).ne')).continuousWithinAt
  have hg0 : ∀ u ∈ Set.Icc a (a + L), 0 ≤ g u := fun u hu => Real.rpow_nonneg (hpos u hu).le _
  have hganti : AntitoneOn g (Set.Icc a (a + L)) := fun u hu v _ huv =>
    Real.rpow_le_rpow_of_nonpos (hpos u hu) huv (by linarith)
  have hmain : ‖∑ n ∈ range L, (g (a + n) : ℂ) * e2pi (f (a + n))
        - ∫ u in a..a + L, (g u : ℂ) * e2pi (f u)‖
      ≤ (5 / 2 + 4 * Real.pi * (1 / (2 * Real.pi)) + 5 / 2 * vdcKappa (1 / (2 * Real.pi)))
        * g a := by
    rcases le_total 0 c with hc | hc
    · refine norm_sum_mul_e2pi_sub_integral_le hθ hf ?_ hbd hg hg0 hganti
      intro u hu v hv huv
      simp only [hf'def]
      have := inv_anti₀ (hpos u hu) huv
      nlinarith
    · refine norm_sum_mul_e2pi_sub_integral_le_of_antitone hθ hf ?_ hbd hg hg0 hganti
      intro u hu v hv huv
      simp only [hf'def]
      have := inv_anti₀ (hpos u hu) huv
      nlinarith
  have hsum : ∑ j ∈ range L, (((a + j : ℝ)) : ℂ) ^ (-s)
      = ∑ n ∈ range L, (g (a + n) : ℂ) * e2pi (f (a + n)) := by
    refine sum_congr rfl fun j _ => ?_
    rw [cpow_neg_eq_rpow_mul_e2pi (by positivity : 0 < a + j)]
  have hint : ∫ u in a..a + L, (u : ℂ) ^ (-s) = ∫ u in a..a + L, (g u : ℂ) * e2pi (f u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by simp)] at hu
    exact cpow_neg_eq_rpow_mul_e2pi (hpos u hu) s
  rw [hsum, hint]
  refine hmain.trans (le_of_eq ?_)
  simp only [hgdef]
  congr 1
  field_simp
  ring

/-- The approximation of `ζ(s)` by `∑_{n ≤ x} n^(-s) − x^(1-s)/(1 − s)`, up to the
Euler–Maclaurin tail at a level `M' ≥ ⌊x⌋`. -/
theorem norm_zeta_sub_partialSum_le_add_tail {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ}
    (hx : 0 < x) (hxt : |s.im| ≤ x) (M' : ℕ) (hM' : ⌊x⌋₊ ≤ M') :
    ‖riemannZeta s - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) + (x : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ (11 / 2 + 5 / 2 * vdcKappa (1 / (2 * Real.pi))) * x ^ (-s.re)
        + ‖∑' n : ℕ, eulerTerm (n + M') s‖ := by
  set K0 := ⌊x⌋₊ with hK0
  set m : ℝ := (K0 : ℝ) + 1 with hmdef
  set L : ℕ := M' - K0 with hLdef
  have hxm : x < m := Nat.lt_floor_add_one x
  have hmx : m ≤ x + 1 := by have := Nat.floor_le hx.le; rw [hmdef]; linarith
  have hm0 : 0 < m := by positivity
  have hML : M' = K0 + L := by omega
  have hMreal : ((M' : ℝ) + 1) = m + L := by
    rw [hmdef, hML]; push_cast; ring
  have hζ := riemannZeta_eq_zetaApprox_of_pos_re M' hs0 hs1
  rw [zetaApprox] at hζ
  -- splitting the partial sum at `x`
  have hsplit : ∑ n ∈ Finset.range M', (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
      = ∑ n ∈ Icc 1 K0, (n : ℂ) ^ (-s) + ∑ j ∈ range L, (((m + j : ℝ)) : ℂ) ^ (-s) := by
    rw [hML, sum_range_add]
    congr 1
    · rw [show Finset.Icc 1 K0 = Finset.Ico 1 (K0 + 1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
      refine sum_congr (by congr 1) fun k _ => ?_
      push_cast
      ring_nf
    · refine sum_congr rfl fun j _ => ?_
      rw [hmdef]
      push_cast
      ring_nf
  -- the integrals
  have hint_total : ∫ u in x..m + L, (u : ℂ) ^ (-s)
      = (((m + L : ℝ) : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s) :=
    integral_cpow_neg hx (by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith) hs1
  have hcpow_int : ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s)) MeasureTheory.volume a b := by
    intro a b ha hb
    refine intervalIntegral.intervalIntegrable_cpow (Or.inr ?_)
    intro h0
    rcases Set.mem_uIcc.mp h0 with h | h <;> linarith [h.1, h.2]
  have hint_split : (∫ u in x..m, (u : ℂ) ^ (-s)) + ∫ u in m..m + L, (u : ℂ) ^ (-s)
      = ∫ u in x..m + L, (u : ℂ) ^ (-s) :=
    intervalIntegral.integral_add_adjacent_intervals (hcpow_int _ _ hx hm0)
      (hcpow_int _ _ hm0 (by positivity))
  have hsmall : ‖∫ u in x..m, (u : ℂ) ^ (-s)‖ ≤ x ^ (-s.re) := by
    have hb : ∀ u ∈ Set.uIoc x m, ‖(u : ℂ) ^ (-s)‖ ≤ x ^ (-s.re) := by
      intro u hu
      rw [Set.uIoc_of_le hxm.le] at hu
      have hu0 : 0 < u := hx.trans hu.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos hx hu.1.le (by linarith)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have h1 : |m - x| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
    have h2 : 0 ≤ x ^ (-s.re) := Real.rpow_nonneg hx.le _
    nlinarith
  have hvdc := norm_sum_cpow_sub_integral_le hs0.le hm0 (hxt.trans hxm.le) L
  have hmpow : m ^ (-s.re) ≤ x ^ (-s.re) := Real.rpow_le_rpow_of_nonpos hx hxm.le (by linarith)
  -- the algebra
  set S2 := ∑ j ∈ range L, (((m + j : ℝ)) : ℂ) ^ (-s)
  set I1 := ∫ u in x..m, (u : ℂ) ^ (-s)
  set I2 := ∫ u in m..m + L, (u : ℂ) ^ (-s)
  set T := ∑' n : ℕ, eulerTerm (n + M') s
  set B : ℂ := ((m + L : ℝ) : ℂ) ^ (1 - s)
  have hB : (((M' : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) = B := by rw [hMreal]
  rw [hsplit, hB] at hζ
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hinv : (s - 1)⁻¹ = -(1 - s)⁻¹ := by rw [← neg_sub, inv_neg]
  have hE : riemannZeta s - ∑ n ∈ Icc 1 K0, (n : ℂ) ^ (-s) + (x : ℂ) ^ (1 - s) / (1 - s)
      = (S2 - I2) - I1 + T := by
    rw [hint_total] at hint_split
    simp only [div_eq_mul_inv, hinv] at hζ hint_split ⊢
    linear_combination hζ + hint_split
  rw [hE]
  have hnn : 0 ≤ x ^ (-s.re) := Real.rpow_nonneg hx.le _
  have hκ : 0 ≤ vdcKappa (1 / (2 * Real.pi)) := vdcKappa_nonneg (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith [Real.pi_gt_three])
  calc ‖(S2 - I2) - I1 + T‖ ≤ ‖S2 - I2‖ + ‖I1‖ + ‖T‖ :=
        (norm_add_le _ _).trans (by linarith [norm_sub_le (S2 - I2) I1])
    _ ≤ (9 / 2 + 5 / 2 * vdcKappa (1 / (2 * Real.pi))) * x ^ (-s.re) + x ^ (-s.re) + ‖T‖ := by
        gcongr
        exact hvdc.trans (mul_le_mul_of_nonneg_left hmpow (by positivity))
    _ = _ := by ring

/-- **The approximation of `ζ` by its partial sums** (Titchmarsh, *The Theory of the Riemann
Zeta-Function*, Theorem 4.11, with `C = 2π`): for `s = σ + it` with `σ > 0`, `s ≠ 1`, and
real `x > 0` with `|t| ≤ x`,
`‖ζ(s) − ∑_{n ≤ x} n^(-s) + x^(1-s)/(1 − s)‖ ≤ 11 x^(-σ)`. -/
theorem norm_riemannZeta_sub_partialSum_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ}
    (hx : 0 < x) (hxt : |s.im| ≤ x) :
    ‖riemannZeta s - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) + (x : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ 11 * x ^ (-s.re) := by
  set C := (11 / 2 + 5 / 2 * vdcKappa (1 / (2 * Real.pi))) * x ^ (-s.re)
  have htend : Tendsto (fun M' : ℕ => C + ‖∑' n : ℕ, eulerTerm (n + M') s‖) atTop
      (nhds (C + 0)) := by
    have h := (tendsto_sum_nat_add (fun n => eulerTerm n s)).norm
    rw [norm_zero] at h
    exact tendsto_const_nhds.add h
  have hle := ge_of_tendsto htend (eventually_atTop.mpr ⟨⌊x⌋₊, fun M' hM' =>
    norm_zeta_sub_partialSum_le_add_tail hs0 hs1 hx hxt M' hM'⟩)
  rw [add_zero] at hle
  refine hle.trans ?_
  have hκ := vdcKappa_half_inv_pi_lt_two
  have hnn : 0 ≤ x ^ (-s.re) := Real.rpow_nonneg hx.le _
  exact mul_le_mul_of_nonneg_right (by linarith) hnn

/-- **Theorem 4.11 on the critical line**: for real `t` and `x > 0` with `|t| ≤ x`,
`‖ζ(1/2 + it) − ∑_{n ≤ x} n^(-1/2-it) + x^(1/2-it)/(1/2 − it)‖ ≤ 11 x^(-1/2)`. -/
theorem norm_riemannZeta_criticalLine_sub_partialSum_le {t x : ℝ} (hx : 0 < x) (hxt : |t| ≤ x) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        + (x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I) / (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I)‖
      ≤ 11 * x ^ (-(1 / 2 : ℝ)) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have h1s : (1 : ℂ) - s = ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I := by
    rw [hs]; push_cast; ring
  have h := norm_riemannZeta_sub_partialSum_le (s := s) (by rw [hre]; norm_num) hs1 hx
    (by rw [him]; exact hxt)
  rw [h1s, hre] at h
  exact h

end ZetaPartialSum

end RiemannHypothesis
