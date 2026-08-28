/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Main
import RiemannHypothesis.Symmetry

/-!
# The alternating series in the whole strip, and a fully elementary form of the hypothesis

`RiemannHypothesis.Eta` identifies `η` with the *unconditional* sum
`∑' n, (-1)^n / (n+1)^s` only on the half-plane of absolute convergence `1 < re s`; inside
the critical strip that series converges only conditionally, so its `tsum` is useless there.
What is true, and proved here, is that the *partial sums* of the alternating series converge
to `η(s)` on the whole right half-plane `0 < re s`:

* `tendsto_alternating_partialSum_dirichletEta` :
  `∑_{n < N} (-1)^n / (n+1)^s → η(s)` as `N → ∞`, for `0 < re s`.

The proof splits a partial sum into complete pairs plus at most one leftover term
(`sum_alternating_eq_pairedSum_add_rem`): the paired sums converge to `η(s)` because the
paired series is absolutely convergent, and the leftover term has norm `N ^ (-re s) → 0`.

As a consequence the Riemann hypothesis has a formulation that mentions neither analytic
continuation nor an unconditional sum — only the limit of the partial sums of an explicit
elementary series:

* `EtaLimitForm` : if the partial sums of `∑ (-1)^n / (n+1)^s` tend to `0` for some `s` in
  the critical strip, then `re s = 1/2`;
* `eta_iff_eta_limit` : `EtaForm ↔ EtaLimitForm`, hence (with `RiemannHypothesis.Main`)
  `ZetaForm ↔ EtaLimitForm` (`zeta_iff_eta_limit`).
-/

noncomputable section

open Complex Filter Finset
open scoped Topology

namespace RiemannHypothesis

/-- The `N`-th partial sum of the alternating series splits into `N / 2` complete pairs plus
a leftover term when `N` is odd. -/
lemma sum_alternating_eq_pairedSum_add_rem (s : ℂ) (N : ℕ) :
    ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s
      = (∑ j ∈ range (N / 2), pairedTerm j s)
        + (if N % 2 = 0 then 0 else ((N : ℂ)) ^ (-s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd N with hN | hN
    · -- `N` even: the new term opens a fresh pair
      obtain ⟨K, hK⟩ := hN
      subst hK
      have hmod : (K + K) % 2 = 0 := by omega
      have hmod' : (K + K + 1) % 2 = 1 := by omega
      have hdiv : (K + K + 1) / 2 = (K + K) / 2 := by omega
      have hsign : (-1 : ℂ) ^ (K + K) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hmod, hmod', hdiv, hsign]
      simp only [reduceIte, add_zero]
      have hcast : ((K + K : ℕ) : ℂ) + 1 = ((K + K + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast, one_div, ← cpow_neg]
      simp
    · -- `N` odd: the new term closes the pair opened by the leftover
      obtain ⟨K, hK⟩ := hN
      subst hK
      have hmod : (2 * K + 1) % 2 = 1 := by omega
      have hmod' : (2 * K + 1 + 1) % 2 = 0 := by omega
      have hdiv : (2 * K + 1) / 2 = K := by omega
      have hdiv' : (2 * K + 1 + 1) / 2 = K + 1 := by omega
      have hsign : (-1 : ℂ) ^ (2 * K + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [hmod, hmod', hdiv, hdiv', hsign, sum_range_succ, pairedTerm]
      simp only [reduceIte, add_zero]
      have hcast : ((2 * K + 1 : ℕ) : ℂ) + 1 = ((2 * K + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast, show (-1 : ℂ) / (((2 * K + 2 : ℕ) : ℂ)) ^ s
          = -((((2 * K + 2 : ℕ) : ℂ)) ^ (-s)) by
        rw [cpow_neg, div_eq_mul_inv]
        ring]
      simp
      ring

/-- The leftover term tends to `0` for `0 < re s`. -/
lemma tendsto_rem_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => if N % 2 = 0 then (0 : ℂ) else ((N : ℂ)) ^ (-s)) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ,
      ‖if N % 2 = 0 then (0 : ℂ) else ((N : ℂ)) ^ (-s)‖ ≤ (N : ℝ) ^ (-s.re) := by
    intro N
    by_cases hN : N % 2 = 0
    · simp only [hN, if_pos, norm_zero]
      positivity
    · have hNpos : 0 < (N : ℝ) := by
        have : N ≠ 0 := by omega
        exact_mod_cast Nat.pos_of_ne_zero this
      simp only [hN, if_false]
      rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      simp
  have hzero : Tendsto (fun N : ℕ => (N : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  exact squeeze_zero_norm hbound hzero

/-- **The alternating series representation on the whole right half-plane.**  For `0 < re s`
the partial sums of the classical alternating series converge to `η(s)`.  (For `1 < re s`
this is the unconditional sum, `dirichletEta_eq_tsum_alternating_of_one_lt_re`; inside the
critical strip the series converges only conditionally, so the statement has to be about
partial sums.) -/
theorem tendsto_alternating_partialSum_dirichletEta {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 (dirichletEta s)) := by
  have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun M => ⟨2 * M, fun N hN => by omega⟩
  have hpair : Tendsto (fun N : ℕ => ∑ j ∈ range (N / 2), pairedTerm j s) atTop
      (𝓝 (dirichletEta s)) :=
    ((summable_pairedTerm hs).tendsto_sum_tsum_nat).comp hhalf
  have := hpair.add (tendsto_rem_zero hs)
  rw [add_zero] at this
  exact this.congr fun N => (sum_alternating_eq_pairedSum_add_rem s N).symm

/-- **The Riemann hypothesis, elementarily**: if the partial sums of the alternating series
`∑ (-1)^n / (n+1)^s` tend to `0` at a point of the critical strip, then that point lies on
the critical line.  No analytic continuation and no unconditional summation appear in this
statement. -/
def EtaLimitForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop (𝓝 0) →
    s.re = 1 / 2

/-- **The eta form and the elementary limit form are equivalent.** -/
theorem eta_iff_eta_limit : EtaForm ↔ EtaLimitForm := by
  constructor
  · intro h s hs0 hs1 hlim
    have heta : dirichletEta s = 0 :=
      tendsto_nhds_unique (tendsto_alternating_partialSum_dirichletEta hs0) hlim
    exact h s hs0 hs1 heta
  · intro h s hs0 hs1 heta
    refine h s hs0 hs1 ?_
    have := tendsto_alternating_partialSum_dirichletEta hs0
    rwa [heta] at this

/-- **The Riemann hypothesis is equivalent to its elementary limit form.** -/
theorem zeta_iff_eta_limit : ZetaForm ↔ EtaLimitForm :=
  zeta_iff_eta.trans eta_iff_eta_limit

end RiemannHypothesis

end
