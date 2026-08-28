/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Criteria
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Abel summation for Dirichlet series with cancellation in the partial sums

Several classical routes towards the Riemann hypothesis have the same analytic skeleton:
one starts from an arithmetic function `a : ℕ → ℂ` whose partial sums

`A(N) = ∑_{1 ≤ n ≤ N} a n`   (`partialSum`)

are small, say `A(N) = O(N^{θ+ε})` for every `ε > 0` (`PartialSumBound a θ`), and deduces
that the Dirichlet series `∑ a n n^{-s}` continues holomorphically to the half-plane
`re s > θ`.

This file isolates that skeleton once and for all.  Summation by parts rewrites the (only
conditionally convergent) Dirichlet series as

`F(s) = ∑_{n ≥ 1} A(n) (n^{-s} - (n+1)^{-s})`   (`abelSum`),

which converges *absolutely* on `re s > θ` because
`‖n^{-s} - (n+1)^{-s}‖ ≤ ‖s‖ n^{-re s - 1}` (`norm_cpow_sub_succ_cpow_le`).  The Weierstrass
M-test then gives holomorphy (`differentiableOn_abelSum`), and wherever the original
Dirichlet series converges `F` agrees with it (`abelSum_eq_LSeries`).

The exponent `θ` is constrained only by `-1 ≤ θ`, which is what the elementary estimate on
`n^{-s} - (n+1)^{-s}` needs.  The case `θ = 1/2` (`SqrtCancellation`, square-root
cancellation) is used by the Mertens criterion (`RiemannHypothesis.MoebiusCriterion`) and by
the Chebyshev criterion (`RiemannHypothesis.ChebyshevCriterion`); the case `θ = -1/2` is used
by the criterion for `∑_{n ≤ N} μ(n)/n` (`RiemannHypothesis.MoebiusOverNCriterion`).
-/

noncomputable section

open Complex Filter Finset
open scoped Topology

namespace RiemannHypothesis

/-- The partial sums `A(N) = ∑_{1 ≤ n ≤ N} a n` of an arithmetic function. -/
def partialSum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Icc 1 N, a n

/-- **Cancellation of exponent `θ`** in the partial sums of `a`: `A(N) = O(N^{θ+ε})` for
every `ε > 0`. -/
def PartialSumBound (a : ℕ → ℂ) (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, ‖partialSum a N‖ ≤ C * (N : ℝ) ^ (θ + ε)

/-- **Square-root cancellation** for the partial sums of `a`: `A(N) = O(N^{1/2+ε})` for
every `ε > 0`. -/
def SqrtCancellation (a : ℕ → ℂ) : Prop := PartialSumBound a (1 / 2)

/-- The `n`-th term of the series obtained from `∑ a n n^{-s}` by summation by parts. -/
def abelTerm (a : ℕ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  partialSum a n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

/-- The Abel-summed Dirichlet series `∑ A(n) (n^{-s} - (n+1)^{-s})`. -/
def abelSum (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ, abelTerm a n s

/-! ## Elementary facts -/

@[simp] lemma partialSum_zero (a : ℕ → ℂ) : partialSum a 0 = 0 := by simp [partialSum]

lemma partialSum_succ (a : ℕ → ℂ) (N : ℕ) :
    partialSum a (N + 1) = partialSum a N + a (N + 1) := by
  simp [partialSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

@[simp] lemma abelTerm_zero (a : ℕ → ℂ) (s : ℂ) : abelTerm a 0 s = 0 := by simp [abelTerm]

/-- A `PartialSumBound` may always be taken with a nonnegative constant. -/
lemma PartialSumBound.exists_nonneg {a : ℕ → ℂ} {θ : ℝ} (h : PartialSumBound a θ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖partialSum a N‖ ≤ C * (N : ℝ) ^ (θ + ε) := by
  obtain ⟨C₀, hC₀⟩ := h ε hε
  refine ⟨max C₀ 0, le_max_right _ _, fun N => (hC₀ N).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ## The basic estimate -/

/-- `‖n^{-s} - (n+1)^{-s}‖ ≤ ‖s‖ · n^{-(re s + 1)}` for `n ≥ 1` and `re s ≥ 0`. -/
lemma norm_cpow_sub_succ_cpow_le {s : ℂ} (hs : -1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-(s.re + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hf
  set C : ℝ := ‖s‖ * (n : ℝ) ^ (-(s.re + 1)) with hC
  have hderiv : ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
      HasDerivWithinAt f ((-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have : (0 : ℝ) < t := lt_of_lt_of_le hn0 ht.1
      exact this.ne'
    exact (hasDerivAt_ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1), ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ C := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hn0 ht.1
    have hre : (-s - 1).re = -(s.re + 1) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      ring
    have hnorm : ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    rw [norm_mul, norm_neg, hnorm, hC]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hn0 ht.1 (by linarith)
  have hmvt := (convex_Icc (n : ℝ) ((n : ℝ) + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  have hfn : f (n : ℝ) = (n : ℂ) ^ (-s) := by simp [hf]
  have hfn1 : f ((n : ℝ) + 1) = ((n : ℂ) + 1) ^ (-s) := by simp [hf]
  rw [hfn, hfn1] at hmvt
  calc ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖
      = ‖((n : ℂ) + 1) ^ (-s) - (n : ℂ) ^ (-s)‖ := norm_sub_rev _ _
    _ ≤ C * ‖(n : ℝ) + 1 - (n : ℝ)‖ := hmvt
    _ = C := by
        have h1 : ‖(n : ℝ) + 1 - (n : ℝ)‖ = 1 := by
          rw [show (n : ℝ) + 1 - (n : ℝ) = 1 by ring]
          simp
        rw [h1, mul_one]

/-! ## Absolute convergence and holomorphy -/

lemma differentiable_abelTerm (a : ℕ → ℂ) (n : ℕ) : Differentiable ℂ (abelTerm a n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : abelTerm a 0 = fun _ : ℂ => (0 : ℂ) := by
      funext z
      simp
    rw [hzero]
    exact differentiable_const 0
  · have hn0 : ((n : ℂ)) ≠ 0 := by
      simpa using (by omega : n ≠ 0)
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by
      intro h
      have hre : ((n : ℂ) + 1).re = 0 := by rw [h]; simp
      simp at hre
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    intro z
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-w)) z :=
      (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) z :=
      (differentiableAt_id.neg).const_cpow (Or.inl hn1)
    exact ((h1.sub h2).const_mul _)

/-- Under a partial-sum bound of exponent `θ` the Abel-summed series is dominated, uniformly
on the region `{re z ≥ δ, ‖z‖ ≤ M}` with `δ > θ`, by a summable sequence. -/
lemma exists_summable_bound_abelTerm {a : ℕ → ℂ} {θ : ℝ} (hθ : -1 ≤ θ)
    (ha : PartialSumBound a θ) {δ : ℝ} (hδ : θ < δ) (M : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (n : ℕ) (z : ℂ), δ ≤ z.re → ‖z‖ ≤ M → ‖abelTerm a n z‖ ≤ u n := by
  set eps : ℝ := (δ - θ) / 2 with heps
  have heps0 : 0 < eps := by rw [heps]; linarith
  obtain ⟨C, hC0, hC⟩ := ha.exists_nonneg heps0
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set e : ℝ := θ + eps - δ - 1 with he
  have helt : e < -1 := by rw [he, heps]; linarith
  have hene : e ≠ 0 := by linarith
  refine ⟨fun n => C * M' * (n : ℝ) ^ e, (Real.summable_nat_rpow.mpr helt).mul_left _, ?_⟩
  intro n z hz hzM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hene]
  · have hn1 : 1 ≤ n := hn
    have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hzre : -1 ≤ z.re := le_trans (by linarith) hz
    have hdiff := norm_cpow_sub_succ_cpow_le hzre hn1
    have hzM' : ‖z‖ ≤ M' := le_trans hzM (le_max_left _ _)
    have hstep1 : ‖abelTerm a n z‖
        ≤ (C * (n : ℝ) ^ (θ + eps)) * (‖z‖ * (n : ℝ) ^ (-(z.re + 1))) := by
      rw [abelTerm, norm_mul]
      exact mul_le_mul (hC n) hdiff (norm_nonneg _) (by positivity)
    have hstep2 : (C * (n : ℝ) ^ (θ + eps)) * (‖z‖ * (n : ℝ) ^ (-(z.re + 1)))
        ≤ (C * (n : ℝ) ^ (θ + eps)) * (M' * (n : ℝ) ^ (-(δ + 1))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul hzM' ?_ (by positivity) hM'0
      exact Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
    have hpow : (n : ℝ) ^ (θ + eps) * (n : ℝ) ^ (-(δ + 1)) = (n : ℝ) ^ e := by
      rw [← Real.rpow_add hn0R, he]
      ring_nf
    have hstep3 : (C * (n : ℝ) ^ (θ + eps)) * (M' * (n : ℝ) ^ (-(δ + 1)))
        = C * M' * (n : ℝ) ^ e := by
      rw [← hpow]
      ring
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]

lemma summable_abelTerm {a : ℕ → ℂ} {θ : ℝ} (hθ : -1 ≤ θ) (ha : PartialSumBound a θ) {s : ℂ}
    (hs : θ < s.re) : Summable (fun n : ℕ => abelTerm a n s) := by
  set δ : ℝ := (θ + s.re) / 2 with hδdef
  have hδ : θ < δ := by rw [hδdef]; linarith
  have hδs : δ ≤ s.re := by rw [hδdef]; linarith
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound_abelTerm hθ ha hδ ‖s‖
  exact Summable.of_norm_bounded hu (fun n => hbound n s hδs le_rfl)

/-- **Holomorphy of the Abel-summed Dirichlet series** on the half-plane `re s > θ`. -/
lemma differentiableOn_abelSum {a : ℕ → ℂ} {θ : ℝ} (hθ : -1 ≤ θ) (ha : PartialSumBound a θ) :
    DifferentiableOn ℂ (abelSum a) {s : ℂ | θ < s.re} := by
  intro s hs
  have hs' : θ < s.re := hs
  set δ : ℝ := (θ + s.re) / 2 with hδdef
  have hδ : θ < δ := by rw [hδdef]; linarith
  have hδs : δ < s.re := by rw [hδdef]; linarith
  set r : ℝ := s.re - δ with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound_abelTerm hθ ha hδ (‖s‖ + r)
  have hUopen : IsOpen (Metric.ball s r) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, abelTerm a n w)
      (Metric.ball s r) := by
    refine differentiableOn_tsum_of_summable_norm hu
      (fun n => (differentiable_abelTerm a n).differentiableOn) hUopen ?_
    intro n w hw
    have hdist : ‖w - s‖ < r := by simpa [Complex.dist_eq] using hw
    have hre : δ ≤ w.re := by
      have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      have h2 : |(w - s).re| < r := lt_of_le_of_lt h1 hdist
      have h3 : -(r : ℝ) < (w - s).re := (abs_lt.mp h2).1
      simp only [Complex.sub_re] at h3
      rw [hrdef] at h3
      linarith
    have hnorm : ‖w‖ ≤ ‖s‖ + r := by
      have : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by simpa using norm_add_le (w - s) s
      linarith
    exact hbound n w hre hnorm
  have hmem : s ∈ Metric.ball s r := Metric.mem_ball_self hr0
  exact ((hdiff.differentiableAt (hUopen.mem_nhds hmem)).differentiableWithinAt)

/-! ## Summation by parts -/

/-- Summation by parts: `∑_{n ≤ N} a(n) n^{-s} = ∑_{n ≤ N} A(n)(n^{-s} - (n+1)^{-s})
+ A(N) (N+1)^{-s}`. -/
lemma sum_mul_cpow_eq (a : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)
      = (∑ n ∈ Finset.range (N + 1), abelTerm a n s)
        + partialSum a N * ((N : ℂ) + 1) ^ (-s) := by
  induction N with
  | zero => simp [abelTerm]
  | succ N ih =>
      have hR : ∑ n ∈ Finset.range (N + 1 + 1), abelTerm a n s
          = (∑ n ∈ Finset.range (N + 1), abelTerm a n s) + abelTerm a (N + 1) s :=
        Finset.sum_range_succ _ _
      have hterm : abelTerm a (N + 1) s =
          partialSum a (N + 1) * (((N : ℂ) + 1) ^ (-s) - ((N : ℂ) + 1 + 1) ^ (-s)) := by
        simp only [abelTerm]
        push_cast
        ring_nf
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, hR, hterm, partialSum_succ]
      push_cast
      ring

/-- A sum over `range (N+1)` of a sequence vanishing at `0` is a sum over `Icc 1 N`. -/
lemma sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] {g : ℕ → M} (hg : g 0 = 0)
    (N : ℕ) : ∑ n ∈ Finset.range (N + 1), g n = ∑ n ∈ Finset.Icc 1 N, g n := by
  induction N with
  | zero => simp [hg]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The boundary term `A(N) (N+1)^{-s}` of the summation by parts tends to zero on
`re s > θ`. -/
lemma tendsto_partialSum_mul_cpow {a : ℕ → ℂ} {θ : ℝ} (ha : PartialSumBound a θ) {s : ℂ}
    (hs : θ < s.re) :
    Tendsto (fun N : ℕ => partialSum a N * ((N : ℂ) + 1) ^ (-s)) atTop (nhds 0) := by
  set eps : ℝ := (s.re - θ) / 2 with heps
  have heps0 : 0 < eps := by rw [heps]; linarith
  obtain ⟨C, hC0, hC⟩ := ha.exists_nonneg heps0
  set b : ℝ := θ + eps - s.re with hb
  have hb0 : b < 0 := by rw [hb, heps]; linarith
  set K : ℝ := max 1 (2 ^ (-s.re)) with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hbound : ∀ N : ℕ, ‖partialSum a N * ((N : ℂ) + 1) ^ (-s)‖ ≤ C * K * (N : ℝ) ^ b := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [partialSum, Real.zero_rpow (ne_of_lt hb0)]
    · have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      have hnorm : ‖((N : ℂ) + 1) ^ (-s)‖ = ((N : ℝ) + 1) ^ (-s.re) := by
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN1, Complex.neg_re]
      have hpow : ((N : ℝ) + 1) ^ (-s.re) ≤ K * (N : ℝ) ^ (-s.re) := by
        rcases le_or_gt (-s.re) 0 with h | h
        · have h1 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
            Real.rpow_le_rpow_of_nonpos hN0 (by linarith) h
          have h2 : (N : ℝ) ^ (-s.re) ≤ K * (N : ℝ) ^ (-s.re) := by
            nlinarith [Real.rpow_nonneg hN0.le (-s.re)]
          linarith
        · have h2 : ((N : ℝ) + 1) ≤ 2 * (N : ℝ) := by linarith
          calc ((N : ℝ) + 1) ^ (-s.re)
              ≤ (2 * (N : ℝ)) ^ (-s.re) := Real.rpow_le_rpow (by positivity) h2 h.le
            _ = 2 ^ (-s.re) * (N : ℝ) ^ (-s.re) := Real.mul_rpow (by norm_num) hN0.le
            _ ≤ K * (N : ℝ) ^ (-s.re) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      calc ‖partialSum a N * ((N : ℂ) + 1) ^ (-s)‖
          = ‖partialSum a N‖ * ((N : ℝ) + 1) ^ (-s.re) := by rw [norm_mul, hnorm]
        _ ≤ (C * (N : ℝ) ^ (θ + eps)) * (K * (N : ℝ) ^ (-s.re)) :=
            mul_le_mul (hC N) hpow (by positivity) (by positivity)
        _ = C * K * (N : ℝ) ^ b := by
            rw [show C * (N : ℝ) ^ (θ + eps) * (K * (N : ℝ) ^ (-s.re))
              = C * K * ((N : ℝ) ^ (θ + eps) * (N : ℝ) ^ (-s.re)) by ring,
              ← Real.rpow_add hN0, hb]
            ring_nf
  have htend : Tendsto (fun N : ℕ => C * K * (N : ℝ) ^ b) atTop (nhds 0) := by
    have h2 : Tendsto (fun x : ℝ => x ^ b) atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (y := -b) (by linarith)
      simpa using this
    simpa using (h2.comp tendsto_natCast_atTop_atTop).const_mul (C * K)
  exact squeeze_zero_norm hbound htend

/-- **The Abel-summed series computes the L-series** wherever the latter converges (in
particular on `re s > 1`). -/
lemma abelSum_eq_LSeries {a : ℕ → ℂ} {θ : ℝ} (hθ : -1 ≤ θ) (ha : PartialSumBound a θ) {s : ℂ}
    (hs : θ < s.re) (hL : LSeriesSummable a s) : abelSum a s = LSeries a s := by
  have hsum := summable_abelTerm hθ ha hs
  have hA : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), abelTerm a n s)
      atTop (nhds (abelSum a s)) :=
    (hsum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hLt : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s))
      atTop (nhds (LSeries a s)) := by
    have h' := (hL.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
    refine h'.congr ?_
    intro N
    have hterm0 : LSeries.term a s 0 = 0 := by simp [LSeries.term]
    rw [Function.comp_apply, sum_range_succ_eq_sum_Icc hterm0 N]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn0 : n ≠ 0 := by
      have := Finset.mem_Icc.mp hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  have hkey : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), abelTerm a n s)
        + partialSum a N * ((N : ℂ) + 1) ^ (-s)) atTop (nhds (LSeries a s)) :=
    hLt.congr (fun N => sum_mul_cpow_eq a s N)
  have hcomb := hA.add (tendsto_partialSum_mul_cpow ha hs)
  rw [add_zero] at hcomb
  exact tendsto_nhds_unique hcomb hkey

/-! ## Specialization to square-root cancellation -/

lemma differentiableOn_abelSum_of_sqrtCancellation {a : ℕ → ℂ} (ha : SqrtCancellation a) :
    DifferentiableOn ℂ (abelSum a) {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_abelSum (by norm_num) ha

lemma abelSum_eq_LSeries_of_sqrtCancellation {a : ℕ → ℂ} (ha : SqrtCancellation a) {s : ℂ}
    (hs : 1 / 2 < s.re) (hL : LSeriesSummable a s) : abelSum a s = LSeries a s :=
  abelSum_eq_LSeries (by norm_num) ha hs hL

end RiemannHypothesis

end
