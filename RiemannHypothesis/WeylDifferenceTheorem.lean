/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCriterion

/-!
# van der Corput's difference theorem

`RiemannHypothesis.WeylDifferencing` proves the A process — the van der Corput inequality

`H ‖∑_{n<N} e(f n)‖² ≤ (N + H − 1)(N + 2 ∑_{0<k<H} ‖∑_{n<N−k} e(f(n+k) − f(n))‖)` —

as an inequality about an arbitrary sequence.  This file draws from it the qualitative
consequence known as **van der Corput's difference theorem**: a sequence is equidistributed
modulo one as soon as *every* difference sequence `n ↦ x(n+k) − x(n)`, `k ≥ 1`, is.

The point of the theorem is that it lowers the degree of a problem: the differences of a
polynomial sequence form a polynomial sequence of one degree less, which is how
`RiemannHypothesis.WeylPolynomial` obtains Weyl's theorem for an arbitrary polynomial.

## Main results

* `mul_normSq_weylSum_le` — the A process rewritten for `ℕ`-indexed sequences:
  `H ‖∑_{n<N} e(m x n)‖² ≤ (N + H − 1)(N + 2 ∑_{k=1}^{H−1} ‖∑_{n<N−k} e(m (x(n+k) − x n))‖)`.
* `weylSumsVanish_of_diff` — if every difference sequence has vanishing Weyl sums, so does `x`.
* `equidistributedMod1_of_diff` — **van der Corput's difference theorem**: if every difference
  sequence is equidistributed modulo one, so is `x`.

## Proof

Fix a frequency `m ≠ 0` and an `ε > 0`, and pick `H > 4/ε²`.  In the A process, each of the
`H − 1` differenced sums is `o(N)` by hypothesis, so for `N` large the right-hand side is at
most `2N · (N + N/2) ≤ 3N²`, giving `‖∑_{n<N} e(m x n)‖² ≤ 3N²/H < ε² N²`.  Since `H` is
arbitrary, the Weyl sums of `x` vanish, and Weyl's criterion converts that into
equidistribution.
-/

noncomputable section

open Complex Filter Finset Topology

namespace RiemannHypothesis

namespace WeylDifference

open KusminLandau WeylQuadratic WeylCriterion

/-- The Weyl sum `∑_{0 ≤ n < N} e(m · x n)` of the sequence `x` at frequency `m`. -/
def weylSum (x : ℕ → ℝ) (m : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, e2pi (m * x n)

/-- The `k`-th difference sequence `n ↦ x (n + k) − x n`. -/
def diffSeq (x : ℕ → ℝ) (k : ℕ) : ℕ → ℝ := fun n => x (n + k) - x n

/-- A sum over the integer interval `(0, H)` is a sum over `Finset.Ico 1 H`. -/
theorem sum_Ioo_int_eq_sum_Ico (H : ℕ) (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), g k = ∑ j ∈ Finset.Ico 1 H, g (j : ℤ) := by
  refine Finset.sum_nbij' (fun n => n.toNat) (fun j => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ioo] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro j hj
    rw [Finset.mem_Ico] at hj
    simp only [Finset.mem_Ioo]
    omega
  · intro a ha
    rw [Finset.mem_Ioo] at ha
    omega
  · intro j _
    omega
  · intro a ha
    rw [Finset.mem_Ioo] at ha
    congr 1
    omega

/-- **The A process for a `ℕ`-indexed sequence.**  For every `H ≥ 1`,

`H ‖∑_{n<N} e(m x n)‖² ≤ (N + H − 1)(N + 2 ∑_{k=1}^{H−1} ‖∑_{n<N−k} e(m (x(n+k) − x n))‖)`. -/
theorem mul_normSq_weylSum_le (x : ℕ → ℝ) (m : ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖weylSum x m N‖ ^ 2
      ≤ ((N : ℝ) + H - 1)
        * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖weylSum (diffSeq x k) m (N - k)‖) := by
  have hA := WeylDifferencing.norm_sq_sum_e2pi_le (fun n : ℤ => m * x n.toNat) N H hH
  have houter : ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (m * x n.toNat) = weylSum x m N := by
    rw [WeylQuadratic.sum_Ico_int_eq_sum_range]
    simp [weylSum]
  have hinner : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (m * x (n + k).toNat - m * x n.toNat)‖
        = ‖weylSum (diffSeq x k.toNat) m (N - k.toNat)‖ := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [WeylQuadratic.sum_Ico_int_eq_sum_range]
    congr 1
    have hNk : ((N : ℤ) - k).toNat = N - k.toNat := by omega
    rw [hNk, weylSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (((j : ℤ) + k).toNat) = j + k.toNat := by omega
    have h2 : ((j : ℤ)).toNat = j := by omega
    rw [h1, h2]
    congr 1
    simp only [diffSeq]
    ring
  rw [houter, Finset.sum_congr rfl hinner,
    sum_Ioo_int_eq_sum_Ico H (fun k => ‖weylSum (diffSeq x k.toNat) m (N - k.toNat)‖)] at hA
  simpa using hA

/-- If every difference sequence has vanishing Weyl sums, then so does `x`. -/
theorem weylSumsVanish_of_diff {x : ℕ → ℝ}
    (h : ∀ k : ℕ, 0 < k → WeylSumsVanish (diffSeq x k)) : WeylSumsVanish x := by
  intro m hm
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hHgt⟩ := exists_nat_gt (4 / ε ^ 2)
  have hHpos : (0 : ℝ) < H := lt_of_le_of_lt (by positivity) hHgt
  have hHnat : 0 < H := by exact_mod_cast hHpos
  -- each difference sequence is `o(N)`, uniformly beyond a threshold `Mk k`
  have hstep : ∀ k : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N → 0 < k →
      ‖weylSum (diffSeq x k) (m : ℝ) N‖ ≤ (N : ℝ) / (4 * H) := by
    intro k
    by_cases hk : 0 < k
    · have hlim := h k hk m hm
      rw [Metric.tendsto_atTop] at hlim
      obtain ⟨M, hM⟩ := hlim (1 / (4 * H)) (by positivity)
      refine ⟨max M 1, fun N hN _ => ?_⟩
      have hNM : M ≤ N := le_trans (le_max_left _ _) hN
      have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hMN := hM N hNM
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos] at hMN
      have heq : 1 / (4 * (H : ℝ)) * N = (N : ℝ) / (4 * H) := by ring
      have hlt : ‖weylSum (diffSeq x k) (m : ℝ) N‖ < (N : ℝ) / (4 * H) := by
        rw [← heq]; exact hMN
      exact hlt.le
    · exact ⟨0, fun N _ hk' => absurd hk' hk⟩
  choose Mk hMk using hstep
  set M : ℕ := (Finset.range H).sup Mk with hMdef
  refine ⟨M + H + 1, fun N hN => ?_⟩
  have hNH : H ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hHleN : (H : ℝ) ≤ N := by exact_mod_cast hNH
  -- the differenced sums are all small
  have hsum : ∑ k ∈ Finset.Ico 1 H, ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖ ≤ (N : ℝ) / 4 := by
    have hterm : ∀ k ∈ Finset.Ico 1 H,
        ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖ ≤ (N : ℝ) / (4 * H) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hMkM : Mk k ≤ M := Finset.le_sup (f := Mk) (Finset.mem_range.2 hk.2)
      have hle : Mk k ≤ N - k := by omega
      refine (hMk k (N - k) hle hk.1).trans ?_
      have : ((N - k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N k
      gcongr
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
      have : (H - 1 : ℕ) ≤ H := Nat.sub_le _ _
      exact_mod_cast this
    have hquot : (0 : ℝ) ≤ (N : ℝ) / (4 * H) := by positivity
    calc ((H - 1 : ℕ) : ℝ) * ((N : ℝ) / (4 * H)) ≤ (H : ℝ) * ((N : ℝ) / (4 * H)) := by
          exact mul_le_mul_of_nonneg_right hcard hquot
      _ = (N : ℝ) / 4 := by field_simp
  -- feed this into the A process
  have hkey := mul_normSq_weylSum_le x (m : ℝ) N H hHnat
  have hrhs : ((N : ℝ) + H - 1)
      * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖)
      ≤ 3 * (N : ℝ) ^ 2 := by
    have h1 : (N : ℝ) + H - 1 ≤ 2 * N := by linarith
    have h2 : (N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
        ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖ ≤ 3 * (N : ℝ) / 2 := by linarith
    have h3 : (0 : ℝ) ≤ (N : ℝ) + H - 1 := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
      linarith
    have h4 : (0 : ℝ) ≤ (N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
        ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖ := by
      have : (0 : ℝ) ≤ ∑ k ∈ Finset.Ico 1 H, ‖weylSum (diffSeq x k) (m : ℝ) (N - k)‖ :=
        Finset.sum_nonneg fun k _ => norm_nonneg _
      linarith
    nlinarith
  have hsq : (H : ℝ) * ‖weylSum x (m : ℝ) N‖ ^ 2 ≤ 3 * (N : ℝ) ^ 2 := hkey.trans hrhs
  have hlt : 3 * (N : ℝ) ^ 2 < ε ^ 2 * (N : ℝ) ^ 2 * H := by
    have h4 : 4 < ε ^ 2 * H := by
      have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).1 hHgt
      nlinarith [h]
    nlinarith [sq_nonneg ((N : ℝ))]
  have hfinal : ‖weylSum x (m : ℝ) N‖ ^ 2 < (ε * N) ^ 2 := by
    have : (H : ℝ) * ‖weylSum x (m : ℝ) N‖ ^ 2 < (ε * N) ^ 2 * H := by nlinarith
    have hH' : (0 : ℝ) < H := hHpos
    nlinarith
  have hnorm : ‖weylSum x (m : ℝ) N‖ < ε * N := by
    nlinarith [norm_nonneg (weylSum x (m : ℝ) N), mul_pos hε hNpos]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hrw : (∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)) = weylSum x (m : ℝ) N := rfl
  rw [hrw, div_lt_iff₀ hNpos]
  linarith

/-- **van der Corput's difference theorem.**  If every difference sequence `n ↦ x(n+k) − x n`,
`k ≥ 1`, is equidistributed modulo one, then so is `x`. -/
theorem equidistributedMod1_of_diff {x : ℕ → ℝ}
    (h : ∀ k : ℕ, 0 < k → EquidistributedMod1 (diffSeq x k)) : EquidistributedMod1 x :=
  equidistributedMod1_of_weylSumsVanish
    (weylSumsVanish_of_diff fun k hk => weylSumsVanish_of_equidistributedMod1 (h k hk))

end WeylDifference

end RiemannHypothesis
