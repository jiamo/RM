/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MertensSums
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The Redheffer matrix: a linear-algebra criterion for the Riemann hypothesis

The **Redheffer matrix** `A n` is the `n × n` matrix of zeroes and ones whose `(i, j)` entry
(indices running over `1, …, n`) is `1` when `j = 1` or when `i ∣ j`, and `0` otherwise.
Redheffer's theorem is the determinant evaluation

`det (A n) = M(n) = ∑_{k ≤ n} μ(k)`,

the Mertens function.  Combined with the Mertens criterion of
`RiemannHypothesis.MoebiusCriterion` it turns the Riemann hypothesis into a statement of
linear algebra: if the determinants of the Redheffer matrices satisfy
`|det (A n)| = O(n^{1/2+ε})` for every `ε > 0`, then the Riemann hypothesis holds.

## Main results

* `sum_mertens_div` : `∑_{d = 1}^{m} M(⌊m/d⌋) = 1` for `m ≥ 1`, the Möbius-inversion identity
  behind the determinant evaluation (from the hyperbola reindexing of
  `RiemannHypothesis.MertensSums`).
* `redheffer_eq_divisorMatrix_mul_mertensColumn` : the factorisation `A = B · C` of the
  Redheffer matrix into the (unit upper triangular) divisibility matrix `B` and the
  (lower triangular) matrix `C` whose first column is `d ↦ M(⌊n/d⌋)`.
* `det_redheffer` : **Redheffer's theorem**, `det (A n) = M(n)` for `n ≥ 1`.
* `zeta_of_redhefferBound` : `RedhefferBoundForm → ZetaForm`; a square-root bound for the
  Redheffer determinants implies the Riemann hypothesis.

## Indexing convention

Lean's matrices here are indexed by `Fin n`, and the index `i : Fin n` stands for the integer
`i + 1`, so that `i = 0` is the first row/column.
-/

noncomputable section

open Complex Filter Finset ArithmeticFunction

namespace RiemannHypothesis

/-- **The key identity**: `∑_{d = 1}^{m} M(⌊m/d⌋) = 1` for every `m ≥ 1`. -/
theorem sum_mertens_div {m : ℕ} (hm : 1 ≤ m) : ∑ d ∈ Icc 1 m, mertens (m / d) = 1 := by
  have h : ∑ d ∈ Icc 1 m, mertens (m / d) = ∑ k ∈ Icc 1 m, ∑ e ∈ k.divisors, moebius e := by
    simpa only [mertens] using sum_pairs_inner m moebius
  rw [h, sum_Icc_sum_divisors_moebius hm]

/-! ### The Redheffer matrix and its factorisation -/

/-- The **Redheffer matrix** of size `n`: the entry in row `i` and column `j` (standing for the
integers `i + 1` and `j + 1`) is `1` if the column is the first one or if `i + 1` divides
`j + 1`, and `0` otherwise. -/
def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The divisibility matrix: `1` in position `(i, j)` exactly when `i + 1` divides `j + 1`.
It is unit upper triangular, so its determinant is `1`. -/
def divisorMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The matrix that agrees with the identity outside its first column, whose first column is
`i ↦ M(⌊n / (i + 1)⌋)`.  It is lower triangular with diagonal `(M(n), 1, …, 1)`. -/
def mertensColumn (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if (j : ℕ) = 0 then mertens (n / ((i : ℕ) + 1)) else if i = j then 1 else 0

lemma divisorMatrix_isUpperTriangular (n : ℕ) : (divisorMatrix n).BlockTriangular id := by
  intro i j hji
  have : ¬ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    have : (j : ℕ) < (i : ℕ) := hji
    omega
  simp [divisorMatrix, this]

lemma det_divisorMatrix (n : ℕ) : (divisorMatrix n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (divisorMatrix_isUpperTriangular n)]
  simp [divisorMatrix]

lemma mertensColumn_isLowerTriangular (n : ℕ) :
    (mertensColumn n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hj : (j : ℕ) ≠ 0 := by
    have : (i : ℕ) < (j : ℕ) := hij
    omega
  have hne : i ≠ j := ne_of_lt hij
  simp [mertensColumn, hj, hne]

lemma det_mertensColumn {n : ℕ} (hn : 1 ≤ n) : (mertensColumn n).det = mertens n := by
  rw [Matrix.det_of_lowerTriangular _ (mertensColumn_isLowerTriangular n)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
  have hrest : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩,
      mertensColumn n i i = 1 := by
    intro i hi
    have hi0 : (i : ℕ) ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hi).1 (Fin.ext h)
    simp [mertensColumn, hi0]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const_one, one_mul]
  simp [mertensColumn]

/-- The sum of `M(⌊n / (k+1)⌋)` over the rows `k` divisible-by-`i+1` (in the shifted indexing)
is `1`: this is `sum_mertens_div` after the substitution `k + 1 = (i + 1) * d`. -/
lemma sum_mertens_div_multiples {n : ℕ} (i : Fin n) :
    ∑ k : Fin n, (if ((i : ℕ) + 1) ∣ ((k : ℕ) + 1) then mertens (n / ((k : ℕ) + 1)) else 0)
      = 1 := by
  set a := (i : ℕ) + 1 with ha
  have han : a ≤ n := by have := i.isLt; omega
  have ha0 : 0 < a := by omega
  have hstep :
      ∑ k : Fin n, (if a ∣ ((k : ℕ) + 1) then mertens (n / ((k : ℕ) + 1)) else 0)
        = ∑ K ∈ Icc 1 n, (if a ∣ K then mertens (n / K) else 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => if a ∣ (k + 1) then mertens (n / (k + 1)) else 0) n,
      show Icc 1 n = Finset.Ico 1 (n + 1) by ext; simp, Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  rw [hstep]
  have hbij : ∑ K ∈ Icc 1 n, (if a ∣ K then mertens (n / K) else 0)
      = ∑ d ∈ Icc 1 (n / a), mertens ((n / a) / d) := by
    rw [Finset.sum_filter (s := Icc 1 n) (p := fun K => a ∣ K) (f := fun K => mertens (n / K))
      |>.symm]
    refine Finset.sum_nbij' (i := fun K => K / a) (j := fun d => a * d) ?_ ?_ ?_ ?_ ?_
    · intro K hK
      simp only [Finset.mem_filter, Finset.mem_Icc] at hK
      obtain ⟨⟨hK1, hKn⟩, hdvd⟩ := hK
      simp only [Finset.mem_Icc]
      exact ⟨(Nat.one_le_div_iff ha0).mpr (Nat.le_of_dvd (by omega) hdvd),
        Nat.div_le_div_right hKn⟩
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith, ?_⟩, ⟨d, rfl⟩⟩
      calc a * d ≤ a * (n / a) := Nat.mul_le_mul_left a hd.2
        _ ≤ n := Nat.mul_div_le n a
    · intro K hK
      simp only [Finset.mem_filter] at hK
      exact Nat.mul_div_cancel' hK.2
    · intro d _
      exact Nat.mul_div_cancel_left d ha0
    · intro K hK
      simp only [Finset.mem_filter] at hK
      rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hK.2]
  rw [hbij]
  exact sum_mertens_div ((Nat.one_le_div_iff ha0).mpr han)

/-- The factorisation `A = B · C` of the Redheffer matrix. -/
theorem redheffer_eq_divisorMatrix_mul_mertensColumn (n : ℕ) :
    redheffer n = divisorMatrix n * mertensColumn n := by
  ext i j
  by_cases hj : (j : ℕ) = 0
  · have : redheffer n i j = 1 := by simp [redheffer, hj]
    rw [this]
    rw [Matrix.mul_apply]
    have : ∀ k : Fin n, divisorMatrix n i k * mertensColumn n k j
        = if ((i : ℕ) + 1) ∣ ((k : ℕ) + 1) then mertens (n / ((k : ℕ) + 1)) else 0 := by
      intro k
      by_cases h : ((i : ℕ) + 1) ∣ ((k : ℕ) + 1) <;>
        simp [divisorMatrix, mertensColumn, hj, h]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    exact (sum_mertens_div_multiples i).symm
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · by_cases h : ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) <;>
        simp [redheffer, divisorMatrix, mertensColumn, hj, h]
    · intro k _ hkj
      simp [mertensColumn, hj, hkj]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- **Redheffer's theorem**: the determinant of the `n × n` Redheffer matrix is the Mertens
function `M(n) = ∑_{k ≤ n} μ(k)`. -/
theorem det_redheffer {n : ℕ} (hn : 1 ≤ n) : (redheffer n).det = mertens n := by
  rw [redheffer_eq_divisorMatrix_mul_mertensColumn, Matrix.det_mul, det_divisorMatrix,
    det_mertensColumn hn, one_mul]

/-! ### The criterion -/

/-- **The Redheffer form of the Riemann hypothesis**: the determinants of the Redheffer
matrices satisfy `|det (A n)| = O(n^{1/2+ε})` for every `ε > 0`. -/
def RedhefferBoundForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |((redheffer n).det : ℝ)| ≤ C * (n : ℝ) ^ (1 / 2 + ε)

/-- The Redheffer bound is the Mertens bound. -/
theorem mertensBound_of_redhefferBound (h : RedhefferBoundForm) : MertensBoundForm := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hz : ((0 : ℕ) : ℝ) ^ (1 / 2 + ε) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by linarith)
    rw [hz, mul_zero]
    simp [mertens]
  · have := hC N hN
    rwa [det_redheffer hN] at this

/-- A square-root bound for the Redheffer determinants implies the Riemann hypothesis. -/
theorem zeta_of_redhefferBound (h : RedhefferBoundForm) : ZetaForm :=
  zeta_of_mertensBound (mertensBound_of_redhefferBound h)

end RiemannHypothesis
