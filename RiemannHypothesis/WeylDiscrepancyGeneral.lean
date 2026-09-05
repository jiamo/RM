/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDiscrepancyQuadratic
import RiemannHypothesis.WeylCountGeneral

/-!
# The discrepancy bound for an arbitrary subinterval

`RiemannHypothesis.WeylDiscrepancy` proves an inequality of Erdős–Turán type,

    |#{n < N : Int.fract (x n) ∈ [a, b)}/N − (b − a)| ≤ 4/K + 2 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N ,

but only for intervals satisfying `1/K < a`, `b + 1/K < 1` and `a + 2/K ≤ b`: intervals shorter
than `2/K`, and intervals touching the point where `[0, 1)` is glued into the circle, are not
covered at that value of `K`.  That restriction is the open boundary recorded for
`M1-WEYL-DISCREPANCY`.  This module removes it: the bound is proved for **every** interval
`[a, b) ⊆ [0, 1]`, at the cost of the constant `4` becoming `20`.  The statement is therefore a
genuine bound for the discrepancy

    D_N(x) = sup_{0 ≤ a ≤ b ≤ 1} |#{n < N : Int.fract (x n) ∈ [a, b)}/N − (b − a)| ,

which the restricted form is not: a discrepancy is a supremum over *all* subintervals, and the
short ones are exactly the ones a supremum is attained on.

## Method

Three devices, all elementary, and each one removes one of the three restrictions.

* *Rotation* removes `1/K < a` and `b + 1/K < 1`.  Translating the sequence by a constant `c`
  multiplies the exponential sum at frequency `m` by the unimodular factor `e(mc)`
  (`norm_expSum_add_const`), so the right-hand side of the inequality is invariant, while the
  counting function is unchanged by the matched translation of the interval
  (`WeylCount.countIn_add_const`).  Choosing `c` so that `[a + c, b + c)` is centred in `(0, 1)`
  gives `abs_countIn_div_sub_le_pow_shift` for every interval of length between `2/K` and
  `1 − 4/K`.
* *Enlargement* removes `a + 2/K ≤ b` in the upper bound: a short interval is contained in one of
  length `2/K` inside `[0, 1]`, and the count only increases (`countIn_div_le_of_le`).  In the
  lower bound a short interval needs no argument at all, the count being nonnegative and the
  length at most `2/K`.
* *Complementation* covers the intervals so long that they cannot be enlarged: for `b − a` close
  to `1` the identity `#[0,a) + #[a,b) + #[b,1) = N` (`countIn_split_unit`) turns the lower bound
  for `[a, b)` into upper bounds for the two short intervals `[0, a)` and `[b, 1)`.

## Main results

* `abs_countIn_div_sub_le_pow_of_le` — **the discrepancy bound for every subinterval**: for
  `K ≥ 8`, `N ≥ 1` and `0 ≤ a ≤ b ≤ 1`,

      |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N .

* `abs_countIn_div_sub_le_linear_of_le` — for a badly approximable `α` the discrepancy of `α n`
  over *all* intervals is at most `(20 + 2/c)/K` as soon as `K⁹ ≤ N`; that is, `O(N^(−1/9))`.
* `abs_countIn_div_sub_le_quadratic_of_le` — the same for `α n²` with `2α` badly approximable,
  and `abs_countIn_div_sub_le_sqrt_two_of_le` for the concrete `α = √2/2`.

## Scope

The weight of the `m`-th exponential sum is still `1` rather than the `1/m` of the sharp
Erdős–Turán inequality, so the exponents inherited from `RiemannHypothesis.WeylDiscrepancy` are
unchanged; only the class of intervals is widened, and the constants are not optimized.  Nothing
here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount

/-! ### Translation invariance of the exponential sums -/

/-- Translating the sequence by a constant multiplies the exponential sum by a unimodular
factor, so its norm is unchanged. -/
theorem norm_expSum_add_const (x : ℕ → ℝ) (c : ℝ) (m : ℤ) (N : ℕ) :
    ‖expSum (fun n => x n + c) m N‖ = ‖expSum x m N‖ := by
  have hfac : expSum (fun n => x n + c) m N
      = e2pi ((m : ℝ) * c) * expSum x m N := by
    unfold expSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← e2pi_add]
    ring_nf
  rw [hfac, norm_mul, norm_e2pi, one_mul]

/-- The right-hand side of the discrepancy inequality is invariant under translation. -/
theorem sum_norm_expSum_add_const (x : ℕ → ℝ) (c : ℝ) (K N : ℕ) :
    ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum (fun n => x n + c) (m : ℤ) N‖ / N
      = ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N :=
  Finset.sum_congr rfl fun m _ => by rw [norm_expSum_add_const]

/-- The sum of exponential-sum averages is nonnegative. -/
theorem sum_norm_expSum_div_nonneg (x : ℕ → ℝ) (K N : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N :=
  Finset.sum_nonneg fun m _ => by positivity

/-! ### Elementary properties of the counting function -/

/-- Widening the interval increases the count. -/
theorem countIn_mono (x : ℕ → ℝ) {a a' b b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') (N : ℕ) :
    countIn x a b N ≤ countIn x a' b' N := by
  classical
  unfold countIn
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, le_trans ha hn.2.1, lt_of_lt_of_le hn.2.2 hb⟩

/-- At most `N` terms are counted. -/
theorem countIn_le (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : countIn x a b N ≤ N := by
  classical
  unfold countIn
  calc ((Finset.range N).filter fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card
      ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

/-- Adjacent intervals: the counts add. -/
theorem countIn_add_countIn (x : ℕ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (N : ℕ) :
    countIn x a b N + countIn x b c N = countIn x a c N := by
  classical
  unfold countIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨hn, h1, h2⟩ | ⟨hn, h1, h2⟩)
      · exact ⟨hn, h1, by linarith⟩
      · exact ⟨hn, by linarith, h2⟩
    · rintro ⟨hn, h1, h2⟩
      rcases lt_or_ge (Int.fract (x n)) b with h | h
      · exact Or.inl ⟨hn, h1, h⟩
      · exact Or.inr ⟨hn, h, h2⟩
  · refine Finset.disjoint_left.2 fun n hn hn' => ?_
    simp only [Finset.mem_filter] at hn hn'
    exact absurd hn'.2.1 (not_le.2 hn.2.2)

/-- Splitting `[0, 1)` at two points: the three counts add up to `N`. -/
theorem countIn_split_unit (x : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (N : ℕ) :
    countIn x 0 a N + countIn x a b N + countIn x b 1 N = N := by
  rw [countIn_add_countIn x ha hab N, countIn_add_countIn x (le_trans ha hab) hb N,
    countIn_zero_one]

/-! ### The bound for an interval of intermediate length, anywhere in `[0, 1]` -/

/-- **Rotation.**  The discrepancy bound of `abs_countIn_div_sub_le_pow` holds for every
interval `[a, b) ⊆ [0, 1]` whose length lies between `2/K` and `1 − 4/K`, with no condition on
its position: the interval is rotated into the middle of `(0, 1)`, which changes neither the
count nor the exponential sums. -/
theorem abs_countIn_div_sub_le_pow_shift (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K)
    (hN : 0 < N) (ha : 0 ≤ a) (hb : b ≤ 1) (hlen : 2 / (K : ℝ) ≤ b - a)
    (hlen' : b - a ≤ 1 - 4 / (K : ℝ)) :
    |(countIn x a b N : ℝ) / N - (b - a)|
      ≤ 4 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hK0 : 0 < K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  set c : ℝ := (1 - (b - a)) / 2 - a with hc
  have hac : 1 / (K : ℝ) < a + c := by
    have h4 : (4 : ℝ) / K ≤ 1 - (b - a) := by linarith
    have h2 : (2 : ℝ) / K ≤ (1 - (b - a)) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have : (4 : ℝ) / K = 2 / K * 2 := by ring
      linarith [this ▸ h4]
    have h1 : 1 / (K : ℝ) < 2 / K := by
      rw [div_lt_div_iff_of_pos_right hKpos]
      norm_num
    have : a + c = (1 - (b - a)) / 2 := by rw [hc]; ring
    rw [this]
    linarith
  have hbc : b + c + 1 / (K : ℝ) < 1 := by
    have hsum : (a + c) + (b + c) = 1 := by rw [hc]; ring
    have h1 : (0 : ℝ) < 1 / K := by positivity
    linarith [hac]
  have hab' : (a + c) + 2 / (K : ℝ) ≤ b + c := by linarith
  have hac0 : (0 : ℝ) < a + c := lt_trans (by positivity) hac
  have hbc0 : b + c < 1 := by
    have : (0 : ℝ) < 1 / K := by positivity
    linarith
  have hcount := countIn_add_const x ha hb hac0 hbc0 N
  have hmain := abs_countIn_div_sub_le_pow (fun n => x n + c) hK hN hac hbc hab'
  rw [sum_norm_expSum_add_const] at hmain
  have hlength : b + c - (a + c) = b - a := by ring
  rw [hlength] at hmain
  rwa [← hcount] at hmain

/-! ### The upper bound for every interval -/

/-- **Enlargement.**  An upper bound for the count of an arbitrary interval `[a, b) ⊆ [0, 1]`:
short intervals are enlarged to length `2/K` inside `[0, 1]`, and intervals of length close to
`1` are handled by the trivial bound `#[a, b) ≤ N`. -/
theorem countIn_div_le_of_le (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (countIn x a b N : ℝ) / N
      ≤ (b - a) + 10 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hK0 : 0 < K := by omega
  have hK2 : 2 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK8 : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hSnn := sum_norm_expSum_div_nonneg x K N
  have h2K : (2 : ℝ) / K ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    linarith
  have h6K : (6 : ℝ) / K ≤ 3 / 4 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    linarith
  have hd2 : (2 : ℝ) / K = 2 * (1 / K) := by ring
  have hd4 : (4 : ℝ) / K = 4 * (1 / K) := by ring
  have hd6 : (6 : ℝ) / K = 6 * (1 / K) := by ring
  have hd10 : (10 : ℝ) / K = 10 * (1 / K) := by ring
  rcases le_or_gt (b - a) (1 - 6 / (K : ℝ)) with hshort | hlong
  · set a' : ℝ := min a (1 - 2 / (K : ℝ)) with ha'
    set b' : ℝ := max b (a' + 2 / (K : ℝ)) with hb'
    have ha'a : a' ≤ a := min_le_left _ _
    have ha'1 : a' ≤ 1 - 2 / (K : ℝ) := min_le_right _ _
    have ha'0 : 0 ≤ a' := by
      rw [ha']
      exact le_min ha (by linarith)
    have hbb' : b ≤ b' := le_max_left _ _
    have hb'1 : b' ≤ 1 := max_le hb (by linarith)
    have hlen : 2 / (K : ℝ) ≤ b' - a' := by
      have : a' + 2 / (K : ℝ) ≤ b' := le_max_right _ _
      linarith
    have ha'ge : a - 2 / (K : ℝ) ≤ a' := by
      rw [ha']
      rcases le_total a (1 - 2 / (K : ℝ)) with h | h
      · rw [min_eq_left h]; linarith [show (0:ℝ) < 2 / K by positivity]
      · rw [min_eq_right h]; linarith
    have hlen' : b' - a' ≤ 1 - 4 / (K : ℝ) := by
      rcases max_cases b (a' + 2 / (K : ℝ)) with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [hb', heq]
        linarith
      · rw [hb', heq]
        linarith
    have hmono : countIn x a b N ≤ countIn x a' b' N := countIn_mono x ha'a hbb' N
    have hmonoR : (countIn x a b N : ℝ) / N ≤ (countIn x a' b' N : ℝ) / N := by
      have h : (countIn x a b N : ℝ) ≤ (countIn x a' b' N : ℝ) := by exact_mod_cast hmono
      gcongr
    have hshiftbound := abs_countIn_div_sub_le_pow_shift x hK2 hN ha'0 hb'1 hlen hlen'
    have hupper : (countIn x a' b' N : ℝ) / N
        ≤ (b' - a') + (4 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
            ‖expSum x (m : ℤ) N‖ / N) := by
      have := (abs_le.mp hshiftbound).2
      linarith
    have hb'a' : b' - a' ≤ (b - a) + 4 / (K : ℝ) := by
      rcases max_cases b (a' + 2 / (K : ℝ)) with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [hb', heq]; linarith
      · rw [hb', heq]
        have hba : (0 : ℝ) ≤ b - a := by linarith
        linarith
    have hKinv : (0 : ℝ) < 1 / K := by positivity
    linarith
  · have hle : (countIn x a b N : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast countIn_le x a b N
    have h6 : (6 : ℝ) / K ≤ 10 / K := by
      rw [div_le_div_iff_of_pos_right hKpos]; norm_num
    linarith

/-! ### The discrepancy bound -/

/-- **The discrepancy bound for every subinterval of `[0, 1]`.**  For `K ≥ 8` and `N ≥ 1`, and
for every `0 ≤ a ≤ b ≤ 1`,

    |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 20/K + 4 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N .

Unlike `abs_countIn_div_sub_le_pow` this covers short intervals and intervals with an endpoint
at `0` or at `1`, so the left-hand side may be taken to be the discrepancy itself. -/
theorem abs_countIn_div_sub_le_pow_of_le (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K)
    (hN : 0 < N) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(countIn x a b N : ℝ) / N - (b - a)|
      ≤ 20 / K + 4 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hK0 : 0 < K := by omega
  have hK2 : 2 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK8 : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set S : ℝ := ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N with hS
  have hSnn : 0 ≤ S := sum_norm_expSum_div_nonneg x K N
  have hupper := countIn_div_le_of_le x hK hN ha hab hb
  rw [← hS] at hupper
  have h10 : (10 : ℝ) / K ≤ 20 / K := by
    rw [div_le_div_iff_of_pos_right hKpos]; norm_num
  refine abs_le.2 ⟨?_, by linarith⟩
  -- the lower bound
  rcases le_or_gt (b - a) (1 - 6 / (K : ℝ)) with hshort | hlong
  · rcases le_or_gt (2 / (K : ℝ)) (b - a) with hlen | hlen
    · have hlen' : b - a ≤ 1 - 4 / (K : ℝ) := by
        have : (4 : ℝ) / K ≤ 6 / K := by
          rw [div_le_div_iff_of_pos_right hKpos]; norm_num
        linarith
      have hmain := abs_countIn_div_sub_le_pow_shift x hK2 hN ha hb hlen hlen'
      rw [← hS] at hmain
      have h4 : (4 : ℝ) / K ≤ 20 / K := by
        rw [div_le_div_iff_of_pos_right hKpos]; norm_num
      linarith [(abs_le.mp hmain).1]
    · have hnn : (0 : ℝ) ≤ (countIn x a b N : ℝ) / N := by positivity
      have h2 : (2 : ℝ) / K ≤ 20 / K := by
        rw [div_le_div_iff_of_pos_right hKpos]; norm_num
      linarith
  · have hsplit := countIn_split_unit x ha hab hb N
    have hsplitR : (countIn x 0 a N : ℝ) + (countIn x a b N : ℝ) + (countIn x b 1 N : ℝ)
        = (N : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsplit
    have hlow := countIn_div_le_of_le x (a := 0) (b := a) hK hN le_rfl ha (by linarith)
    have hhigh := countIn_div_le_of_le x (a := b) (b := 1) hK hN (by linarith) hb le_rfl
    rw [← hS] at hlow hhigh
    have hdiv : (countIn x 0 a N : ℝ) / N + (countIn x a b N : ℝ) / N
        + (countIn x b 1 N : ℝ) / N = 1 := by
      field_simp
      linarith [hsplitR]
    have h20 : (10 : ℝ) / K + 10 / K = 20 / K := by ring
    linarith

/-! ### Explicit rates -/

/-- For a badly approximable `α` the exponential-sum average occurring in the discrepancy bound
is at most `1/(2cK)`, as soon as `K⁹ ≤ N`. -/
theorem sum_norm_expSum_div_le_linear {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {K N : ℕ} (hK : 2 ≤ K)
    (hNK : K ^ 9 ≤ N) :
    ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N
      ≤ 1 / (2 * c * K) := by
  have hK0 : 0 < K := by omega
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNK
  have hNR : ((K : ℝ)) ^ 9 ≤ N := by exact_mod_cast hNK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
      ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N ≤ ((K : ℝ) ^ 4) / (2 * c) / N := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have h1 := norm_expSum_linear_le hc hbad hm.1 N
    have h2 : (m : ℝ) ≤ (K : ℝ) ^ 4 := by
      have : m ≤ K ^ 4 := le_trans hm.2 (Nat.sub_le _ _)
      exact_mod_cast this
    have h3 : ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ ≤ ((K : ℝ) ^ 4) / (2 * c) :=
      h1.trans (by gcongr)
    gcongr
  have hcard : (Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card ≤ K ^ 4 := by
    rw [Nat.card_Icc]
    omega
  calc ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
        ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N
      ≤ ∑ _m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ((K : ℝ) ^ 4) / (2 * c) / N :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) * (((K : ℝ) ^ 4) / (2 * c) / N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((K : ℝ) ^ 4) * (((K : ℝ) ^ 4) / (2 * c) / N) := by
        have hc4 : ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) ≤ (K : ℝ) ^ 4 := by
          have : ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) ≤ ((K ^ 4 : ℕ) : ℝ) := by
            exact_mod_cast hcard
          simpa using this
        have hpos : (0 : ℝ) ≤ ((K : ℝ) ^ 4) / (2 * c) / N := by positivity
        exact mul_le_mul_of_nonneg_right hc4 hpos
    _ = ((K : ℝ) ^ 8) / (2 * c * N) := by field_simp
    _ ≤ 1 / (2 * c * K) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hKpos 8, hc, sq_nonneg ((K : ℝ) ^ 4)]

/-- **An explicit rate, for every interval.**  For `α` badly approximable the discrepancy of
`α n` — the supremum over *all* subintervals of `[0, 1]` — is at most `(20 + 2/c)/K` as soon as
`K⁹ ≤ N`; that is, `O(N^(−1/9))`. -/
theorem abs_countIn_div_sub_le_linear_of_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K)
    (hNK : K ^ 9 ≤ N) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(countIn (fun n : ℕ => α * n) a b N : ℝ) / N - (b - a)| ≤ (20 + 2 / c) / K := by
  have hK0 : 0 < K := by omega
  have hKR : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNK
  have hmain := abs_countIn_div_sub_le_pow_of_le (fun n : ℕ => α * n) hK hN ha hab hb
  have hsum := sum_norm_expSum_div_le_linear hc hbad (by omega : 2 ≤ K) hNK
  have hfin : (20 : ℝ) / K + 4 * (1 / (2 * c * K)) = (20 + 2 / c) / K := by
    field_simp
    ring
  linarith [hmain, hsum, hfin.le, hfin.ge]

/-- For `2α` badly approximable the exponential-sum average occurring in the discrepancy bound
is at most `K⁴ √((16 K⁴/c + 26) N (1 + log N))/N`. -/
theorem sum_norm_expSum_div_le_quadratic {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {K N : ℕ} (hN : 0 < N) :
    ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
        ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N
      ≤ (K : ℝ) ^ 4 * (Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) / N) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  set S : ℝ := Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) with hS
  have hterm : ∀ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
      ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N ≤ S / N := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmK : (m : ℝ) ≤ (K : ℝ) ^ 4 := by
      have : m ≤ K ^ 4 := le_trans hm.2 (Nat.sub_le _ _)
      exact_mod_cast this
    have h1 := norm_expSum_quadratic_le hc hbad hm.1 hN
    have h2 : Real.sqrt ((16 * (m : ℝ) / c + 26) * N * (1 + Real.log N)) ≤ S := by
      rw [hS]
      refine Real.sqrt_le_sqrt ?_
      have h1log : (0 : ℝ) ≤ 1 + Real.log N := by linarith
      gcongr
    have := h1.trans h2
    gcongr
  have hcard : (Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card ≤ K ^ 4 := by
    rw [Nat.card_Icc]; omega
  calc ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
        ‖expSum (fun n : ℕ => α * (n : ℝ) ^ 2) (m : ℤ) N‖ / N
      ≤ ∑ _m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), S / N := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) * (S / N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) ^ 4 * (S / N) := by
        have hc4 : ((Finset.Icc (1 : ℕ) (K ^ 4 - 1)).card : ℝ) ≤ (K : ℝ) ^ 4 := by
          have h := (Nat.cast_le (α := ℝ)).2 hcard
          simpa using h
        have hpos : (0 : ℝ) ≤ S / N := by positivity
        exact mul_le_mul_of_nonneg_right hc4 hpos

/-- **An explicit rate for the quadratic sequence, for every interval.**  If `2α` is badly
approximable with constant `c`, the discrepancy of `α n²` over all subintervals of `[0, 1]` is
at most `20/K + 4 K⁴ √((16 K⁴/c + 26) N (1 + log N))/N`. -/
theorem abs_countIn_div_sub_le_quadratic_of_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(countIn (fun n : ℕ => α * (n : ℝ) ^ 2) a b N : ℝ) / N - (b - a)|
      ≤ 20 / K
        + 4 * (K : ℝ) ^ 4 * Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) / N := by
  have hmain := abs_countIn_div_sub_le_pow_of_le (fun n : ℕ => α * (n : ℝ) ^ 2) hK hN ha hab hb
  have hsum := sum_norm_expSum_div_le_quadratic (α := α) hc hbad (K := K) hN
  have hfin : 4 * ((K : ℝ) ^ 4 *
      (Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) / N))
      = 4 * (K : ℝ) ^ 4 * Real.sqrt ((16 * (K : ℝ) ^ 4 / c + 26) * N * (1 + Real.log N)) / N := by
    ring
  linarith [hmain, hsum, hfin.le, hfin.ge]

/-- The concrete instance `α = √2/2`, for which `2α = √2` is badly approximable with `c = 1/4`,
now for every subinterval of `[0, 1]`. -/
theorem abs_countIn_div_sub_le_sqrt_two_of_le {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(countIn (fun n : ℕ => Real.sqrt 2 / 2 * (n : ℝ) ^ 2) a b N : ℝ) / N - (b - a)|
      ≤ 20 / K
        + 4 * (K : ℝ) ^ 4 * Real.sqrt ((64 * (K : ℝ) ^ 4 + 26) * N * (1 + Real.log N)) / N := by
  have hbad : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ |2 * (Real.sqrt 2 / 2) - (a : ℝ) / q| := by
    intro a q hq
    have h := WeylQuadratic.badlyApproximable_sqrt_two a q hq
    rwa [show 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 by ring]
  have h := abs_countIn_div_sub_le_quadratic_of_le (α := Real.sqrt 2 / 2) (c := 1 / 4)
    (by norm_num) hbad hK hN ha hab hb
  have hcoef : 16 * (K : ℝ) ^ 4 / (1 / 4) + 26 = 64 * (K : ℝ) ^ 4 + 26 := by ring
  rwa [hcoef] at h

end WeylDiscrepancy

end RiemannHypothesis
