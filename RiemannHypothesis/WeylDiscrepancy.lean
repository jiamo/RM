/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylLinear
import RiemannHypothesis.LargeSieveGallagher
import RiemannHypothesis.WeylMinSum

/-!
# A rate of convergence for equidistribution modulo one

`RiemannHypothesis.WeylCount`, `RiemannHypothesis.WeylCountGeneral` and
`RiemannHypothesis.WeylPortmanteau` prove the counting form of Weyl's criterion:
`#{n < N : Int.fract (x n) ∈ [a, b)} / N → b − a` as soon as the exponential sums are `o(N)`.
That deduction is *qualitative*: it converts a limit into a limit and claims no rate, which is
the open boundary those rows record.  This module removes that restriction, by proving an
inequality of Erdős–Turán type: a bound for the discrepancy of the first `N` terms in terms of
*finitely many* exponential sums, valid for every `N`, with explicit constants.

## Main results

* `kern` — the Fejér-type kernel `K_M(t) = |∑_{j < M} e(t j)|² / M`, nonnegative, of mass one,
  and concentrated at scale `1/M`.
* `abs_avg_sub_integral_le` — **the quantitative Weyl criterion**: for a `1`-periodic `L`-Lipschitz
  test function `g` with values in `[0, 1]`,

      |(1/N) ∑_{n<N} g(xₙ) − ∫₀¹ g| ≤ L δ + 1/(2Mδ) + 2 ∑_{m=1}^{M−1} ‖∑_{n<N} e(m xₙ)‖ / N

  for every `M ≥ 1` and every `0 < δ ≤ 1/2`.
* `abs_countIn_div_sub_le` — the same for the counting function of an interval, with the
  trapezoidal parameter `η` in place of the Lipschitz constant.
* `abs_countIn_div_sub_le_pow` — the tidied form: for `K ≥ 2`,

      |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 4/K + 2 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N .

* `abs_countIn_div_sub_le_linear` — **an explicit rate**: for a badly approximable `α`, meaning
  `‖mα‖ ≥ c/m` for all `m ≥ 1`, the discrepancy of `α n` on an interval is at most
  `(4 + 1/c)/K` as soon as `K⁹ ≤ N`; that is, `O(N^(−1/9))`.

## Proof

The kernel `K_M(t) = |∑_{j<M} e(tj)|²/M` expands as `(1/M) ∑_{j,k<M} cos(2π t (j − k))`, so its
integral over a period is `1` (the diagonal), and it is bounded by `1/(4M t²)` for
`0 < |t| ≤ 1/2` by the geometric-series bound `‖∑_{j<M} e(θ j)‖ ≤ 1/(2‖θ‖)` of
`RiemannHypothesis.WeylQuadratic`.  Two estimates follow.

*Smoothing.*  Because `K_M` has mass one, `g(y) − ∫₀¹ g(t) K_M(y − t) dt` is an average of
`g(y) − g(y − s)` against `K_M(s)`; the part `|s| ≤ δ` costs `Lδ` by the Lipschitz bound and the
part `|s| > δ` costs `1/(2Mδ)` by the tail bound, since `0 ≤ g ≤ 1`.

*Averaging.*  Conversely `(1/N) ∑_n K_M(xₙ − t) = 1 + (1/M) ∑_{j ≠ k} (1/N) ∑_n cos(2π(j−k)(xₙ−t))`,
and each inner sum is bounded by the exponential sum at frequency `j − k`; folding the pairs onto
their difference gives `2 ∑_{m=1}^{M−1} ‖∑_n e(m xₙ)‖/N` for the deviation of the smoothed
empirical density from `1`, hence the same bound for `(1/N) ∑_n ∫ g K_M(xₙ − ·) − ∫₀¹ g`.

Adding the two and squeezing the indicator of `[a, b)` between two trapezoids of slope `1/η`
gives the discrepancy bound.  With `η = 1/K`, `δ = 1/K²` and `M = K⁴` all the parameters collapse
to a single one.

## Scope

The weight of the `m`-th exponential sum here is `1`, not the `1/m` of the sharp Erdős–Turán
inequality, which needs the Beurling–Selberg extremal majorant; the resulting exponent in the
linear application is `1/9` rather than the classical `1`.  Nothing here concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory

namespace RiemannHypothesis

namespace WeylDiscrepancy

open KusminLandau WeylQuadratic WeylCount LargeSieveGallagher

/-! ### The kernel -/

/-- The Fejér-type kernel `K_M(t) = |∑_{j < M} e(t j)|² / M`. -/
def kern (M : ℕ) (t : ℝ) : ℝ := ‖∑ j ∈ range M, e2pi (t * j)‖ ^ 2 / M

theorem kern_eq_sum (M : ℕ) (t : ℝ) :
    ((kern M t : ℝ) : ℂ)
      = (∑ j ∈ range M, ∑ k ∈ range M, e2pi (t * j - t * k)) / M := by
  set S : ℂ := ∑ j ∈ range M, e2pi (t * j) with hS
  have hconj : (starRingEnd ℂ) S = ∑ k ∈ range M, e2pi (-(t * k)) := by
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun k _ => WeylDifferencing.conj_e2pi _
  have hsq : ((‖S‖ : ℝ) : ℂ) ^ 2 = ∑ j ∈ range M, ∑ k ∈ range M, e2pi (t * j - t * k) := by
    have h1 : ((‖S‖ : ℝ) : ℂ) ^ 2 = S * (starRingEnd ℂ) S := by
      rw [RCLike.mul_conj]; norm_cast
    rw [h1, hconj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← e2pi_add]
    ring_nf
  unfold kern
  push_cast
  rw [hsq]

/-- The kernel as a double sum of standard exponentials. -/
theorem kern_eq_sum' (M : ℕ) (t : ℝ) :
    ((kern M t : ℝ) : ℂ)
      = ∑ j ∈ range M, ∑ k ∈ range M, e2pi ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) / M := by
  rw [kern_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

theorem intervalIntegrable_e2pi_div (M : ℕ) (c : ℝ) :
    IntervalIntegrable (fun t : ℝ => e2pi (c * t) / M) volume 0 1 :=
  ((continuous_e2pi_mul c).div_const _).intervalIntegrable _ _

theorem intervalIntegrable_sum_e2pi_div (M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) :
    IntervalIntegrable (fun t : ℝ => ∑ k ∈ s, e2pi (c k * t) / M) volume 0 1 :=
  (continuous_finsetSum _ fun k _ =>
    (continuous_e2pi_mul (c k)).div_const _).intervalIntegrable _ _

theorem integral_kern (M : ℕ) (hM : 0 < M) : (∫ t in (0 : ℝ)..1, kern M t) = 1 := by
  have hterm : ∀ j k : ℕ,
      (∫ t in (0 : ℝ)..1, e2pi ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) / M)
        = if j = k then (1 / M : ℂ) else 0 := by
    intro j k
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_e2pi_int]
    by_cases h : j = k
    · subst h; simp
    · have hne : ((j : ℤ) - (k : ℤ)) ≠ 0 := sub_ne_zero_of_ne (by exact_mod_cast h)
      rw [if_neg hne, if_neg h]
      simp
  have hcomplex : ((∫ t in (0 : ℝ)..1, kern M t : ℝ) : ℂ) = 1 := by
    rw [← intervalIntegral.integral_ofReal]
    calc (∫ t in (0 : ℝ)..1, ((kern M t : ℝ) : ℂ))
        = ∫ t in (0 : ℝ)..1,
            ∑ j ∈ range M, ∑ k ∈ range M, e2pi ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) / M :=
          intervalIntegral.integral_congr fun t _ => kern_eq_sum' M t
      _ = ∑ j ∈ range M, ∑ k ∈ range M,
            ∫ t in (0 : ℝ)..1, e2pi ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) / M := by
          refine Eq.trans (intervalIntegral.integral_finsetSum
            (s := (range M : Finset ℕ))
            (f := fun (j : ℕ) t => ∑ k ∈ range M, e2pi ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) / M)
            (fun j _ => intervalIntegrable_sum_e2pi_div M (range M)
              (fun k => (((j : ℤ) - (k : ℤ) : ℤ) : ℝ)))) ?_
          exact Finset.sum_congr rfl fun j _ =>
            intervalIntegral.integral_finsetSum fun k _ => intervalIntegrable_e2pi_div M _
      _ = 1 := by
          simp_rw [hterm]
          rw [Finset.sum_congr rfl fun j (hj : j ∈ range M) =>
            Finset.sum_ite_eq (range M) j (fun _ => (1 / M : ℂ))]
          simp only [Finset.mem_range]
          rw [Finset.sum_congr rfl fun j (hj : j ∈ range M) => if_pos (Finset.mem_range.mp hj)]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [mul_one_div, div_self (Nat.cast_ne_zero.mpr hM.ne')]
  exact_mod_cast hcomplex


theorem kern_nonneg (M : ℕ) (t : ℝ) : 0 ≤ kern M t := by
  unfold kern; positivity

theorem kern_neg (M : ℕ) (t : ℝ) : kern M (-t) = kern M t := by
  have h : (∑ j ∈ range M, e2pi (-t * j))
      = (starRingEnd ℂ) (∑ j ∈ range M, e2pi (t * j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WeylDifferencing.conj_e2pi]
    ring_nf
  unfold kern
  rw [h, RCLike.norm_conj]

theorem kern_periodic (M : ℕ) : Function.Periodic (kern M) 1 := by
  intro t
  have h : (∑ j ∈ range M, e2pi ((t + 1) * j)) = ∑ j ∈ range M, e2pi (t * j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (t + 1) * (j : ℝ) = t * j + ((j : ℤ) : ℝ) := by push_cast; ring
    rw [hj, ← e2pi_sub_int (t * (j : ℝ) + ((j : ℤ) : ℝ)) (j : ℤ)]
    ring_nf
  unfold kern
  rw [h]

theorem integral_kern_symm (M : ℕ) (hM : 0 < M) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), kern M t) = 1 := by
  have h := (kern_periodic M).intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num at h
  rw [h]
  exact integral_kern M hM

theorem intDist_eq_abs {t : ℝ} (ht : |t| ≤ 1 / 2) : intDist t = |t| := by
  unfold intDist
  rcases lt_or_eq_of_le ht with hlt | heq
  · have h0 : round t = 0 := by
      rw [round_eq]
      have h1 : (0 : ℝ) ≤ t + 1 / 2 := by cases abs_lt.mp hlt; linarith
      have h2 : t + 1 / 2 < 1 := by cases abs_lt.mp hlt; linarith
      exact_mod_cast Int.floor_eq_zero_iff.mpr ⟨h1, h2⟩
    rw [h0]
    norm_num
  · rcases abs_eq (by norm_num : (0:ℝ) ≤ 1 / 2) |>.mp heq with h | h
    · have : round t = 1 := by
        rw [round_eq, h]
        norm_num
      rw [this, h]
      norm_num
    · have : round t = 0 := by
        rw [round_eq, h]
        norm_num
      rw [this, h]
      norm_num

theorem kern_le_inv (M : ℕ) (hM : 0 < M) {t : ℝ} (ht : t ≠ 0) (ht2 : |t| ≤ 1 / 2) :
    kern M t ≤ 1 / (4 * M * t ^ 2) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have hd : intDist t = |t| := intDist_eq_abs ht2
  have hne : intDist t ≠ 0 := by rw [hd]; exact habs.ne'
  have hsum : ‖∑ j ∈ range M, e2pi (t * j)‖ ≤ 1 / (2 * |t|) := by
    have h := norm_geomSum_e2pi_le hne M 0
    simpa [hd] using h
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
  unfold kern
  calc ‖∑ j ∈ range M, e2pi (t * j)‖ ^ 2 / M ≤ (1 / (2 * |t|)) ^ 2 / M := by gcongr
    _ = 1 / (4 * M * t ^ 2) := by
        rw [div_pow, one_pow, mul_pow, sq_abs]
        field_simp
        ring


theorem continuous_kern (M : ℕ) : Continuous (kern M) := by
  unfold kern e2pi
  fun_prop

theorem integral_kern_tail (M : ℕ) (hM : 0 < M) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    (∫ t in δ..(1 / 2 : ℝ), kern M t) + (∫ t in (-(1 / 2) : ℝ)..(-δ), kern M t)
      ≤ 1 / (2 * M * δ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hzero : (0 : ℝ) ∉ Set.uIcc δ (1 / 2 : ℝ) := by
    rw [Set.uIcc_of_le hδ]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 / (4 * M)) * (t ^ (-2 : ℤ)))
      volume δ (1 / 2) := by
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul continuousOn_const ?_)
    refine ContinuousOn.zpow₀ continuousOn_id _ fun t ht => ?_
    rw [Set.uIcc_of_le hδ] at ht
    exact Or.inl (by simpa using (lt_of_lt_of_le hδ0 ht.1).ne')
  have hmono : (∫ t in δ..(1 / 2 : ℝ), kern M t)
      ≤ ∫ t in δ..(1 / 2 : ℝ), (1 / (4 * M)) * (t ^ (-2 : ℤ)) := by
    refine intervalIntegral.integral_mono_on hδ
      ((continuous_kern M).intervalIntegrable _ _) hint2 fun t ht => ?_
    have htpos : 0 < t := lt_of_lt_of_le hδ0 ht.1
    have habs : |t| ≤ 1 / 2 := by rw [abs_of_pos htpos]; exact ht.2
    calc kern M t ≤ 1 / (4 * M * t ^ 2) := kern_le_inv M hM htpos.ne' habs
      _ = (1 / (4 * M)) * (t ^ (-2 : ℤ)) := by
          rw [zpow_neg, zpow_two]
          field_simp
  have hz := integral_zpow (a := δ) (b := (1 / 2 : ℝ)) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
  have hcalc : (∫ t in δ..(1 / 2 : ℝ), (1 / (4 * M)) * (t ^ (-2 : ℤ)))
      = (1 / (4 * M)) * (1 / δ - 2) := by
    rw [intervalIntegral.integral_const_mul, hz]
    have h : ((-2 : ℤ) + 1) = (-1 : ℤ) := by decide
    rw [h]
    simp only [zpow_neg, zpow_one]
    congr 1
    rw [div_eq_iff (by norm_num : ((-2 : ℤ) : ℝ) + 1 ≠ 0)]
    field_simp
    ring
  have hneg : (∫ t in (-(1 / 2) : ℝ)..(-δ), kern M t) = ∫ t in δ..(1 / 2 : ℝ), kern M t := by
    rw [← intervalIntegral.integral_comp_neg (fun t => kern M t)]
    exact intervalIntegral.integral_congr fun t _ => kern_neg M t
  have hsplit : (1 / (4 * M)) * (1 / δ - 2) = 1 / (4 * M * δ) - 1 / (2 * M) := by
    field_simp
    ring
  have hhalf : 1 / (4 * M * δ) - 1 / (2 * M) ≤ 1 / (4 * M * δ) := by
    have : (0 : ℝ) < 1 / (2 * M) := by positivity
    linarith
  have htwo : 2 * (1 / (4 * M * δ)) = 1 / (2 * M * δ) := by
    field_simp
    ring
  rw [hneg]
  linarith [hmono, hcalc.le, hcalc.ge]

/-! ### Exponential sums -/

/-- The exponential sum of the sequence at frequency `m`. -/
def expSum (x : ℕ → ℝ) (m : ℤ) (N : ℕ) : ℂ := ∑ n ∈ range N, e2pi ((m : ℝ) * x n)

theorem norm_expSum_neg (x : ℕ → ℝ) (m : ℤ) (N : ℕ) :
    ‖expSum x (-m) N‖ = ‖expSum x m N‖ := by
  have h : expSum x (-m) N = (starRingEnd ℂ) (expSum x m N) := by
    unfold expSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [WeylDifferencing.conj_e2pi]
    congr 1
    push_cast
    ring
  rw [h, RCLike.norm_conj]

/-- Folding the shifted frequencies onto the positive ones. -/
theorem sum_norm_expSum_shift_le (x : ℕ → ℝ) (N M j : ℕ) (hj : j < M) :
    ∑ k ∈ (range M).erase j, ‖expSum x ((j : ℤ) - k) N‖
      ≤ 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ := by
  classical
  set P : Finset ℤ := (Finset.Icc (1 : ℕ) (M - 1)).image (fun m : ℕ => (m : ℤ)) with hP
  set Q : Finset ℤ := (Finset.Icc (1 : ℕ) (M - 1)).image (fun m : ℕ => -(m : ℤ)) with hQ
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    rw [hP, Finset.mem_image] at hiP
    rw [hQ, Finset.mem_image] at hiQ
    obtain ⟨m, hm, rfl⟩ := hiP
    obtain ⟨m', hm', hmm⟩ := hiQ
    rw [Finset.mem_Icc] at hm hm'
    omega
  have himg : ((range M).erase j).image (fun k : ℕ => (j : ℤ) - k) ⊆ P ∪ Q := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [Finset.mem_erase, Finset.mem_range] at hk
    rcases lt_or_gt_of_ne (show (k : ℤ) ≠ (j : ℤ) by exact_mod_cast hk.1) with hlt | hgt
    · refine Finset.mem_union_left _ ?_
      rw [hP, Finset.mem_image]
      refine ⟨j - k, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · have : k < j := by exact_mod_cast hlt
        push_cast [Nat.cast_sub this.le]
        ring
    · refine Finset.mem_union_right _ ?_
      rw [hQ, Finset.mem_image]
      refine ⟨k - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        have : j < k := by exact_mod_cast hgt
        constructor <;> omega
      · have hjk : j < k := by exact_mod_cast hgt
        push_cast [Nat.cast_sub hjk.le]
        ring
  have hinj : Set.InjOn (fun k : ℕ => (j : ℤ) - k) ((range M).erase j) := by
    intro a _ b _ hab
    have hab' : (j : ℤ) - a = (j : ℤ) - b := hab
    have : (a : ℤ) = b := by omega
    exact_mod_cast this
  calc ∑ k ∈ (range M).erase j, ‖expSum x ((j : ℤ) - k) N‖
      = ∑ i ∈ ((range M).erase j).image (fun k : ℕ => (j : ℤ) - k), ‖expSum x i N‖ :=
        (Finset.sum_image (f := fun i : ℤ => ‖expSum x i N‖) hinj).symm
    _ ≤ ∑ i ∈ P ∪ Q, ‖expSum x i N‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => norm_nonneg _
    _ = (∑ i ∈ P, ‖expSum x i N‖) + ∑ i ∈ Q, ‖expSum x i N‖ := Finset.sum_union hdisj
    _ = 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ := by
        have h1 : (∑ i ∈ P, ‖expSum x i N‖)
            = ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ := by
          rw [hP, Finset.sum_image]
          intro a _ b _ h
          have h' : (a : ℤ) = (b : ℤ) := h
          exact_mod_cast h'
        have h2 : (∑ i ∈ Q, ‖expSum x i N‖)
            = ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ := by
          rw [hQ, Finset.sum_image]
          · exact Finset.sum_congr rfl fun m _ => norm_expSum_neg x (m : ℤ) N
          · intro a _ b _ h
            have h' : -(a : ℤ) = -(b : ℤ) := h
            have : (a : ℤ) = b := by omega
            exact_mod_cast this
        rw [h1, h2]
        ring


theorem norm_inner_eq (x : ℕ → ℝ) (t : ℝ) (N j k : ℕ) :
    ‖∑ n ∈ range N, e2pi ((x n - t) * j - (x n - t) * k)‖ = ‖expSum x ((j : ℤ) - k) N‖ := by
  have hfac : (∑ n ∈ range N, e2pi ((x n - t) * j - (x n - t) * k))
      = e2pi (-((((j : ℤ) - k : ℤ) : ℝ) * t)) * expSum x ((j : ℤ) - k) N := by
    unfold expSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← e2pi_add]
    congr 1
    push_cast
    ring
  rw [hfac, norm_mul, norm_e2pi, one_mul]

theorem abs_avgKern_sub_one_le (x : ℕ → ℝ) {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (t : ℝ) :
    |(∑ n ∈ range N, kern M (x n - t)) / N - 1|
      ≤ 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by
  classical
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set S : ℕ → ℕ → ℂ := fun j k => ∑ n ∈ range N, e2pi ((x n - t) * j - (x n - t) * k) with hS
  have hdiag : ∀ j : ℕ, S j j = (N : ℂ) := by
    intro j
    rw [hS]
    simp [e2pi]
  have h1 : (∑ n ∈ range N, ((kern M (x n - t) : ℝ) : ℂ))
      = (∑ j ∈ range M, ∑ k ∈ range M, S j k) / M := by
    rw [Finset.sum_congr rfl (fun n _ => kern_eq_sum M (x n - t)), ← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have h2 : (∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k))
      = (∑ j ∈ range M, ∑ k ∈ range M, S j k) - (M : ℂ) * N := by
    have hrow : ∀ j ∈ range M, (∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k))
        = (∑ k ∈ range M, S j k) - (N : ℂ) := by
      intro j hj
      have hpt : ∀ k : ℕ, (if j = k then (0 : ℂ) else S j k)
          = S j k - (if j = k then S j k else 0) := by
        intro k
        by_cases h : j = k
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_sub_distrib,
        Finset.sum_ite_eq (range M) j (fun k => S j k), if_pos hj, hdiag j]
    rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hexpand : (((∑ n ∈ range N, kern M (x n - t)) / N - 1 : ℝ) : ℂ)
      = (∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k)) / ((N : ℂ) * M) := by
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    push_cast
    rw [h2, h1]
    field_simp
  have hbound : ‖(∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k))‖
      ≤ (M : ℝ) * (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) := by
    calc ‖(∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k))‖
        ≤ ∑ j ∈ range M, ‖∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ range M, (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjM : j < M := Finset.mem_range.mp hj
          calc ‖∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k)‖
              ≤ ∑ k ∈ range M, ‖(if j = k then (0 : ℂ) else S j k)‖ := norm_sum_le _ _
            _ = ∑ k ∈ (range M).erase j, ‖expSum x ((j : ℤ) - k) N‖ := by
                have hzero : ‖(if j = j then (0 : ℂ) else S j j)‖ = 0 := by simp
                rw [← Finset.sum_erase (range M) hzero]
                refine Finset.sum_congr rfl fun k hk => ?_
                have hne : j ≠ k := (Finset.mem_erase.mp hk).1.symm
                rw [if_neg hne, hS]
                exact norm_inner_eq x t N j k
            _ ≤ 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ :=
                sum_norm_expSum_shift_le x N M j hjM
      _ = (M : ℝ) * (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have habs : |(∑ n ∈ range N, kern M (x n - t)) / N - 1|
      = ‖(((∑ n ∈ range N, kern M (x n - t)) / N - 1 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hexpand, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  have hsum : (2 : ℝ) * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N
      = (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) / N := by
    rw [mul_div_assoc, Finset.sum_div]
  rw [hsum]
  calc ‖(∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (0 : ℂ) else S j k))‖
      ≤ (M : ℝ) * (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) := hbound
    _ = (2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖) / N * ((N : ℝ) * M) := by
        field_simp


/-- **Smoothing.**  A periodic Lipschitz function is close to its convolution with the kernel. -/
theorem abs_sub_smoothing_le {g : ℝ → ℝ} {L δ : ℝ} {M : ℕ} (hM : 0 < M)
    (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (hper : ∀ t, g (t + 1) = g t)
    (hlip : ∀ u v, |g u - g v| ≤ L * |u - v|) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (y : ℝ) :
    |g y - ∫ t in (0 : ℝ)..1, g t * kern M (y - t)| ≤ L * δ + 1 / (2 * M * δ) := by
  have hL : 0 ≤ L := by
    have h := hlip 0 1
    have h2 : |g 0 - g 1| ≥ 0 := abs_nonneg _
    simp only [zero_sub, abs_neg, abs_one, mul_one] at h
    linarith
  have hgc : Continuous g := by
    refine LipschitzWith.continuous (K := Real.toNNReal L) ?_
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |g u - g v| ≤ L * |u - v| := hlip u v
      _ = (Real.toNNReal L : ℝ) * |u - v| := by rw [Real.coe_toNNReal L hL]
  -- the integrand is periodic
  have hFper : Function.Periodic (fun t => g t * kern M (y - t)) 1 := by
    intro t
    change g (t + 1) * kern M (y - (t + 1)) = g t * kern M (y - t)
    have h1 : g (t + 1) = g t := hper t
    have h2 : kern M (y - (t + 1)) = kern M (y - t) := by
      have := (kern_periodic M) (y - (t + 1))
      rw [show y - (t + 1) + 1 = y - t by ring] at this
      exact this.symm
    rw [h1, h2]
  have hshift : (∫ t in (0 : ℝ)..1, g t * kern M (y - t))
      = ∫ t in (y - 1 / 2)..(y - 1 / 2 + 1), g t * kern M (y - t) := by
    have h := hFper.intervalIntegral_add_eq 0 (y - 1 / 2)
    rw [zero_add] at h
    exact h
  have hsub : (∫ t in (y - 1 / 2)..(y - 1 / 2 + 1), g t * kern M (y - t))
      = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), g (y - s) * kern M s := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := y - 1 / 2) (b := y - 1 / 2 + 1) (f := fun s => g (y - s) * kern M s) y
    rw [show y - (y - 1 / 2 + 1) = -(1 / 2 : ℝ) by ring, show y - (y - 1 / 2) = (1 / 2 : ℝ) by ring]
      at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show y - (y - t) = t by ring]
  have hconst : g y = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), g y * kern M s := by
    rw [intervalIntegral.integral_const_mul, integral_kern_symm M hM, mul_one]
  have hcontprod : Continuous (fun s : ℝ => (g y - g (y - s)) * kern M s) := by
    exact ((continuous_const.sub (hgc.comp (continuous_const.sub continuous_id))).mul
      (continuous_kern M))
  have hdiff : g y - (∫ t in (0 : ℝ)..1, g t * kern M (y - t))
      = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), (g y - g (y - s)) * kern M s := by
    rw [hshift, hsub]
    nth_rewrite 1 [hconst]
    have hI := intervalIntegral.integral_sub (a := (-(1 / 2) : ℝ)) (b := (1 / 2 : ℝ))
      (μ := MeasureTheory.volume)
      (f := fun s : ℝ => g y * kern M s) (g := fun s : ℝ => g (y - s) * kern M s)
      ((continuous_const.mul (continuous_kern M)).intervalIntegrable _ _)
      (((hgc.comp (continuous_const.sub continuous_id)).mul
        (continuous_kern M)).intervalIntegrable _ _)
    rw [← hI]
    refine intervalIntegral.integral_congr fun s _ => ?_
    change g y * kern M s - g (y - s) * kern M s = (g y - g (y - s)) * kern M s
    ring
  rw [hdiff]
  -- bound the integral
  have habs : |∫ s in (-(1 / 2) : ℝ)..(1 / 2), (g y - g (y - s)) * kern M s|
      ≤ ∫ s in (-(1 / 2) : ℝ)..(1 / 2), |g y - g (y - s)| * kern M s := by
    have hle : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
    calc |∫ s in (-(1 / 2) : ℝ)..(1 / 2), (g y - g (y - s)) * kern M s|
        ≤ ∫ s in (-(1 / 2) : ℝ)..(1 / 2), |(g y - g (y - s)) * kern M s| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), |g y - g (y - s)| * kern M s := by
          refine intervalIntegral.integral_congr fun s _ => ?_
          rw [abs_mul, abs_of_nonneg (kern_nonneg M s)]
  have hFcont : Continuous (fun s : ℝ => |g y - g (y - s)| * kern M s) :=
    ((continuous_const.sub (hgc.comp (continuous_const.sub continuous_id))).abs).mul
      (continuous_kern M)
  have hFint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => |g y - g (y - s)| * kern M s)
      MeasureTheory.volume a b := fun a b => hFcont.intervalIntegrable _ _
  have hKint : ∀ a b : ℝ, IntervalIntegrable (kern M) MeasureTheory.volume a b :=
    fun a b => (continuous_kern M).intervalIntegrable _ _
  have hδhalf : -(1 / 2 : ℝ) ≤ -δ := by linarith
  have hδδ : -δ ≤ δ := by linarith
  have hδ2 : δ ≤ (1 / 2 : ℝ) := hδ
  -- split both integrals
  have hsplitF : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), |g y - g (y - s)| * kern M s)
      = (∫ s in (-(1 / 2) : ℝ)..(-δ), |g y - g (y - s)| * kern M s)
        + (∫ s in (-δ)..δ, |g y - g (y - s)| * kern M s)
        + ∫ s in δ..(1 / 2 : ℝ), |g y - g (y - s)| * kern M s := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFint _ _) (hFint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hFint _ _) (hFint _ _)]
  have hsplitK : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), kern M s)
      = (∫ s in (-(1 / 2) : ℝ)..(-δ), kern M s) + (∫ s in (-δ)..δ, kern M s)
        + ∫ s in δ..(1 / 2 : ℝ), kern M s := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hKint _ _) (hKint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hKint _ _) (hKint _ _)]
  have hJ1 : 0 ≤ ∫ s in (-(1 / 2) : ℝ)..(-δ), kern M s :=
    intervalIntegral.integral_nonneg hδhalf fun s _ => kern_nonneg M s
  have hJ3 : 0 ≤ ∫ s in δ..(1 / 2 : ℝ), kern M s :=
    intervalIntegral.integral_nonneg hδ2 fun s _ => kern_nonneg M s
  have hJ2le : (∫ s in (-δ)..δ, kern M s) ≤ 1 := by
    have h := integral_kern_symm M hM
    rw [hsplitK] at h
    linarith
  have hI1 : (∫ s in (-(1 / 2) : ℝ)..(-δ), |g y - g (y - s)| * kern M s)
      ≤ ∫ s in (-(1 / 2) : ℝ)..(-δ), kern M s := by
    refine intervalIntegral.integral_mono_on hδhalf (hFint _ _) (hKint _ _) fun s _ => ?_
    have hle : |g y - g (y - s)| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hg0 y, hg1 (y - s)]; linarith [hg1 y, hg0 (y - s)]]
    calc |g y - g (y - s)| * kern M s ≤ 1 * kern M s := by
          exact mul_le_mul_of_nonneg_right hle (kern_nonneg M s)
      _ = kern M s := one_mul _
  have hI3 : (∫ s in δ..(1 / 2 : ℝ), |g y - g (y - s)| * kern M s)
      ≤ ∫ s in δ..(1 / 2 : ℝ), kern M s := by
    refine intervalIntegral.integral_mono_on hδ2 (hFint _ _) (hKint _ _) fun s _ => ?_
    have hle : |g y - g (y - s)| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hg0 y, hg1 (y - s)]; linarith [hg1 y, hg0 (y - s)]]
    calc |g y - g (y - s)| * kern M s ≤ 1 * kern M s := by
          exact mul_le_mul_of_nonneg_right hle (kern_nonneg M s)
      _ = kern M s := one_mul _
  have hI2 : (∫ s in (-δ)..δ, |g y - g (y - s)| * kern M s)
      ≤ (L * δ) * ∫ s in (-δ)..δ, kern M s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hδδ (hFint _ _)
      ((continuous_const.mul (continuous_kern M)).intervalIntegrable _ _) fun s hs => ?_
    have habs : |s| ≤ δ := by
      rw [abs_le]
      exact ⟨hs.1, hs.2⟩
    have hle : |g y - g (y - s)| ≤ L * δ := by
      calc |g y - g (y - s)| ≤ L * |y - (y - s)| := hlip y (y - s)
        _ = L * |s| := by rw [show y - (y - s) = s by ring]
        _ ≤ L * δ := by exact mul_le_mul_of_nonneg_left habs hL
    exact mul_le_mul_of_nonneg_right hle (kern_nonneg M s)
  have hI2' : (∫ s in (-δ)..δ, |g y - g (y - s)| * kern M s) ≤ L * δ := by
    have hLδ : 0 ≤ L * δ := by positivity
    calc (∫ s in (-δ)..δ, |g y - g (y - s)| * kern M s)
        ≤ (L * δ) * ∫ s in (-δ)..δ, kern M s := hI2
      _ ≤ (L * δ) * 1 := by exact mul_le_mul_of_nonneg_left hJ2le hLδ
      _ = L * δ := mul_one _
  have htail := integral_kern_tail M hM hδ0 hδ
  calc |∫ s in (-(1 / 2) : ℝ)..(1 / 2), (g y - g (y - s)) * kern M s|
      ≤ ∫ s in (-(1 / 2) : ℝ)..(1 / 2), |g y - g (y - s)| * kern M s := habs
    _ ≤ L * δ + 1 / (2 * M * δ) := by
        rw [hsplitF]
        linarith [hI1, hI3, hI2', htail]

theorem abs_avg_smoothing_sub_integral_le {g : ℝ → ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (hgc : Continuous g) (x : ℕ → ℝ) :
    |(∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N
        - ∫ t in (0 : ℝ)..1, g t|
      ≤ 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set B : ℝ := 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : 0 ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N :=
      Finset.sum_nonneg fun m _ => by positivity
    linarith
  set A : ℝ → ℝ := fun t => (∑ n ∈ range N, kern M (x n - t)) / N with hA
  have hAcont : Continuous A := by
    rw [hA]
    exact (continuous_finsetSum _ fun n _ =>
      (continuous_kern M).comp (continuous_const.sub continuous_id)).div_const _
  have hAbound : ∀ t, |A t - 1| ≤ B := fun t => abs_avgKern_sub_one_le x hM hN t
  have hswap : (∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t))
      = ∫ t in (0 : ℝ)..1, g t * (∑ n ∈ range N, kern M (x n - t)) := by
    rw [← intervalIntegral.integral_finsetSum
      (f := fun n t => g t * kern M (x n - t))
      (fun n _ => (hgc.mul ((continuous_kern M).comp
        (continuous_const.sub continuous_id))).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    change (∑ n ∈ range N, g t * kern M (x n - t)) = g t * ∑ n ∈ range N, kern M (x n - t)
    rw [Finset.mul_sum]
  have hkey : (∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N
      - ∫ t in (0 : ℝ)..1, g t = ∫ t in (0 : ℝ)..1, g t * (A t - 1) := by
    rw [hswap, ← intervalIntegral.integral_div]
    have hI := intervalIntegral.integral_sub (a := (0 : ℝ)) (b := (1 : ℝ))
      (μ := MeasureTheory.volume)
      (f := fun t : ℝ => (g t * ∑ n ∈ range N, kern M (x n - t)) / N)
      (g := fun t : ℝ => g t)
      (((hgc.mul (continuous_finsetSum _ fun n _ =>
        (continuous_kern M).comp (continuous_const.sub continuous_id))).div_const
          _).intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
    rw [← hI]
    refine intervalIntegral.integral_congr fun t _ => ?_
    change g t * (∑ n ∈ range N, kern M (x n - t)) / N - g t = g t * (A t - 1)
    rw [hA]
    field_simp
  rw [hkey]
  have hintg : (∫ t in (0 : ℝ)..1, g t) ≤ 1 := by
    calc (∫ t in (0 : ℝ)..1, g t) ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by norm_num) (hgc.intervalIntegrable _ _)
            intervalIntegrable_const fun t _ => hg1 t
      _ = 1 := by simp
  calc |∫ t in (0 : ℝ)..1, g t * (A t - 1)|
      ≤ ∫ t in (0 : ℝ)..1, |g t * (A t - 1)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, g t * B := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          ((hgc.mul (hAcont.sub continuous_const)).abs.intervalIntegrable _ _)
          ((hgc.mul continuous_const).intervalIntegrable _ _) fun t _ => ?_
        rw [abs_mul, abs_of_nonneg (hg0 t)]
        exact mul_le_mul_of_nonneg_left (hAbound t) (hg0 t)
    _ = (∫ t in (0 : ℝ)..1, g t) * B := by
        rw [intervalIntegral.integral_mul_const]
    _ ≤ 1 * B := by exact mul_le_mul_of_nonneg_right hintg hB0
    _ = B := one_mul _

/-- **The quantitative Weyl criterion.** -/
theorem abs_avg_sub_integral_le {g : ℝ → ℝ} {L δ : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (hper : ∀ t, g (t + 1) = g t)
    (hlip : ∀ u v, |g u - g v| ≤ L * |u - v|) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (x : ℕ → ℝ) :
    |(∑ n ∈ range N, g (x n)) / N - ∫ t in (0 : ℝ)..1, g t|
      ≤ L * δ + 1 / (2 * M * δ)
        + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ L := by
    have h := hlip 0 1
    have h2 : |g 0 - g 1| ≥ 0 := abs_nonneg _
    simp only [zero_sub, abs_neg, abs_one, mul_one] at h
    linarith
  have hgc : Continuous g := by
    refine LipschitzWith.continuous (K := Real.toNNReal L) ?_
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |g u - g v| ≤ L * |u - v| := hlip u v
      _ = (Real.toNNReal L : ℝ) * |u - v| := by rw [Real.coe_toNNReal L hL]
  set C : ℝ := L * δ + 1 / (2 * M * δ) with hC
  have h1 : |(∑ n ∈ range N, g (x n)) / N
      - (∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N| ≤ C := by
    have hsub : (∑ n ∈ range N, g (x n)) / N
        - (∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N
        = (∑ n ∈ range N, (g (x n) - ∫ t in (0 : ℝ)..1, g t * kern M (x n - t))) / N := by
      rw [Finset.sum_sub_distrib, sub_div]
    rw [hsub, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    calc |∑ n ∈ range N, (g (x n) - ∫ t in (0 : ℝ)..1, g t * kern M (x n - t))|
        ≤ ∑ n ∈ range N, |g (x n) - ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ range N, C :=
          Finset.sum_le_sum fun n _ => abs_sub_smoothing_le hM hg0 hg1 hper hlip hδ0 hδ (x n)
      _ = C * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have h2 := abs_avg_smoothing_sub_integral_le (g := g) hM hN hg0 hg1 hgc x
  calc |(∑ n ∈ range N, g (x n)) / N - ∫ t in (0 : ℝ)..1, g t|
      ≤ |(∑ n ∈ range N, g (x n)) / N
          - (∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N|
        + |(∑ n ∈ range N, ∫ t in (0 : ℝ)..1, g t * kern M (x n - t)) / N
          - ∫ t in (0 : ℝ)..1, g t| := abs_sub_le _ _ _
    _ ≤ C + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by
        linarith [h1, h2]
    _ = L * δ + 1 / (2 * M * δ)
          + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by rw [hC]

/-! ### The periodized trapezoid -/

theorem abs_trap_sub_trap_le {u v η : ℝ} (hη : 0 < η) (s t : ℝ) :
    |trap u v η s - trap u v η t| ≤ (1 / η) * |s - t| := by
  have hf : |(s - u + η) / η - (t - u + η) / η| = (1 / η) * |s - t| := by
    rw [div_sub_div_same, abs_div, abs_of_pos hη]
    rw [show s - u + η - (t - u + η) = s - t by ring]
    field_simp
  have hg : |(v + η - s) / η - (v + η - t) / η| = (1 / η) * |s - t| := by
    rw [div_sub_div_same, abs_div, abs_of_pos hη]
    rw [show v + η - s - (v + η - t) = -(s - t) by ring, abs_neg]
    field_simp
  have hmin : |min ((s - u + η) / η) ((v + η - s) / η)
      - min ((t - u + η) / η) ((v + η - t) / η)| ≤ (1 / η) * |s - t| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [hf, hg, max_self]
  have hmin1 : |min 1 (min ((s - u + η) / η) ((v + η - s) / η))
      - min 1 (min ((t - u + η) / η) ((v + η - t) / η))| ≤ (1 / η) * |s - t| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simpa using hmin
  unfold trap
  rw [max_comm 0 _, max_comm 0 _]
  exact (abs_max_sub_max_le_abs _ _ _).trans hmin1



def perTrap (u v η : ℝ) (t : ℝ) : ℝ := trap u v η (Int.fract t)

theorem perTrap_periodic (u v η : ℝ) : Function.Periodic (perTrap u v η) 1 := by
  intro t
  unfold perTrap
  rw [show t + 1 = t + ((1 : ℤ) : ℝ) by norm_num, Int.fract_add_intCast]

theorem intDist_neg (θ : ℝ) : intDist (-θ) = intDist θ := by
  have h1 : intDist (-θ) ≤ intDist θ := by
    have := intDist_le_abs_sub_int (-θ) (-(round θ))
    rw [show |(-θ) - ((-(round θ) : ℤ) : ℝ)| = |θ - ((round θ : ℤ) : ℝ)| by
      push_cast
      rw [show -θ - -(round θ : ℝ) = -(θ - (round θ : ℝ)) by ring, abs_neg]] at this
    exact this
  have h2 : intDist θ ≤ intDist (-θ) := by
    have := intDist_le_abs_sub_int θ (-(round (-θ)))
    rw [show |θ - ((-(round (-θ)) : ℤ) : ℝ)| = |(-θ) - ((round (-θ) : ℤ) : ℝ)| by
      push_cast
      rw [show θ - -(round (-θ) : ℝ) = -((-θ) - (round (-θ) : ℝ)) by ring, abs_neg]] at this
    exact this
  linarith

theorem abs_perTrap_sub_perTrap_le {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1)
    (s t : ℝ) : |perTrap u v η s - perTrap u v η t| ≤ (1 / η) * |s - t| := by
  set p := Int.fract s with hp
  set q := Int.fract t with hq
  have hp0 : 0 ≤ p := Int.fract_nonneg s
  have hp1 : p < 1 := Int.fract_lt_one s
  have hq0 : 0 ≤ q := Int.fract_nonneg t
  have hq1 : q < 1 := Int.fract_lt_one t
  have hzero : trap u v η 0 = 0 := trap_eq_zero_of_le hη (by linarith)
  have hone : trap u v η 1 = 0 := trap_eq_zero_of_ge hη (by linarith)
  have hkey : |trap u v η p - trap u v η q| ≤ (1 / η) * min |p - q| (1 - |p - q|) := by
    rcases le_or_gt (|p - q|) (1 - |p - q|) with hcase | hcase
    · rw [min_eq_left hcase]
      exact abs_trap_sub_trap_le hη p q
    · rw [min_eq_right hcase.le]
      rcases le_total p q with hpq | hpq
      · have habs : |p - q| = q - p := by rw [abs_of_nonpos (by linarith)]; ring
        have hbound : |trap u v η p - trap u v η q|
            ≤ |trap u v η p - trap u v η 0| + |trap u v η 1 - trap u v η q| := by
          rw [hzero, hone]
          have : trap u v η p - trap u v η q = (trap u v η p - 0) + (0 - trap u v η q) := by ring
          rw [this]
          exact (abs_add_le _ _).trans (le_of_eq rfl)
        have h2 : |trap u v η p - trap u v η 0| ≤ (1 / η) * p := by
          have := abs_trap_sub_trap_le (u := u) (v := v) hη p 0
          simpa [abs_of_nonneg hp0] using this
        have h3 : |trap u v η 1 - trap u v η q| ≤ (1 / η) * (1 - q) := by
          have := abs_trap_sub_trap_le (u := u) (v := v) hη 1 q
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - q)] at this
          exact this
        rw [habs]
        have : (1 / η) * p + (1 / η) * (1 - q) = (1 / η) * (1 - (q - p)) := by ring
        linarith [hbound, h2, h3]
      · have habs : |p - q| = p - q := by rw [abs_of_nonneg (by linarith)]
        have hbound : |trap u v η p - trap u v η q|
            ≤ |trap u v η q - trap u v η 0| + |trap u v η 1 - trap u v η p| := by
          rw [hzero, hone]
          have : trap u v η p - trap u v η q = -((trap u v η q - 0) + (0 - trap u v η p)) := by ring
          rw [this, abs_neg]
          exact (abs_add_le _ _).trans (le_of_eq rfl)
        have h2 : |trap u v η q - trap u v η 0| ≤ (1 / η) * q := by
          have := abs_trap_sub_trap_le (u := u) (v := v) hη q 0
          simpa [abs_of_nonneg hq0] using this
        have h3 : |trap u v η 1 - trap u v η p| ≤ (1 / η) * (1 - p) := by
          have := abs_trap_sub_trap_le (u := u) (v := v) hη 1 p
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - p)] at this
          exact this
        rw [habs]
        have : (1 / η) * q + (1 / η) * (1 - p) = (1 / η) * (1 - (p - q)) := by ring
        linarith [hbound, h2, h3]
  have hdist : min |p - q| (1 - |p - q|) ≤ |s - t| := by
    have hle1 : |p - q| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hmin := min_le_intDist_of_unit (abs_nonneg (p - q)) hle1
    have habs : intDist |p - q| = intDist (p - q) := by
      rcases abs_choice (p - q) with h | h
      · rw [h]
      · rw [h, intDist_neg]
    have hshift : intDist (p - q) = intDist (s - t) := by
      have : s - t = (p - q) + (((⌊s⌋ - ⌊t⌋ : ℤ)) : ℝ) := by
        rw [hp, hq, Int.fract, Int.fract]
        push_cast
        ring
      rw [this, intDist_add_intCast]
    have hfin : intDist (s - t) ≤ |s - t| := by
      have := intDist_le_abs_sub_int (s - t) 0
      simpa using this
    rw [habs, hshift] at hmin
    linarith
  have hpos : (0 : ℝ) < 1 / η := by positivity
  unfold perTrap
  calc |trap u v η p - trap u v η q| ≤ (1 / η) * min |p - q| (1 - |p - q|) := hkey
    _ ≤ (1 / η) * |s - t| := by exact mul_le_mul_of_nonneg_left hdist hpos.le


theorem perTrap_nonneg (u v η t : ℝ) : 0 ≤ perTrap u v η t := trap_nonneg _ _ _ _

theorem perTrap_le_one (u v η t : ℝ) : perTrap u v η t ≤ 1 := trap_le_one _ _ _ _

theorem integral_perTrap (u v η : ℝ) :
    (∫ t in (0 : ℝ)..1, perTrap u v η t) = ∫ t in (0 : ℝ)..1, trap u v η t := by
  refine intervalIntegral.integral_congr_ae ?_
  have hcompl : ({(1 : ℝ)} : Set ℝ)ᶜ ∈ MeasureTheory.ae MeasureTheory.volume := by
    rw [MeasureTheory.mem_ae_iff]
    simp
  filter_upwards [hcompl] with t ht htmem
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at htmem
  have hne : t ≠ 1 := ht
  have hfract : Int.fract t = t :=
    Int.fract_eq_self.mpr ⟨htmem.1.le, lt_of_le_of_ne htmem.2 hne⟩
  unfold perTrap
  rw [hfract]

theorem integral_trap_le {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1)
    (huv : u ≤ v) : (∫ t in (0 : ℝ)..1, trap u v η t) ≤ (v - u) + 2 * η := by
  have h := integral_trapCirc_le hη h0 h1 huv
  rwa [integral_trapCirc_eq hη h0 h1] at h

theorem le_integral_trap {u v η : ℝ} (hη : 0 < η) (h0 : 0 < u - η) (h1 : v + η < 1)
    (huv : u ≤ v) : (v - u) ≤ ∫ t in (0 : ℝ)..1, trap u v η t := by
  have h := le_integral_trapCirc hη h0 h1 huv
  rwa [integral_trapCirc_eq hη h0 h1] at h

theorem countIn_le_sum_perTrap (x : ℕ → ℝ) {a b η : ℝ} (hη : 0 < η) (N : ℕ) :
    (countIn x a b N : ℝ) ≤ ∑ n ∈ range N, perTrap a b η (x n) := by
  rw [countIn_eq_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases h : a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
  · rw [if_pos h]
    unfold perTrap
    exact ge_of_eq (trap_eq_one hη h.1 h.2.le)
  · rw [if_neg h]
    exact perTrap_nonneg a b η (x n)

theorem sum_perTrap_le_countIn (x : ℕ → ℝ) {a b η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∑ n ∈ range N, perTrap (a + η) (b - η) η (x n) ≤ (countIn x a b N : ℝ) := by
  rw [countIn_eq_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases h : a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
  · rw [if_pos h]
    exact perTrap_le_one _ _ _ _
  · rw [if_neg h]
    unfold perTrap
    rcases not_and_or.mp h with hlt | hge
    · have : Int.fract (x n) ≤ (a + η) - η := by
        push Not at hlt
        linarith
      exact le_of_eq (trap_eq_zero_of_le hη this)
    · have : (b - η) + η ≤ Int.fract (x n) := by
        push Not at hge
        linarith
      exact le_of_eq (trap_eq_zero_of_ge hη this)


/-! ### The discrepancy bound -/

/-- **The discrepancy bound of Erdős–Turán type.** -/
theorem abs_countIn_div_sub_le (x : ℕ → ℝ) {a b η δ : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hη : 0 < η) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (ha : 0 < a - η) (hb : b + η < 1)
    (hab : a + 2 * η ≤ b) :
    |(countIn x a b N : ℝ) / N - (b - a)|
      ≤ 2 * η + δ / η + 1 / (2 * M * δ)
        + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set W : ℝ := 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1), ‖expSum x (m : ℤ) N‖ / N with hW
  have hup := abs_avg_sub_integral_le (g := perTrap a b η) (L := 1 / η) hM hN
    (fun t => perTrap_nonneg a b η t) (fun t => perTrap_le_one a b η t)
    (fun t => perTrap_periodic a b η t)
    (fun u v => abs_perTrap_sub_perTrap_le hη ha hb u v) hδ0 hδ x
  have hlow := abs_avg_sub_integral_le (g := perTrap (a + η) (b - η) η) (L := 1 / η) hM hN
    (fun t => perTrap_nonneg _ _ η t) (fun t => perTrap_le_one _ _ η t)
    (fun t => perTrap_periodic _ _ η t)
    (fun u v => abs_perTrap_sub_perTrap_le hη (by linarith) (by linarith) u v) hδ0 hδ x
  have hupint : (∫ t in (0 : ℝ)..1, perTrap a b η t) ≤ (b - a) + 2 * η := by
    rw [integral_perTrap]
    exact integral_trap_le hη ha hb (by linarith)
  have hlowint : (b - a) - 2 * η ≤ ∫ t in (0 : ℝ)..1, perTrap (a + η) (b - η) η t := by
    rw [integral_perTrap]
    have := le_integral_trap (u := a + η) (v := b - η) hη (by linarith) (by linarith)
      (by linarith)
    linarith
  have hcount_up : (countIn x a b N : ℝ) / N ≤ (∑ n ∈ range N, perTrap a b η (x n)) / N := by
    gcongr
    exact countIn_le_sum_perTrap x hη N
  have hcount_low : (∑ n ∈ range N, perTrap (a + η) (b - η) η (x n)) / N
      ≤ (countIn x a b N : ℝ) / N := by
    gcongr
    exact sum_perTrap_le_countIn x hη N
  have hup' := abs_le.mp hup
  have hlow' := abs_le.mp hlow
  have hδη : (1 / η) * δ = δ / η := by
    field_simp
  rw [abs_le]
  constructor
  · linarith [hcount_low, hlow'.1, hlowint]
  · linarith [hcount_up, hup'.2, hupint]

/-- The discrepancy bound with all parameters tied to a single one: `η = 1/K`, `δ = 1/K²`,
`M = K⁴`. -/
theorem abs_countIn_div_sub_le_pow (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K) (hN : 0 < N)
    (ha : 1 / (K : ℝ) < a) (hb : b + 1 / (K : ℝ) < 1) (hab : a + 2 / (K : ℝ) ≤ b) :
    |(countIn x a b N : ℝ) / N - (b - a)|
      ≤ 4 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1), ‖expSum x (m : ℤ) N‖ / N := by
  have hK0 : 0 < K := by omega
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hMpos : 0 < K ^ 4 := by positivity
  have hη : (0 : ℝ) < 1 / K := by positivity
  have hδ0 : (0 : ℝ) < 1 / (K : ℝ) ^ 2 := by positivity
  have hδ : (1 : ℝ) / (K : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmain := abs_countIn_div_sub_le x (a := a) (b := b) (η := 1 / (K : ℝ))
    (δ := 1 / (K : ℝ) ^ 2) (M := K ^ 4) (N := N) hMpos hN hη hδ0 hδ (by linarith)
    (by linarith) (by
      have : (2 : ℝ) / K = 2 * (1 / K) := by ring
      linarith [hab, this.le, this.ge])
  have hcast : ((K ^ 4 : ℕ) : ℝ) = (K : ℝ) ^ 4 := by push_cast; ring
  have harith : 2 * (1 / (K : ℝ)) + (1 / (K : ℝ) ^ 2) / (1 / (K : ℝ))
      + 1 / (2 * ((K ^ 4 : ℕ) : ℝ) * (1 / (K : ℝ) ^ 2)) ≤ 4 / K := by
    rw [hcast]
    have h1 : (1 / (K : ℝ) ^ 2) / (1 / (K : ℝ)) = 1 / K := by
      field_simp
    have h2 : 1 / (2 * (K : ℝ) ^ 4 * (1 / (K : ℝ) ^ 2)) = 1 / (2 * (K : ℝ) ^ 2) := by
      field_simp
    rw [h1, h2]
    have h3 : 1 / (2 * (K : ℝ) ^ 2) ≤ 1 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have hsum4 : 2 * (1 / (K : ℝ)) + 1 / K + 1 / K = 4 / K := by field_simp; ring
    linarith
  linarith [hmain, harith]

/-! ### An explicit rate for a badly approximable linear sequence -/

/-- For a badly approximable `α` the exponential sums of `α n` at frequency `m` are at most
`m/(2c)`. -/
theorem norm_expSum_linear_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ ≤ m / (2 * c) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : c / m ≤ intDist ((m : ℝ) * α) := hbad m hm
  have hdpos : 0 < intDist ((m : ℝ) * α) := lt_of_lt_of_le (by positivity) hd
  have hne : intDist ((m : ℝ) * α) ≠ 0 := hdpos.ne'
  have hsum : expSum (fun n : ℕ => α * n) (m : ℤ) N
      = ∑ n ∈ range N, e2pi (((m : ℝ) * α) * (n : ℝ) + 0) := by
    unfold expSum
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  rw [hsum]
  calc ‖∑ n ∈ range N, e2pi (((m : ℝ) * α) * (n : ℝ) + 0)‖
      ≤ 1 / (2 * intDist ((m : ℝ) * α)) := norm_geomSum_e2pi_le hne N 0
    _ ≤ m / (2 * c) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : c ≤ (m : ℝ) * intDist ((m : ℝ) * α) := by
          rw [div_le_iff₀ hmpos] at hd
          linarith
        nlinarith

/-- **An explicit rate.**  For `α` badly approximable the discrepancy of `α n` on an interval is
`O(N^(−1/9))`: it is at most `(4 + 1/c)/K` as soon as `K⁹ ≤ N`. -/
theorem abs_countIn_div_sub_le_linear {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ intDist ((m : ℝ) * α)) {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K)
    (hNK : K ^ 9 ≤ N) (ha : 1 / (K : ℝ) < a) (hb : b + 1 / (K : ℝ) < 1)
    (hab : a + 2 / (K : ℝ) ≤ b) :
    |(countIn (fun n : ℕ => α * n) a b N : ℝ) / N - (b - a)| ≤ (4 + 1 / c) / K := by
  have hK0 : 0 < K := by omega
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNK
  have hNR : ((K : ℝ)) ^ 9 ≤ N := by exact_mod_cast hNK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmain := abs_countIn_div_sub_le_pow (fun n : ℕ => α * n) hK hN ha hb hab
  have hsum : ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
      ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N ≤ 1 / (2 * c * K) := by
    have hterm : ∀ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
        ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N ≤ ((K : ℝ) ^ 4) / (2 * c) / N := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have h1 := norm_expSum_linear_le hc hbad hm.1 N
      have h2 : (m : ℝ) ≤ (K : ℝ) ^ 4 := by
        have : m ≤ K ^ 4 := le_trans hm.2 (Nat.sub_le _ _)
        exact_mod_cast this
      have h3 : ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ ≤ ((K : ℝ) ^ 4) / (2 * c) := by
        refine le_trans h1 ?_
        gcongr
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
      _ = ((K : ℝ) ^ 8) / (2 * c * N) := by
          field_simp
      _ ≤ 1 / (2 * c * K) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h9 : (K : ℝ) ^ 9 ≤ N := hNR
          nlinarith [pow_pos hKpos 8, hc, sq_nonneg ((K : ℝ) ^ 4)]
  have hfin : (4 : ℝ) / K + 2 * (1 / (2 * c * K)) = (4 + 1 / c) / K := by
    field_simp
  calc |(countIn (fun n : ℕ => α * n) a b N : ℝ) / N - (b - a)|
      ≤ 4 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
          ‖expSum (fun n : ℕ => α * n) (m : ℤ) N‖ / N := hmain
    _ ≤ 4 / K + 2 * (1 / (2 * c * K)) := by linarith [hsum]
    _ = (4 + 1 / c) / K := hfin

end WeylDiscrepancy

end RiemannHypothesis
