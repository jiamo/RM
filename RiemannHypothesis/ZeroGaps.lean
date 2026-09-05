/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroOrdinate

/-!
# The gaps between consecutive zero ordinates

`RiemannHypothesis.ZeroOrdinate` defines the ordinate `γ_n = nthZeroOrdinate n` of the `n`-th
zero of `ζ` in the upper half plane, counted with multiplicity, and proves
`γ_n ~ 2π n / log n`.  This file records what that asymptotic says about the *gaps*

`zeroGap n = γ_{n+1} − γ_n`.

The gaps are non-negative and telescope: `∑_{n < N} zeroGap n = γ_N`, because `γ_0 = 0`.  Since
`γ_N / N → 0`, the average gap tends to `0`; and since the weighted average
`(1/N) ∑_{n < N} (γ_{n+1} − γ_n) log γ_n` is at most `γ_N log γ_N / N → 2π`, the normalized gap
`(γ_{n+1} − γ_n) log γ_n` is smaller than `2π + ε` for infinitely many `n` — the classical
statement `liminf (γ_{n+1} − γ_n) log γ_n ≤ 2π`, i.e. that infinitely many gaps are no larger
than the average gap `2π / log γ_n`.

The matching lower bound `limsup (γ_{n+1} − γ_n) log γ_n ≥ 2π` comes from the elementary
inequality `h(b) − h(a) ≤ (b − a) log b` for `h(x) = x log x − x` and `0 ≤ a ≤ b`, which
telescopes to `∑_{n < N} (γ_{n+1} − γ_n) log γ_{n+1} ≥ γ_N log γ_N − γ_N`, a quantity that is
again `(2π + o(1)) N`; the weight `log γ_{n+1}` is then traded for `log γ_n` using
`log γ_{n+1} / log γ_n → 1`.

## Main results

* `monotone_nthZeroOrdinate`, `zeroGap_nonneg` — the ordinates increase.
* `nthZeroOrdinate_zero`, `sum_zeroGap` — `γ_0 = 0` and the telescoping identity.
* `tendsto_nthZeroOrdinate_div_nat` — `γ_n / n → 0`.
* `tendsto_avg_zeroGap` — the average gap tends to `0`.
* `infinite_setOf_zeroGap_lt` — for every `ε > 0` infinitely many gaps are smaller than `ε`.
* `infinite_setOf_zeroGap_mul_log_lt` — **`liminf (γ_{n+1} − γ_n) log γ_n ≤ 2π`**: for every
  `ε > 0` infinitely many `n` satisfy `(γ_{n+1} − γ_n) log γ_n < 2π + ε`.
* `tendsto_log_nthZeroOrdinate_succ_div` — `log γ_{n+1} / log γ_n → 1`.
* `infinite_setOf_zeroGap_mul_log_gt` — **`limsup (γ_{n+1} − γ_n) log γ_n ≥ 2π`**: for every
  `ε > 0` infinitely many `n` satisfy `(γ_{n+1} − γ_n) log γ_n > 2π − ε`.
-/

noncomputable section

open Filter Real Set

open scoped Topology

namespace RiemannHypothesis

/-- The gap between the ordinates of the `n`-th and the `(n+1)`-st zero. -/
def zeroGap (n : ℕ) : ℝ := nthZeroOrdinate (n + 1) - nthZeroOrdinate n

lemma nthOrdinateSet_subset {n m : ℕ} (h : n ≤ m) : nthOrdinateSet m ⊆ nthOrdinateSet n :=
  fun _ hT => ⟨hT.1, le_trans h hT.2⟩

lemma monotone_nthZeroOrdinate : Monotone nthZeroOrdinate := fun _ _ h =>
  csInf_le_csInf (nthOrdinateSet_bddBelow _) (nthOrdinateSet_nonempty _)
    (nthOrdinateSet_subset h)

lemma zeroGap_nonneg (n : ℕ) : 0 ≤ zeroGap n :=
  sub_nonneg.2 (monotone_nthZeroOrdinate (Nat.le_succ n))

/-- The counting function has "reached `0`" at every height, so `γ_0 = 0`. -/
lemma nthZeroOrdinate_zero : nthZeroOrdinate 0 = 0 := by
  have hset : nthOrdinateSet 0 = Ici (0 : ℝ) := by
    ext T
    simp [nthOrdinateSet]
  rw [nthZeroOrdinate, hset, csInf_Ici]

/-- The gaps telescope. -/
lemma sum_zeroGap (N : ℕ) : ∑ n ∈ Finset.range N, zeroGap n = nthZeroOrdinate N := by
  simpa [zeroGap, nthZeroOrdinate_zero] using
    Finset.sum_range_sub (f := nthZeroOrdinate) (n := N)

/-- `γ_n / n → 0`: the ordinates grow strictly more slowly than `n`. -/
theorem tendsto_nthZeroOrdinate_div_nat :
    Tendsto (fun n : ℕ => nthZeroOrdinate n / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) := hlog.inv_tendsto_atTop
  have h := tendsto_nthZeroOrdinate_mul_log_nat_div.mul hinv
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn1)
  field_simp

/-- **The average gap tends to `0`.** -/
theorem tendsto_avg_zeroGap :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, zeroGap n) / N) atTop (𝓝 0) := by
  simpa [sum_zeroGap] using tendsto_nthZeroOrdinate_div_nat

/-- If the partial averages of a sequence are eventually at most `L`, and `L < c`, then
`f n < c` for infinitely many `n`. -/
private lemma infinite_setOf_lt_of_avg_le {f : ℕ → ℝ} {c L : ℝ} (hLc : L < c)
    (hbound : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.range N, f n) / N ≤ L) :
    {n : ℕ | f n < c}.Infinite := by
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  set N₀ : ℕ := b + 1 with hN₀
  have hge : ∀ n, N₀ ≤ n → c ≤ f n := by
    intro n hn
    by_contra hcon
    exact absurd (hb (not_le.1 hcon : f n < c)) (by omega)
  set K : ℝ := ∑ n ∈ Finset.range N₀, f n with hK
  -- for `M ≥ N₀` the partial sum is at least `K + c (M − N₀)`
  have hlower : ∀ M : ℕ, N₀ ≤ M → K + c * ((M : ℝ) - N₀) ≤ ∑ n ∈ Finset.range M, f n := by
    intro M hM
    have hsplit : (∑ n ∈ Finset.range N₀, f n) + (∑ n ∈ Finset.Ico N₀ M, f n)
        = ∑ n ∈ Finset.range M, f n := by
      simp only [Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive f (Nat.zero_le _) hM
    have h1 : ∑ _n ∈ Finset.Ico N₀ M, c ≤ ∑ n ∈ Finset.Ico N₀ M, f n :=
      Finset.sum_le_sum fun n hn => hge n (Finset.mem_Ico.1 hn).1
    have h3 : ∑ _n ∈ Finset.Ico N₀ M, c = ((M : ℝ) - N₀) * c := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hM]
    rw [h3] at h1
    rw [← hsplit, ← hK]
    linarith [h1]
  -- hence the averages are at least `K/M + c (1 − N₀/M)`, whose limit is `c`
  have hlim : Tendsto (fun M : ℕ => K / M + c * (1 - (N₀ : ℝ) / M)) atTop (𝓝 c) := by
    have hK0 : Tendsto (fun M : ℕ => K / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h0 : Tendsto (fun M : ℕ => (N₀ : ℝ) / M) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Tendsto (fun M : ℕ => c * (1 - (N₀ : ℝ) / M)) atTop (𝓝 c) := by
      have h2 : Tendsto (fun M : ℕ => (1 : ℝ) - (N₀ : ℝ) / M) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at h2
      simpa using h2.const_mul c
    simpa using hK0.add h1
  have hev : ∀ᶠ M : ℕ in atTop, K / M + c * (1 - (N₀ : ℝ) / M) ≤ L := by
    filter_upwards [hbound, eventually_ge_atTop N₀, eventually_gt_atTop 0] with M hM hMN hM0
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
    have h := hlower M hMN
    have hdiv : (K + c * ((M : ℝ) - N₀)) / M ≤ L := le_trans (by gcongr) hM
    calc K / M + c * (1 - (N₀ : ℝ) / M) = (K + c * ((M : ℝ) - N₀)) / M := by
          field_simp
      _ ≤ L := hdiv
  exact absurd (le_of_tendsto hlim hev) (not_le.2 hLc)

/-- **Infinitely many gaps are arbitrarily small.** -/
theorem infinite_setOf_zeroGap_lt {ε : ℝ} (hε : 0 < ε) : {n : ℕ | zeroGap n < ε}.Infinite := by
  refine infinite_setOf_lt_of_avg_le (L := ε / 2) (by linarith) ?_
  have h := tendsto_avg_zeroGap.eventually
    (eventually_le_nhds (show (0 : ℝ) < ε / 2 by linarith))
  filter_upwards [h] with N hN using hN

/-- The weighted partial sums of the gaps are bounded by `γ_N log γ_N`. -/
lemma sum_zeroGap_mul_log_le {N : ℕ} (hN : 1 ≤ nthZeroOrdinate N) :
    ∑ n ∈ Finset.range N, zeroGap n * Real.log (nthZeroOrdinate n)
      ≤ nthZeroOrdinate N * Real.log (nthZeroOrdinate N) := by
  have hstep : ∀ n ∈ Finset.range N,
      zeroGap n * Real.log (nthZeroOrdinate n)
        ≤ zeroGap n * Real.log (nthZeroOrdinate N) := by
    intro n hn
    have hle : nthZeroOrdinate n ≤ nthZeroOrdinate N :=
      monotone_nthZeroOrdinate (Finset.mem_range.1 hn).le
    have hlog : Real.log (nthZeroOrdinate n) ≤ Real.log (nthZeroOrdinate N) := by
      rcases eq_or_lt_of_le (nthZeroOrdinate_nonneg n) with h0 | h0
      · rw [← h0, Real.log_zero]
        exact Real.log_nonneg hN
      · exact Real.log_le_log h0 hle
    exact mul_le_mul_of_nonneg_left hlog (zeroGap_nonneg n)
  calc ∑ n ∈ Finset.range N, zeroGap n * Real.log (nthZeroOrdinate n)
      ≤ ∑ n ∈ Finset.range N, zeroGap n * Real.log (nthZeroOrdinate N) :=
        Finset.sum_le_sum hstep
    _ = (∑ n ∈ Finset.range N, zeroGap n) * Real.log (nthZeroOrdinate N) := by
        rw [Finset.sum_mul]
    _ = nthZeroOrdinate N * Real.log (nthZeroOrdinate N) := by rw [sum_zeroGap]

/-- **`liminf (γ_{n+1} − γ_n) log γ_n ≤ 2π`.**  Infinitely many gaps are no larger than the
average gap `2π / log γ_n`, up to an arbitrarily small relative error. -/
theorem infinite_setOf_zeroGap_mul_log_lt {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | zeroGap n * Real.log (nthZeroOrdinate n) < 2 * Real.pi + ε}.Infinite := by
  refine infinite_setOf_lt_of_avg_le (L := 2 * Real.pi + ε / 2) (by linarith) ?_
  have hmain := tendsto_nthZeroOrdinate_mul_log_div_nat
  have hsmall : ∀ᶠ N : ℕ in atTop,
      nthZeroOrdinate N * Real.log (nthZeroOrdinate N) / N ≤ 2 * Real.pi + ε / 2 :=
    hmain.eventually
      (eventually_le_nhds (show 2 * Real.pi < 2 * Real.pi + ε / 2 by linarith))
  filter_upwards [hsmall, tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop 0] with N hN hγ hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  exact le_trans (by gcongr; exact sum_zeroGap_mul_log_le hγ) hN

/-- The elementary inequality behind the lower bound for the weighted sums: for `0 ≤ a ≤ b`,
`h(b) − h(a) ≤ (b − a) log b`, where `h(x) = x log x − x`. -/
private lemma sub_mul_log_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b * Real.log b - b) - (a * Real.log a - a) ≤ (b - a) * Real.log b := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · have hb : 0 ≤ b := le_trans ha hab
    simp only [← h0, Real.log_zero, zero_mul, sub_zero]
    linarith
  · have hb : 0 < b := lt_of_lt_of_le h0 hab
    -- `a log (a/b) ≥ a − b`, from `log (b/a) ≤ b/a − 1`
    have hkey : Real.log b - Real.log a ≤ b / a - 1 := by
      have h := Real.log_le_sub_one_of_pos (x := b / a) (by positivity)
      rwa [Real.log_div (ne_of_gt hb) (ne_of_gt h0)] at h
    have hmul : a * (Real.log b - Real.log a) ≤ b - a := by
      have := mul_le_mul_of_nonneg_left hkey h0.le
      calc a * (Real.log b - Real.log a) ≤ a * (b / a - 1) := this
        _ = b - a := by field_simp
    nlinarith [hmul]

/-- The weighted partial sums of the gaps are at least `γ_N log γ_N − γ_N`. -/
lemma le_sum_zeroGap_mul_log_succ (N : ℕ) :
    nthZeroOrdinate N * Real.log (nthZeroOrdinate N) - nthZeroOrdinate N
      ≤ ∑ n ∈ Finset.range N, zeroGap n * Real.log (nthZeroOrdinate (n + 1)) := by
  have htel : ∑ n ∈ Finset.range N,
      ((nthZeroOrdinate (n + 1) * Real.log (nthZeroOrdinate (n + 1)) - nthZeroOrdinate (n + 1))
        - (nthZeroOrdinate n * Real.log (nthZeroOrdinate n) - nthZeroOrdinate n))
      = (nthZeroOrdinate N * Real.log (nthZeroOrdinate N) - nthZeroOrdinate N)
        - (nthZeroOrdinate 0 * Real.log (nthZeroOrdinate 0) - nthZeroOrdinate 0) :=
    Finset.sum_range_sub (fun n => nthZeroOrdinate n * Real.log (nthZeroOrdinate n)
      - nthZeroOrdinate n) N
  rw [nthZeroOrdinate_zero] at htel
  simp only [Real.log_zero, mul_zero, sub_zero, sub_self] at htel
  rw [← htel]
  refine Finset.sum_le_sum fun n _ => ?_
  exact sub_mul_log_le_of_le (nthZeroOrdinate_nonneg n)
    (monotone_nthZeroOrdinate (Nat.le_succ n))

/-- The dual of `infinite_setOf_lt_of_avg_le`: if the partial averages of `f` are eventually at
least `L`, and `c < L`, then `c < f n` for infinitely many `n`. -/
private lemma infinite_setOf_gt_of_avg_ge {f : ℕ → ℝ} {c L : ℝ} (hcL : c < L)
    (hbound : ∀ᶠ N : ℕ in atTop, L ≤ (∑ n ∈ Finset.range N, f n) / N) :
    {n : ℕ | c < f n}.Infinite := by
  have h := infinite_setOf_lt_of_avg_le (f := fun n => -f n) (c := -c) (L := -L)
    (by linarith) ?_
  · simpa using h
  · filter_upwards [hbound] with N hN
    rw [Finset.sum_neg_distrib, neg_div]
    linarith

/-- **`limsup (γ_{n+1} − γ_n) log γ_{n+1} ≥ 2π`.**  Infinitely many gaps are at least as large as
the average gap `2π / log γ_{n+1}`, up to an arbitrarily small relative error. -/
theorem infinite_setOf_zeroGap_mul_log_succ_gt {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | 2 * Real.pi - ε < zeroGap n * Real.log (nthZeroOrdinate (n + 1))}.Infinite := by
  refine infinite_setOf_gt_of_avg_ge (L := 2 * Real.pi - ε / 2) (by linarith) ?_
  have hmain := tendsto_nthZeroOrdinate_mul_log_div_nat
  have hdiv : Tendsto (fun N : ℕ => nthZeroOrdinate N / N) atTop (𝓝 0) :=
    tendsto_nthZeroOrdinate_div_nat
  have hsub : Tendsto (fun N : ℕ =>
      nthZeroOrdinate N * Real.log (nthZeroOrdinate N) / N - nthZeroOrdinate N / N) atTop
      (𝓝 (2 * Real.pi - 0)) := hmain.sub hdiv
  rw [sub_zero] at hsub
  have hev := hsub.eventually
    (eventually_ge_nhds (show 2 * Real.pi - ε / 2 < 2 * Real.pi by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hle := le_sum_zeroGap_mul_log_succ N
  have : nthZeroOrdinate N * Real.log (nthZeroOrdinate N) / N - nthZeroOrdinate N / N
      ≤ (∑ n ∈ Finset.range N, zeroGap n * Real.log (nthZeroOrdinate (n + 1))) / N := by
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hNpos]
    exact hle
  linarith

/-- `log γ_{n+1} / log γ_n → 1`: consecutive ordinates have asymptotically equal logarithms. -/
lemma tendsto_log_nthZeroOrdinate_succ_div :
    Tendsto (fun n : ℕ => Real.log (nthZeroOrdinate (n + 1)) / Real.log (nthZeroOrdinate n))
      atTop (𝓝 1) := by
  -- `log (n+1) / log n → 1`
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  have hd : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) - Real.log n) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun n : ℕ => Real.log (((n : ℝ) + 1) / n)) atTop (𝓝 (Real.log 1)) :=
      ((Real.continuousAt_log one_ne_zero).tendsto).comp hratio
    rw [Real.log_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.log_div (by positivity) (ne_of_gt hn0)]
  have hsucc : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.log n) atTop (𝓝 1) := by
    have h := hd.div_atTop hlogn
    have h1 : Tendsto (fun n : ℕ =>
        1 + (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlogne : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn1)
    field_simp
    ring
  -- combine with `log γ_n / log n → 1`, shifted and unshifted
  have hA : Tendsto
      (fun n : ℕ => Real.log (nthZeroOrdinate (n + 1)) / Real.log ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have h := tendsto_log_nthZeroOrdinate_div_log_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp [Function.comp]
  have hB := tendsto_log_nat_div_log_nthZeroOrdinate
  have hprod := (hA.mul hsucc).mul hB
  simp only [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 2,
    tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ)] with n hn hγ
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogne : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn1)
  have hn1' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogne1 : Real.log ((n : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hlogγ : Real.log (nthZeroOrdinate n) ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  field_simp

/-- The `limsup` statement for small `ε`. -/
private lemma infinite_setOf_zeroGap_mul_log_gt_aux {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ Real.pi) :
    {n : ℕ | 2 * Real.pi - ε < zeroGap n * Real.log (nthZeroOrdinate n)}.Infinite := by
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  set N₀ : ℕ := b + 1 with hN₀
  have hle : ∀ n, N₀ ≤ n → zeroGap n * Real.log (nthZeroOrdinate n) ≤ 2 * Real.pi - ε := by
    intro n hn
    by_contra hcon
    exact absurd (hb (not_le.1 hcon)) (by omega)
  have hposε : 0 < 2 * Real.pi - ε := by
    have := Real.pi_pos
    linarith
  set δ : ℝ := ε / (4 * (2 * Real.pi - ε)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- eventually `log γ_{n+1} ≤ (1 + δ) log γ_n`
  have hclose : ∀ᶠ n : ℕ in atTop,
      Real.log (nthZeroOrdinate (n + 1)) ≤ (1 + δ) * Real.log (nthZeroOrdinate n) := by
    have h := tendsto_log_nthZeroOrdinate_succ_div.eventually
      (eventually_le_nhds (show (1 : ℝ) < 1 + δ by linarith))
    filter_upwards [h, tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ)] with n hn hγ
    have hlogγ : 0 < Real.log (nthZeroOrdinate n) := Real.log_pos (by linarith)
    rwa [div_le_iff₀ hlogγ] at hn
  -- so the gaps weighted by `log γ_{n+1}` are eventually below `2π − ε/2`
  have hcontra : ∀ᶠ n : ℕ in atTop,
      zeroGap n * Real.log (nthZeroOrdinate (n + 1)) ≤ 2 * Real.pi - ε / 2 := by
    filter_upwards [hclose, eventually_ge_atTop N₀,
      tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ)] with n hn hnN hγ
    have hgap : 0 ≤ zeroGap n := zeroGap_nonneg n
    have h1 : zeroGap n * Real.log (nthZeroOrdinate (n + 1))
        ≤ zeroGap n * ((1 + δ) * Real.log (nthZeroOrdinate n)) :=
      mul_le_mul_of_nonneg_left hn hgap
    have h2 : zeroGap n * ((1 + δ) * Real.log (nthZeroOrdinate n))
        = (1 + δ) * (zeroGap n * Real.log (nthZeroOrdinate n)) := by ring
    have h3 : (1 + δ) * (zeroGap n * Real.log (nthZeroOrdinate n))
        ≤ (1 + δ) * (2 * Real.pi - ε) :=
      mul_le_mul_of_nonneg_left (hle n hnN) (by linarith)
    have h4 : (1 + δ) * (2 * Real.pi - ε) = 2 * Real.pi - ε + ε / 4 := by
      rw [hδ]; field_simp
    linarith
  -- but infinitely many `n` violate that bound
  have hinf := infinite_setOf_zeroGap_mul_log_succ_gt (ε := ε / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hcontra
  refine absurd hinf (Set.not_infinite.2 (Set.Finite.subset (Set.finite_Iio N₁) fun n hn => ?_))
  simp only [Set.mem_ofPred_eq] at hn
  by_contra hcon
  exact absurd (hN₁ n (not_lt.1 hcon)) (not_le.2 hn)

/-- **`limsup (γ_{n+1} − γ_n) log γ_n ≥ 2π`**, with the standard normalization: for every
`ε > 0` there are infinitely many `n` with `(γ_{n+1} − γ_n) log γ_n > 2π − ε`. -/
theorem infinite_setOf_zeroGap_mul_log_gt {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | 2 * Real.pi - ε < zeroGap n * Real.log (nthZeroOrdinate n)}.Infinite := by
  rcases le_or_gt ε Real.pi with hsmall | hbig
  · exact infinite_setOf_zeroGap_mul_log_gt_aux hε hsmall
  · refine Set.Infinite.mono (s := {n : ℕ | 2 * Real.pi - Real.pi
      < zeroGap n * Real.log (nthZeroOrdinate n)}) (fun n hn => ?_)
      (infinite_setOf_zeroGap_mul_log_gt_aux Real.pi_pos le_rfl)
    simp only [Set.mem_ofPred_eq] at hn ⊢
    linarith

end RiemannHypothesis
