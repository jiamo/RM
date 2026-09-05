/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylQuadraticQuantitative
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The counting lemma of Weyl's method, and the exponent `1/2` for a quadratic sum

`RiemannHypothesis.WeylQuadraticQuantitative` proves Weyl's inequality for the phase `α n²` with
the diophantine input supplied in its classical form, but it uses only the crude bound
`‖2αk‖ ≥ 1/(2q)`, valid for `2k ≤ q`, and therefore has to stop the differencing at `H = q/2`.
The resulting exponent is `3/4`.  The classical exponent `1/2` needs the *counting lemma*

  `∑_{k ≤ H} min(N, 1/‖βk‖) ≪ (H/q + 1)(N + q log q)`,

which is what this file proves, and then applies.

## The counting lemma

It is stated for an arbitrary majorant: if `g : ℤ → ℝ` satisfies `0 ≤ g k ≤ N` and
`g k · 2‖βk‖ ≤ 1` — the two properties of `min(N, 1/(2‖βk‖))`, written so that no convention for
`1/0` is needed — then, whenever `|β − a/q| ≤ 1/q²` with `a` and `q` coprime,

* `sum_block_le` — over a block of `q` consecutive integers, `∑ g k ≤ 4N + q(1 + log q)`;
* `sum_Ioc_le` — hence `∑_{0 < k ≤ H} g k ≤ (H/q + 1)(4N + q(1 + log q))`.

The proof of the block bound is the classical one.  Write `β = a/q + θ` with `|θ| ≤ 1/q²`.  On a
block `k = x + r`, `1 ≤ r ≤ q`, the perturbation `θ r` is at most `1/q` in absolute value, so
`‖βk‖ ≥ ‖βx + ar/q‖ − 1/q`, and since `a` is invertible modulo `q` the numbers `βx + ar/q` run,
as `r` runs over the block, through the `q` points of an arithmetic progression of step `1/q`
that covers the circle exactly once (`gridIndex`, `grid_sub_le_intDist`, `gridIndex_injOn`).  All
but four of those points are at distance at least `2/q` from the integers, and the `m`-th closest
is at distance at least `(m−1)/q`, so the sum of the reciprocals is a harmonic sum, at most
`q(1 + log q)`; the four exceptional points are bounded by `N`.

## The Weyl bound

Feeding the counting lemma into the differencing inequality of
`RiemannHypothesis.WeylDifferencing` with `H = N` gives, for `|2α − a/q| ≤ 1/q²` with `a`, `q`
coprime,

* `normSq_quadSum_le_of_approx_count` —
  `‖∑_{n<N} e(α n²)‖² ≤ 2N + 4(N/q + 1)(4N + q(1 + log q))`,

the classical shape `N²(1/q + 1/N + q/N²)`, up to logarithms; and for a denominator `N ≤ q ≤ 2N`
— the interesting case, `α` not close to a rational with small denominator —

* `normSq_quadSum_le_of_approx_large` — `‖∑_{n<N} e(α n²)‖² ≤ 66 N (1 + log (2N))`,

which is square-root cancellation: the exponent `1/2` up to a logarithm, in place of the exponent
`3/4` of `RiemannHypothesis.WeylQuadraticQuantitative`.

## Scope

Everything here is about exponential sums; nothing about `ζ` follows.  As it must be, the bound is
conditional on the existence of a rational approximation with a *large* denominator: for `α` close
to a rational with small denominator the sum has no cancellation at all.  The constants are not
optimized and the logarithm is not removed.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylQuadratic

open KusminLandau WeylDifferencing

/-! ## Two elementary estimates -/

/-- The harmonic sum, in the form used below. -/
theorem sum_range_inv_succ_le (n : ℕ) : ∑ j ∈ range n, ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log n := by
  have hh : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ range n, ((j : ℝ) + 1)⁻¹ := by simp [harmonic]
  have h := harmonic_le_one_add_log n
  rwa [hh] at h

/-- `log (q - c) ≤ log q`, with the truncated subtraction of `ℕ`. -/
theorem log_natSub_le {q : ℕ} (hq : 0 < q) (c : ℕ) : Real.log ((q - c : ℕ) : ℝ) ≤ Real.log q := by
  rcases Nat.eq_zero_or_pos (q - c) with h | h
  · rw [h]
    simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hq)
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.sub_le q c)

/-! ## The grid -/

/-- The distance to the nearest integer is `1`-periodic. -/
theorem intDist_add_intCast (θ : ℝ) (n : ℤ) : intDist (θ + n) = intDist θ := by
  unfold intDist
  rw [round_add_intCast]
  push_cast
  ring_nf

/-- For `v` in `[0,1]` the distance to the nearest integer is at least `min v (1 - v)`. -/
theorem min_le_intDist_of_unit {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : min v (1 - v) ≤ intDist v := by
  have key : ∀ m : ℤ, min v (1 - v) ≤ |v - m| := by
    intro m
    rcases le_or_gt m 0 with hm | hm
    · have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast hm
      exact le_trans (min_le_left _ _) (by rw [abs_of_nonneg (by linarith)]; linarith)
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      exact le_trans (min_le_right _ _) (by rw [abs_of_nonpos (by linarith)]; linarith)
  exact key (round v)

/-- The `i`-th point of the grid `(i + f)/q`, `0 ≤ i < q`, `0 ≤ f < 1`, is at distance at least
`min (i, q - 1 - i)/q` from the integers. -/
theorem grid_le_intDist {q i : ℕ} (hq : 0 < q) (hi : i < q) {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) :
    min ((i : ℝ) / q) (((q : ℝ) - 1 - i) / q) ≤ intDist (((i : ℝ) + f) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hiR : (i : ℝ) ≤ (q : ℝ) - 1 := by
    have : (i : ℝ) + 1 ≤ q := by exact_mod_cast hi
    linarith
  have h0 : (0 : ℝ) ≤ ((i : ℝ) + f) / q := by positivity
  have h1 : ((i : ℝ) + f) / q ≤ 1 := by rw [div_le_one hqR]; linarith
  refine le_trans ?_ (min_le_intDist_of_unit h0 h1)
  apply min_le_min
  · rw [div_le_div_iff_of_pos_right hqR]; linarith
  · have hrw : (1 : ℝ) - ((i : ℝ) + f) / q = ((q : ℝ) - i - f) / q := by field_simp; ring
    rw [hrw, div_le_div_iff_of_pos_right hqR]
    linarith

/-- The index of the block element `k` on the grid: the residue of `⌊βxq⌋ + a(k − x)` mod `q`. -/
def gridIndex (β : ℝ) (a : ℤ) (q : ℕ) (x k : ℤ) : ℕ :=
  ((⌊β * x * q⌋ + a * (k - x)) % (q : ℤ)).toNat

theorem gridIndex_lt {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (x k : ℤ) : gridIndex β a q x k < q := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have h := Int.emod_lt_of_pos (⌊β * x * q⌋ + a * (k - x)) hq'
  have h0 := Int.emod_nonneg (⌊β * x * q⌋ + a * (k - x)) (ne_of_gt hq')
  unfold gridIndex
  omega

/-- **The grid bound.**  For `k` in a block of `q` consecutive integers the distance of `βk` to the
integers is at least the distance of the corresponding grid point, less `1/q`. -/
theorem grid_sub_le_intDist {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (x k : ℤ) (hk1 : x < k) (hk2 : k ≤ x + q) :
    min ((gridIndex β a q x k : ℝ) / q) (((q : ℝ) - 1 - gridIndex β a q x k) / q) - 1 / q
      ≤ intDist (β * k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  set f : ℝ := β * x * q - ⌊β * x * q⌋ with hf
  have hf0 : 0 ≤ f := by have := Int.floor_le (β * x * q); simp only [hf]; linarith
  have hf1 : f < 1 := by have := Int.lt_floor_add_one (β * x * q); simp only [hf]; linarith
  set i : ℕ := gridIndex β a q x k with hi
  have hilt : i < q := gridIndex_lt hq x k
  set m : ℤ := ⌊β * x * q⌋ + a * (k - x) with hm
  have hi' : (i : ℤ) = m % (q : ℤ) := by
    have h0 := Int.emod_nonneg m (ne_of_gt hq')
    simp only [hi, gridIndex, ← hm]
    omega
  have hiR : ((i : ℕ) : ℝ) = ((m % (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hi'
  have hgrid : β * x + (a : ℝ) * ((k : ℝ) - x) / q
      = ((i : ℝ) + f) / q + ((m / (q : ℤ) : ℤ) : ℝ) := by
    have hdiv : (q : ℤ) * (m / (q : ℤ)) + m % (q : ℤ) = m := Int.mul_ediv_add_emod m (q : ℤ)
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdiv
    push_cast at h
    have hmdef : (m : ℝ) = (⌊β * x * q⌋ : ℝ) + (a : ℝ) * ((k : ℝ) - x) := by
      simp only [hm]; push_cast; ring
    have hxq : (⌊β * x * q⌋ : ℝ) = β * x * q - f := by simp only [hf]; ring
    rw [hiR]
    field_simp
    nlinarith [h, hmdef, hxq]
  have hpert : |β * k - (β * x + (a : ℝ) * ((k : ℝ) - x) / q)| ≤ 1 / q := by
    have hrpos : (0 : ℝ) < ((k : ℝ) - x) := by
      have : (x : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      linarith
    have hrq' : ((k : ℝ) - x) ≤ q := by
      have : (k : ℝ) ≤ (x : ℝ) + q := by exact_mod_cast hk2
      linarith
    have hdiff : β * k - (β * x + (a : ℝ) * ((k : ℝ) - x) / q)
        = (β - (a : ℝ) / q) * ((k : ℝ) - x) := by field_simp; ring
    rw [hdiff, abs_mul, abs_of_pos hrpos]
    calc |β - (a : ℝ) / q| * ((k : ℝ) - x) ≤ (1 / (q : ℝ) ^ 2) * q :=
          mul_le_mul happ hrq' (le_of_lt hrpos) (by positivity)
      _ = 1 / q := by field_simp
  have hdist : intDist (β * x + (a : ℝ) * ((k : ℝ) - x) / q) ≤ intDist (β * k) + 1 / q := by
    have h := intDist_le_intDist_add_abs_sub (β * k) (β * x + (a : ℝ) * ((k : ℝ) - x) / q)
    linarith [hpert]
  have hgrid' : intDist (β * x + (a : ℝ) * ((k : ℝ) - x) / q) = intDist (((i : ℝ) + f) / q) := by
    rw [hgrid, intDist_add_intCast]
  have hlow := grid_le_intDist hq hilt hf0 hf1
  rw [hgrid'] at hdist
  linarith

/-- The grid index is injective on a block of `q` consecutive integers, because `a` is invertible
modulo `q`. -/
theorem gridIndex_injOn {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a) (x : ℤ) :
    Set.InjOn (gridIndex β a q x) (Finset.Ioc x (x + q) : Finset ℤ) := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  intro k hk l hl hkl
  simp only [Finset.coe_Ioc, Set.mem_Ioc] at hk hl
  have hmod : (⌊β * x * q⌋ + a * (k - x)) % (q : ℤ) = (⌊β * x * q⌋ + a * (l - x)) % (q : ℤ) := by
    have h1 := Int.emod_nonneg (⌊β * x * q⌋ + a * (k - x)) (ne_of_gt hq')
    have h2 := Int.emod_nonneg (⌊β * x * q⌋ + a * (l - x)) (ne_of_gt hq')
    have h3 := hkl
    simp only [gridIndex] at h3
    omega
  have hdvd0 : (q : ℤ) ∣ ((⌊β * x * q⌋ + a * (l - x)) - (⌊β * x * q⌋ + a * (k - x))) :=
    Int.ModEq.dvd hmod
  have hdvd : (q : ℤ) ∣ a * (l - k) := by
    have h : (⌊β * x * q⌋ + a * (l - x)) - (⌊β * x * q⌋ + a * (k - x)) = a * (l - k) := by ring
    rwa [h] at hdvd0
  have hkl' : (q : ℤ) ∣ (l - k) := hcop.dvd_of_dvd_mul_left hdvd
  have habs : |l - k| < (q : ℤ) := by rw [abs_lt]; omega
  have := Int.eq_zero_of_abs_lt_dvd hkl' habs
  omega

/-! ## The majorant -/

/-- The majorant of a block: `N` at the four grid points closest to the integers, and
`q/(2(i−1)) + q/(2(q−2−i))` at the others. -/
def weylMajorant (N : ℝ) (q i : ℕ) : ℝ :=
  (if i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q then N else 0)
    + (if 2 ≤ i then (q : ℝ) / (2 * ((i : ℝ) - 1)) else 0)
    + (if i + 3 ≤ q then (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) else 0)

theorem weylMajorant_nonneg {N : ℝ} (hN : 0 ≤ N) (q i : ℕ) : 0 ≤ weylMajorant N q i := by
  have h1 : (0 : ℝ) ≤ if i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q then N else 0 := by
    split_ifs with h
    · exact hN
    · exact le_refl 0
  have h2 : (0 : ℝ) ≤ if 2 ≤ i then (q : ℝ) / (2 * ((i : ℝ) - 1)) else 0 := by
    split_ifs with h
    · have hi : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
      exact div_nonneg (Nat.cast_nonneg q) (by linarith)
    · exact le_refl 0
  have h3 : (0 : ℝ) ≤ if i + 3 ≤ q then (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) else 0 := by
    split_ifs with h
    · have hi : (i : ℝ) + 3 ≤ (q : ℝ) := by exact_mod_cast h
      exact div_nonneg (Nat.cast_nonneg q) (by linarith)
    · exact le_refl 0
  unfold weylMajorant
  linarith

/-- The pointwise bound: on a block of `q` consecutive integers, `g` is at most the majorant at the
corresponding grid index. -/
theorem le_weylMajorant {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N) (hgd : ∀ k, g k * (2 * intDist (β * k)) ≤ 1)
    (x k : ℤ) (hk1 : x < k) (hk2 : k ≤ x + q) :
    g k ≤ weylMajorant N q (gridIndex β a q x k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set i : ℕ := gridIndex β a q x k with hi
  have hilt : i < q := gridIndex_lt hq x k
  unfold weylMajorant
  by_cases hexc : i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q
  · rw [if_pos hexc]
    have h2 : (0 : ℝ) ≤ if 2 ≤ i then (q : ℝ) / (2 * ((i : ℝ) - 1)) else 0 := by
      split_ifs with h
      · have hi2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
        exact div_nonneg (Nat.cast_nonneg q) (by linarith)
      · exact le_refl 0
    have h3 : (0 : ℝ) ≤ if i + 3 ≤ q then (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) else 0 := by
      split_ifs with h
      · have hi3 : (i : ℝ) + 3 ≤ (q : ℝ) := by exact_mod_cast h
        exact div_nonneg (Nat.cast_nonneg q) (by linarith)
      · exact le_refl 0
    linarith [hgN k]
  · have hi2 : 2 ≤ i := by omega
    have hi3 : i + 3 ≤ q := by omega
    rw [if_neg hexc, if_pos hi2, if_pos hi3]
    have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
    have hi3R : (i : ℝ) + 3 ≤ (q : ℝ) := by exact_mod_cast hi3
    have hu : (0 : ℝ) < ((i : ℝ) - 1) / q := div_pos (by linarith) hqR
    have hv : (0 : ℝ) < ((q : ℝ) - 2 - i) / q := div_pos (by linarith) hqR
    have hminsub : ∀ u v c : ℝ, min u v - c = min (u - c) (v - c) := by
      intro u v c
      rcases le_total u v with h | h
      · rw [min_eq_left h, min_eq_left (by linarith)]
      · rw [min_eq_right h, min_eq_right (by linarith)]
    have hd := grid_sub_le_intDist hq happ x k hk1 hk2
    rw [← hi] at hd
    have he1 : (i : ℝ) / q - 1 / q = ((i : ℝ) - 1) / q := by field_simp
    have he2 : ((q : ℝ) - 1 - i) / q - 1 / q = ((q : ℝ) - 2 - i) / q := by field_simp; ring
    rw [hminsub, he1, he2] at hd
    set μ : ℝ := min (((i : ℝ) - 1) / q) (((q : ℝ) - 2 - i) / q) with hμ
    have hμpos : 0 < μ := lt_min hu hv
    have hgk : g k * (2 * μ) ≤ 1 := by
      refine le_trans ?_ (hgd k)
      have h0 := hg0 k
      nlinarith [hd]
    have hle : g k ≤ 1 / (2 * μ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
    have hi1ne : (i : ℝ) - 1 ≠ 0 := by linarith
    have hi2ne : (q : ℝ) - 2 - i ≠ 0 := by linarith
    have e1 : 1 / (2 * (((i : ℝ) - 1) / q)) = (q : ℝ) / (2 * ((i : ℝ) - 1)) := by
      field_simp
    have e2 : 1 / (2 * (((q : ℝ) - 2 - i) / q)) = (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) := by
      field_simp
    rcases le_total (((i : ℝ) - 1) / q) (((q : ℝ) - 2 - i) / q) with h | h
    · rw [hμ, min_eq_left h, e1] at hle
      have : (0 : ℝ) ≤ (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) :=
        div_nonneg (Nat.cast_nonneg q) (by linarith)
      linarith
    · rw [hμ, min_eq_right h, e2] at hle
      have : (0 : ℝ) ≤ (q : ℝ) / (2 * ((i : ℝ) - 1)) :=
        div_nonneg (Nat.cast_nonneg q) (by linarith)
      linarith

/-- The four exceptional grid points contribute at most `4N`. -/
theorem sum_weylMajorant_exceptional_le {q : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    ∑ i ∈ range q, (if i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q then N else 0) ≤ 4 * N := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hsub : (range q).filter (fun i => i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q)
      ⊆ ({0, 1, q - 2, q - 1} : Finset ℕ) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcard : ((range q).filter (fun i => i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q)).card ≤ 4 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h1 := Finset.card_insert_le 1 ({q - 2, q - 1} : Finset ℕ)
    have h2 := Finset.card_insert_le (q - 2) ({q - 1} : Finset ℕ)
    simp only [Finset.card_singleton] at h2 ⊢
    omega
  have hc : ((((range q).filter
      (fun i => i = 0 ∨ i = 1 ∨ i + 2 = q ∨ i + 1 = q)).card : ℝ)) ≤ 4 := by
    exact_mod_cast hcard
  nlinarith

/-- The grid points on the left of the block contribute a harmonic sum. -/
theorem sum_weylMajorant_left_le {q : ℕ} (hq : 0 < q) :
    ∑ i ∈ range q, (if 2 ≤ i then (q : ℝ) / (2 * ((i : ℝ) - 1)) else 0)
      ≤ ((q : ℝ) / 2) * (1 + Real.log q) := by
  classical
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hfil : (range q).filter (fun i => 2 ≤ i) = Finset.Ico 2 q := by
    ext i; simp [Finset.mem_filter, Finset.mem_Ico, and_comm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ j ∈ range (q - 2),
      (q : ℝ) / (2 * (((2 + j : ℕ) : ℝ) - 1)) = ((q : ℝ) / 2) * ((j : ℝ) + 1)⁻¹ := by
    intro j _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hden : (2 : ℝ) * (((2 + j : ℕ) : ℝ) - 1) = 2 * ((j : ℝ) + 1) := by push_cast; ring
    rw [hden, eq_comm, mul_inv_eq_iff_eq_mul₀ (by positivity), div_mul_eq_mul_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h1 : ∑ j ∈ range (q - 2), ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log (q - 2 : ℕ) :=
    sum_range_inv_succ_le _
  have h3 : ∑ j ∈ range (q - 2), ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log q := by
    have := log_natSub_le hq 2; linarith
  nlinarith [h3, hq0]

/-- The grid points on the right of the block contribute a harmonic sum. -/
theorem sum_weylMajorant_right_le {q : ℕ} (hq : 0 < q) :
    ∑ i ∈ range q, (if i + 3 ≤ q then (q : ℝ) / (2 * ((q : ℝ) - 2 - i)) else 0)
      ≤ ((q : ℝ) / 2) * (1 + Real.log q) := by
  classical
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hfil : (range q).filter (fun i => i + 3 ≤ q) = range (q - 2) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil, ← Finset.sum_range_reflect]
  have hterm : ∀ j ∈ range (q - 2),
      (q : ℝ) / (2 * ((q : ℝ) - 2 - ((q - 2 - 1 - j : ℕ) : ℝ)))
        = ((q : ℝ) / 2) * ((j : ℝ) + 1)⁻¹ := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hcast : ((q - 2 - 1 - j : ℕ) : ℝ) = (q : ℝ) - 3 - j := by
      have hrw : (q - 2 - 1 - j : ℕ) = q - (3 + j) := by omega
      rw [hrw, Nat.cast_sub (by omega : 3 + j ≤ q)]
      push_cast; ring
    rw [hcast]
    have hden : (2 : ℝ) * ((q : ℝ) - 2 - ((q : ℝ) - 3 - j)) = 2 * ((j : ℝ) + 1) := by ring
    rw [hden, eq_comm, mul_inv_eq_iff_eq_mul₀ (by positivity), div_mul_eq_mul_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h1 : ∑ j ∈ range (q - 2), ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log (q - 2 : ℕ) :=
    sum_range_inv_succ_le _
  have h3 : ∑ j ∈ range (q - 2), ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log q := by
    have := log_natSub_le hq 2; linarith
  nlinarith [h3, hq0]

/-- The total mass of the majorant over a block. -/
theorem sum_weylMajorant_le {q : ℕ} (hq : 0 < q) {N : ℝ} (hN : 0 ≤ N) :
    ∑ i ∈ range q, weylMajorant N q i ≤ 4 * N + q * (1 + Real.log q) := by
  unfold weylMajorant
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA := sum_weylMajorant_exceptional_le (q := q) hN
  have hB := sum_weylMajorant_left_le hq
  have hC := sum_weylMajorant_right_le hq
  linarith

/-! ## The counting lemma -/

/-- **The block bound.**  Over `q` consecutive integers, a majorant of `min(N, 1/(2‖βk‖))` has
total mass at most `4N + q(1 + log q)`. -/
theorem sum_block_le {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} (hN : 0 ≤ N) {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N) (hgd : ∀ k, g k * (2 * intDist (β * k)) ≤ 1)
    (x : ℤ) :
    ∑ k ∈ Finset.Ioc x (x + q), g k ≤ 4 * N + q * (1 + Real.log q) := by
  classical
  have step1 : ∑ k ∈ Finset.Ioc x (x + q), g k
      ≤ ∑ k ∈ Finset.Ioc x (x + q), weylMajorant N q (gridIndex β a q x k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    rw [Finset.mem_Ioc] at hk
    exact le_weylMajorant hq happ hg0 hgN hgd x k hk.1 hk.2
  have hinj : ∀ k ∈ Finset.Ioc x (x + q), ∀ l ∈ Finset.Ioc x (x + q),
      gridIndex β a q x k = gridIndex β a q x l → k = l := by
    intro k hk l hl h
    exact gridIndex_injOn hq hcop x (by simpa using hk) (by simpa using hl) h
  have step2 : ∑ k ∈ Finset.Ioc x (x + q), weylMajorant N q (gridIndex β a q x k)
      = ∑ i ∈ (Finset.Ioc x (x + q)).image (gridIndex β a q x), weylMajorant N q i :=
    (Finset.sum_image fun k hk l hl h =>
      hinj k (by simpa using hk) l (by simpa using hl) h).symm
  have step3 : ∑ i ∈ (Finset.Ioc x (x + q)).image (gridIndex β a q x), weylMajorant N q i
      ≤ ∑ i ∈ range q, weylMajorant N q i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => weylMajorant_nonneg hN q i)
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, _, rfl⟩ := hi
    exact Finset.mem_range.mpr (gridIndex_lt hq x k)
  have step4 := sum_weylMajorant_le hq hN
  linarith

/-- The block bound iterated over `n` consecutive blocks. -/
theorem sum_Ioc_mul_le {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} (hN : 0 ≤ N) {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N) (hgd : ∀ k, g k * (2 * intDist (β * k)) ≤ 1)
    (n : ℕ) :
    ∑ k ∈ Finset.Ioc (0 : ℤ) ((n * q : ℕ) : ℤ), g k
      ≤ n * (4 * N + q * (1 + Real.log q)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hle1 : (0 : ℤ) ≤ ((n * q : ℕ) : ℤ) := by positivity
      have hle2 : ((n * q : ℕ) : ℤ) ≤ (((n + 1) * q : ℕ) : ℤ) := by
        have : n * q ≤ (n + 1) * q := Nat.mul_le_mul_right q (by omega)
        exact_mod_cast this
      have hsplit : ∑ k ∈ Finset.Ioc (0 : ℤ) ((n * q : ℕ) : ℤ), g k
          + ∑ k ∈ Finset.Ioc (((n * q : ℕ) : ℤ)) ((((n + 1) * q : ℕ)) : ℤ), g k
          = ∑ k ∈ Finset.Ioc (0 : ℤ) ((((n + 1) * q : ℕ)) : ℤ), g k := by
        rw [← Finset.sum_union, Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2]
        refine Finset.disjoint_left.mpr ?_
        intro y hy hy'
        simp only [Finset.mem_Ioc] at hy hy'
        omega
      have hblock : ∑ k ∈ Finset.Ioc (((n * q : ℕ) : ℤ)) ((((n + 1) * q : ℕ)) : ℤ), g k
          ≤ 4 * N + q * (1 + Real.log q) := by
        have h := sum_block_le hq hcop happ hN hg0 hgN hgd ((n * q : ℕ) : ℤ)
        have hrw : ((n * q : ℕ) : ℤ) + (q : ℤ) = (((n + 1) * q : ℕ) : ℤ) := by push_cast; ring
        rwa [hrw] at h
      have hcast : ((n : ℝ) + 1) * (4 * N + q * (1 + Real.log q))
          = n * (4 * N + q * (1 + Real.log q)) + (4 * N + q * (1 + Real.log q)) := by ring
      push_cast at hsplit hblock ih ⊢
      linarith [hsplit, hblock, ih]

/-- **The counting lemma.**  `∑_{0 < k ≤ H} min(N, 1/(2‖βk‖)) ≤ (H/q + 1)(4N + q(1 + log q))`. -/
theorem sum_Ioc_le {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} (hN : 0 ≤ N) {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N) (hgd : ∀ k, g k * (2 * intDist (β * k)) ≤ 1)
    (H : ℕ) :
    ∑ k ∈ Finset.Ioc (0 : ℤ) (H : ℤ), g k
      ≤ ((H : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set n : ℕ := H / q + 1 with hn
  have hHn : (H : ℤ) ≤ ((n * q : ℕ) : ℤ) := by
    have h1 := Nat.div_add_mod H q
    have h2 := Nat.mod_lt H hq
    have : H < (H / q + 1) * q := by
      calc H = q * (H / q) + H % q := h1.symm
        _ < q * (H / q) + q := by omega
        _ = (H / q + 1) * q := by ring
    exact_mod_cast le_of_lt this
  have hsub : ∑ k ∈ Finset.Ioc (0 : ℤ) (H : ℤ), g k
      ≤ ∑ k ∈ Finset.Ioc (0 : ℤ) ((n * q : ℕ) : ℤ), g k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hHn) ?_
    intro k _ _
    exact hg0 k
  have hmain := sum_Ioc_mul_le hq hcop happ hN hg0 hgN hgd n
  have hnR : (n : ℝ) ≤ (H : ℝ) / q + 1 := by
    have : ((H / q : ℕ) : ℝ) ≤ (H : ℝ) / q := Nat.cast_div_le
    rw [hn]
    push_cast
    linarith
  have hB : (0 : ℝ) ≤ 4 * N + q * (1 + Real.log q) := by
    have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith
  calc ∑ k ∈ Finset.Ioc (0 : ℤ) (H : ℤ), g k
      ≤ ∑ k ∈ Finset.Ioc (0 : ℤ) ((n * q : ℕ) : ℤ), g k := hsub
    _ ≤ n * (4 * N + q * (1 + Real.log q)) := hmain
    _ ≤ ((H : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := by
        exact mul_le_mul_of_nonneg_right hnR hB

/-! ## Weyl's inequality for the quadratic sum, with the counting lemma -/

/-- The differenced sums of the phase `α n²`, extended by zero to the left. -/
def quadInner (α : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if 0 < k then
    ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖
  else 0

theorem quadInner_nonneg (α : ℝ) (N : ℕ) (k : ℤ) : 0 ≤ quadInner α N k := by
  unfold quadInner
  split_ifs
  · exact norm_nonneg _
  · exact le_refl 0

theorem quadInner_le (α : ℝ) (N : ℕ) (k : ℤ) : quadInner α N k ≤ N := by
  unfold quadInner
  split_ifs with hk
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
        ‖e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖ = 1 := fun n _ => norm_e2pi _
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Ico]
    have : ((N : ℤ) - k - 0).toNat ≤ N := by omega
    exact_mod_cast this
  · exact Nat.cast_nonneg N

theorem quadInner_mul_intDist_le (α : ℝ) (N : ℕ) (k : ℤ) :
    quadInner α N k * (2 * intDist (2 * α * k)) ≤ 1 := by
  unfold quadInner
  split_ifs with hk
  · by_cases h : intDist (2 * α * k) = 0
    · rw [h]; simp
    · have hd : 0 < intDist (2 * α * k) :=
        lt_of_le_of_ne (intDist_nonneg _) (Ne.symm h)
      have hb : ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
            e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖
          ≤ 1 / (2 * intDist (2 * α * k)) := by
        have hg : ∀ n : ℤ, e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)
            = e2pi ((2 * α * k) * (n : ℝ) + α * (k : ℝ) ^ 2) := fun n => by rw [quadratic_diff]
        simp only [hg]
        rw [sum_Ico_int_eq_sum_range]
        exact norm_geomSum_e2pi_le h _ _
      calc ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
              e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖ * (2 * intDist (2 * α * k))
          ≤ (1 / (2 * intDist (2 * α * k))) * (2 * intDist (2 * α * k)) := by
            exact mul_le_mul_of_nonneg_right hb (by positivity)
        _ = 1 := by field_simp
  · simp

/-- **Weyl's inequality for a quadratic phase, with the counting lemma.**  For a rational
approximation `|2α − a/q| ≤ 1/q²` with `a` and `q` coprime,
`‖∑_{n<N} e(α n²)‖² ≤ 2N + 4(N/q + 1)(4N + q(1 + log q))`. -/
theorem normSq_quadSum_le_of_approx_count {α : ℝ} {a : ℤ} {q N : ℕ} (hq : 0 < q) (hN : 0 < N)
    (hcop : IsCoprime (q : ℤ) a) (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ 2 * N + 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hA := norm_sq_sum_e2pi_le (fun n : ℤ => α * (n : ℝ) ^ 2) N N hN
  -- the differenced sums are the values of `quadInner`
  have hIoo : ∑ k ∈ Finset.Ioo (0 : ℤ) (N : ℤ),
        ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
          e2pi (α * ((n + k : ℤ) : ℝ) ^ 2 - α * (n : ℝ) ^ 2)‖
      = ∑ k ∈ Finset.Ioo (0 : ℤ) (N : ℤ), quadInner α N k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_Ioo] at hk
    unfold quadInner
    rw [if_pos hk.1]
  -- the counting lemma, applied with `β = 2α`
  have hcount : ∑ k ∈ Finset.Ioc (0 : ℤ) (N : ℤ), quadInner α N k
      ≤ ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := by
    have happ' : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := happ
    have hgd : ∀ k : ℤ, quadInner α N k * (2 * intDist (2 * α * k)) ≤ 1 :=
      quadInner_mul_intDist_le α N
    exact sum_Ioc_le hq hcop happ' (le_of_lt hNR) (quadInner_nonneg α N)
      (quadInner_le α N) hgd N
  have hsub : ∑ k ∈ Finset.Ioo (0 : ℤ) (N : ℤ), quadInner α N k
      ≤ ∑ k ∈ Finset.Ioc (0 : ℤ) (N : ℤ), quadInner α N k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => quadInner_nonneg α N k)
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [Finset.mem_Ioc]
    omega
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ with hS
  set B : ℝ := ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) with hB
  have hBnonneg : 0 ≤ B := by
    have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    have h1 : (0 : ℝ) ≤ (N : ℝ) / q + 1 := by positivity
    have h2 : (0 : ℝ) ≤ 4 * N + q * (1 + Real.log q) := by nlinarith
    exact mul_nonneg h1 h2
  have hSnonneg : 0 ≤ S := norm_nonneg _
  have hkey : (N : ℝ) * S ^ 2 ≤ ((N : ℝ) + N - 1) * ((N : ℝ) + 2 * B) := by
    refine le_trans hA ?_
    have hfac : (0 : ℝ) ≤ (N : ℝ) + N - 1 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    refine mul_le_mul_of_nonneg_left ?_ hfac
    rw [hIoo] at *
    linarith [hsub, hcount]
  have hfinal : (N : ℝ) * S ^ 2 ≤ (N : ℝ) * (2 * N + 4 * B) := by
    have hle : ((N : ℝ) + N - 1) * ((N : ℝ) + 2 * B) ≤ (2 * N) * ((N : ℝ) + 2 * B) := by
      have hpos : (0 : ℝ) ≤ (N : ℝ) + 2 * B := by linarith
      nlinarith
    calc (N : ℝ) * S ^ 2 ≤ ((N : ℝ) + N - 1) * ((N : ℝ) + 2 * B) := hkey
      _ ≤ (2 * N) * ((N : ℝ) + 2 * B) := hle
      _ = (N : ℝ) * (2 * N + 4 * B) := by ring
  have hcancel := le_of_mul_le_mul_left hfinal hNR
  calc S ^ 2 ≤ 2 * N + 4 * B := hcancel
    _ = 2 * N + 4 * (((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q))) := by rw [hB]
    _ = 2 * N + 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := by ring

/-- **Square-root cancellation.**  If `2α` has a rational approximation `|2α − a/q| ≤ 1/q²` with
`a` and `q` coprime and a denominator `N ≤ q ≤ 2N`, then
`‖∑_{n<N} e(α n²)‖² ≤ 66 N (1 + log (2N))`. -/
theorem normSq_quadSum_le_of_approx_large {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N)
    (hq1 : N ≤ q) (hq2 : q ≤ 2 * N) (hcop : IsCoprime (q : ℤ) a)
    (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ 66 * N * (1 + Real.log (2 * N)) := by
  have hq : 0 < q := lt_of_lt_of_le hN hq1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (N : ℝ) ≤ q := by exact_mod_cast hq1
  have hq2R : (q : ℝ) ≤ 2 * N := by exact_mod_cast hq2
  have hmain := normSq_quadSum_le_of_approx_count hq hN hcop happ
  have hratio : (N : ℝ) / q + 1 ≤ 2 := by
    have h : (N : ℝ) / q ≤ 1 := by rw [div_le_one hqR]; exact hq1R
    linarith
  have hlogq : Real.log q ≤ Real.log (2 * N) := by
    refine Real.log_le_log hqR ?_
    linarith
  have hlog2N : (0 : ℝ) ≤ Real.log (2 * N) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hq' : (q : ℝ) * (1 + Real.log q) ≤ 2 * N * (1 + Real.log (2 * N)) := by
    have h1 : (0 : ℝ) ≤ 1 + Real.log q := by
      have : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
      linarith
    nlinarith
  have hfactor : (0 : ℝ) ≤ 4 * N + q * (1 + Real.log q) := by
    have : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    nlinarith
  have hstep : 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q))
      ≤ 8 * (4 * N + 2 * N * (1 + Real.log (2 * N))) := by
    have h1 : 4 * ((N : ℝ) / q + 1) ≤ 8 := by linarith
    have h2 : (4 : ℝ) * N + q * (1 + Real.log q) ≤ 4 * N + 2 * N * (1 + Real.log (2 * N)) := by
      linarith
    have h3 : (0 : ℝ) ≤ 4 * ((N : ℝ) / q + 1) := by positivity
    nlinarith
  nlinarith [hmain, hstep, hlog2N, hNR]

/-- The same bound, in the form `‖∑_{n<N} e(α n²)‖ ≤ 9 √(N (1 + log (2N)))`: the Weyl exponent
`1/2`, up to a logarithm. -/
theorem norm_quadSum_le_of_approx_large {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N)
    (hq1 : N ≤ q) (hq2 : q ≤ 2 * N) (hcop : IsCoprime (q : ℤ) a)
    (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖
      ≤ 9 * Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N))) := by
  have hsq := normSq_quadSum_le_of_approx_large hN hq1 hq2 hcop happ
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 2)‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have hX : (0 : ℝ) ≤ (N : ℝ) * (1 + Real.log (2 * N)) := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) ≤ Real.log (2 * N) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    nlinarith
  have hle : S ^ 2 ≤ (9 * Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N)))) ^ 2 := by
    have hsqrt : Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N))) ^ 2
        = (N : ℝ) * (1 + Real.log (2 * N)) := Real.sq_sqrt hX
    calc S ^ 2 ≤ 66 * N * (1 + Real.log (2 * N)) := hsq
      _ ≤ 81 * ((N : ℝ) * (1 + Real.log (2 * N))) := by nlinarith
      _ = (9 * Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N)))) ^ 2 := by
          rw [mul_pow, hsqrt]; ring
  have hpos : (0 : ℝ) ≤ 9 * Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N))) := by positivity
  nlinarith [hle, hS0, hpos]

end WeylQuadratic

end RiemannHypothesis
