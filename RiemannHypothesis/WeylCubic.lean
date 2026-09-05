/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylBadlyApproximable

/-!
# Weyl's bound for a cubic exponential sum: the A process iterated

`RiemannHypothesis.WeylQuadratic` applies van der Corput's A process once, to the phase `α n²`,
whose differenced phase is linear.  A cubic phase needs the process *twice*: the first differencing
turns `α n³` into a quadratic phase, the second one turns that quadratic phase into a linear one,
which is summed exactly by the geometric-series bound `norm_geomSum_e2pi_le`.  This file carries
out the two steps and feeds the result into the counting lemma `sum_Ioc_le` of
`RiemannHypothesis.WeylMinSum`, which is what the open boundary of `M1-WEYL-MIN-SUM` named as the
missing degree-`3` case.

## The mechanism

Write `f n = α n³` and `S = ∑_{0 ≤ n < N} e(f n)`.  The A process gives

  `H ‖S‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} ‖T k‖)`,   `T k = ∑_n e(f(n+k) − f n)`,

and each `T k` is an exponential sum with the *quadratic* phase `f(· + k) − f(·)`.  Applying the A
process to it as well, and using

  `f(n+l+k) − f(n+l) − f(n+k) + f n = (6α k l) n + α(3kl² + 3k²l)`,

a linear phase in `n` with leading coefficient `6α k l`, gives

  `H ‖T k‖² ≤ (N + H − 1) (N + 2 ∑_{0 < l < H} min(N, 1/(2‖6α k l‖)))`.

Cauchy–Schwarz over the `H − 1` shifts `k` turns `(∑_k ‖T k‖)²` into `H ∑_k ‖T k‖²`, and the double
sum over `(k, l)` is folded onto the single variable `m = k l`: for each fixed `k` the map
`l ↦ k l` is injective into `(0, H²]`, so the double sum is at most `H` times
`∑_{0 < m ≤ H²} min(N, 1/(2‖6α m‖))`, which is exactly what the counting lemma of
`RiemannHypothesis.WeylMinSum` bounds.  No divisor-function estimate is needed: the crude count
`#{l < H : k l = m} ≤ 1` for fixed `k` suffices, at the cost of a worse exponent than the classical
one.

## Main results

* `dioMaj` — the majorant `min(N, 1/(2‖β m‖))`, written so that no convention for `1/0` is needed;
* `norm_linSum_le_dioMaj` — a linear exponential sum of length at most `N` is at most `dioMaj`;
* `mul_normSq_cubeSum_le` — the first differencing;
* `mul_sq_cubeInner_le` — the second differencing, for a fixed shift `k`;
* `sum_double_le` — the double sum `∑_{k,l < H} dioMaj (6α) N (k l)`, through the counting lemma;
* `norm_cubeSum_pow_four_le_of_approx` — the assembled inequality, with `H` free;
* `norm_cubeSum_pow_eight_le_of_approx` — the choice `H = ⌊√N⌋ + 1`:
  `‖∑_{n<N} e(α n³)‖⁸ ≤ 2²² (4N/q + 1)² N⁷ (1 + log 4N)²`, i.e. `‖S‖ ≪ N^(7/8) (log N)^(1/4)`
  once `6α` has a coprime approximation `|6α − a/q| ≤ 1/q²` with `q` of order `N`;
* `norm_cubeSum_pow_eight_le_of_badlyApproximable`, `norm_cubeSum_sqrt_two_le` — the unconditional
  form for a badly approximable `6α`, and the explicit instance `α = √2/6`.

## Scope

The exponent is `7/8`, not the classical Weyl exponent `3/4` for a cubic phase: the losses are the
Cauchy–Schwarz over the shifts and the crude folding of the pairs `(k, l)`, which the classical
argument avoids by an average divisor bound.  The constants are not optimized.  As it must be, the
bound is conditional on a rational approximation to `6α` with a large denominator; for `α` close to
a rational with a small denominator there is no cancellation at all.  Nothing about `ζ` follows:
cubic phases are not zeta phases, and no subconvexity bound, approximate functional equation or
density estimate is claimed.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylCubic

open KusminLandau WeylDifferencing WeylQuadratic

/-! ## The majorant `min(N, 1/(2‖β m‖))` -/

/-- The majorant `min(N, 1/(2‖β m‖))` of a linear exponential sum of length at most `N` and
frequency `β m`.  When `β m` is an integer the reciprocal is meaningless and the value is `N`. -/
def dioMaj (β : ℝ) (N : ℕ) (m : ℤ) : ℝ :=
  if intDist (β * m) = 0 then (N : ℝ) else min (N : ℝ) (1 / (2 * intDist (β * m)))

theorem dioMaj_nonneg (β : ℝ) (N : ℕ) (m : ℤ) : 0 ≤ dioMaj β N m := by
  unfold dioMaj
  split_ifs with h
  · exact Nat.cast_nonneg N
  · have hd : 0 < intDist (β * m) := lt_of_le_of_ne (intDist_nonneg _) (Ne.symm h)
    exact le_min (Nat.cast_nonneg N) (by positivity)

theorem dioMaj_le (β : ℝ) (N : ℕ) (m : ℤ) : dioMaj β N m ≤ (N : ℝ) := by
  unfold dioMaj
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

theorem dioMaj_mul_intDist_le (β : ℝ) (N : ℕ) (m : ℤ) :
    dioMaj β N m * (2 * intDist (β * m)) ≤ 1 := by
  unfold dioMaj
  split_ifs with h
  · rw [h]; simp
  · have hd : 0 < intDist (β * m) := lt_of_le_of_ne (intDist_nonneg _) (Ne.symm h)
    calc min (N : ℝ) (1 / (2 * intDist (β * m))) * (2 * intDist (β * m))
        ≤ (1 / (2 * intDist (β * m))) * (2 * intDist (β * m)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1 := by field_simp

/-- A linear exponential sum of length at most `N` is bounded by the majorant. -/
theorem norm_linSum_le_dioMaj {β c : ℝ} {m M : ℤ} {N : ℕ} (hM : M ≤ (N : ℤ)) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) M, e2pi (β * (m : ℝ) * (n : ℝ) + c)‖ ≤ dioMaj β N m := by
  have hlen : ‖∑ n ∈ Finset.Ico (0 : ℤ) M, e2pi (β * (m : ℝ) * (n : ℝ) + c)‖ ≤ (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ico (0 : ℤ) M,
        ‖e2pi (β * (m : ℝ) * (n : ℝ) + c)‖ = 1 := fun n _ => norm_e2pi _
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Ico]
    have : (M - 0).toNat ≤ N := by omega
    exact_mod_cast this
  unfold dioMaj
  split_ifs with h
  · exact hlen
  · refine le_min hlen ?_
    have hgeom : ‖∑ j ∈ range M.toNat, e2pi (β * (m : ℝ) * (j : ℝ) + c)‖
        ≤ 1 / (2 * intDist (β * (m : ℝ))) := norm_geomSum_e2pi_le h _ _
    rw [sum_Ico_int_eq_sum_range]
    refine le_trans (le_of_eq ?_) hgeom
    congr 1

/-! ## The two differencing steps -/

/-- The cubic exponential sum `∑_{0 ≤ n < N} e(α n³)`. -/
def cubeSum (α : ℝ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ 3)

/-- The once-differenced sums of the phase `α n³`, extended by zero to the left. -/
def cubeInner (α : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if 0 < k then
    ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (α * ((n + k : ℤ) : ℝ) ^ 3 - α * (n : ℝ) ^ 3)‖
  else 0

theorem cubeInner_nonneg (α : ℝ) (N : ℕ) (k : ℤ) : 0 ≤ cubeInner α N k := by
  unfold cubeInner
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

/-- The second difference of a cubic phase is linear, with leading coefficient `6α k l`. -/
theorem cubic_second_diff (α : ℝ) (k l n : ℤ) :
    (α * ((n + l + k : ℤ) : ℝ) ^ 3 - α * ((n + l : ℤ) : ℝ) ^ 3)
        - (α * ((n + k : ℤ) : ℝ) ^ 3 - α * (n : ℝ) ^ 3)
      = 6 * α * ((k * l : ℤ) : ℝ) * (n : ℝ)
        + α * (3 * (k : ℝ) * (l : ℝ) ^ 2 + 3 * (k : ℝ) ^ 2 * (l : ℝ)) := by
  push_cast
  ring

/-- **The first differencing.**  The A process applied to the cubic phase. -/
theorem mul_normSq_cubeSum_le (α : ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖cubeSum α N‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), cubeInner α N k) := by
  have h := norm_sq_sum_e2pi_le (fun n : ℤ => α * (n : ℝ) ^ 3) N H hH
  have hIoo : ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
          e2pi (α * ((n + k : ℤ) : ℝ) ^ 3 - α * (n : ℝ) ^ 3)‖
      = ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), cubeInner α N k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ioo] at hk
    unfold cubeInner
    rw [if_pos hk.1]
  rw [hIoo] at h
  exact h

/-- **The second differencing.**  For a fixed shift `k`, the once-differenced sum is a quadratic
exponential sum, and the A process bounds it by the linear sums with frequencies `6α k l`. -/
theorem mul_sq_cubeInner_le (α : ℝ) {N H : ℕ} (hH : 0 < H) {k : ℤ} (hk : 0 < k)
    (hkN : k ≤ (N : ℤ)) :
    (H : ℝ) * cubeInner α N k ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          dioMaj (6 * α) N (k * l)) := by
  set M : ℕ := ((N : ℤ) - k).toNat with hMdef
  have hMZ : ((M : ℤ)) = (N : ℤ) - k := Int.toNat_of_nonneg (by omega)
  have hMN : M ≤ N := by omega
  have hMNR : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  set g : ℤ → ℝ := fun n => α * ((n + k : ℤ) : ℝ) ^ 3 - α * (n : ℝ) ^ 3 with hg
  have hcube : cubeInner α N k = ‖∑ n ∈ Finset.Ico (0 : ℤ) (M : ℤ), e2pi (g n)‖ := by
    unfold cubeInner
    rw [if_pos hk, hMZ]
  have hA := norm_sq_sum_e2pi_le g M H hH
  have hinner : ∀ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((M : ℤ) - l), e2pi (g (n + l) - g n)‖
        ≤ dioMaj (6 * α) N (k * l) := by
    intro l hl
    rw [Finset.mem_Ioo] at hl
    have hphase : ∀ n : ℤ, g (n + l) - g n
        = 6 * α * ((k * l : ℤ) : ℝ) * (n : ℝ)
          + α * (3 * (k : ℝ) * (l : ℝ) ^ 2 + 3 * (k : ℝ) ^ 2 * (l : ℝ)) := by
      intro n
      simp only [hg]
      have := cubic_second_diff α k l n
      push_cast at this ⊢
      linarith [this]
    simp only [hphase]
    exact norm_linSum_le_dioMaj (by omega)
  have hsum : ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        ‖∑ n ∈ Finset.Ico (0 : ℤ) ((M : ℤ) - l), e2pi (g (n + l) - g n)‖
      ≤ ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l) :=
    Finset.sum_le_sum hinner
  have hDnonneg : (0 : ℝ) ≤ ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l) :=
    Finset.sum_nonneg fun l _ => dioMaj_nonneg _ _ _
  have hfac : (0 : ℝ) ≤ (M : ℝ) + H - 1 := by
    have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith [show (1 : ℝ) ≤ (H : ℝ) from by exact_mod_cast hH]
  rw [hcube]
  refine hA.trans ?_
  have h1 : (M : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        ‖∑ n ∈ Finset.Ico (0 : ℤ) ((M : ℤ) - l), e2pi (g (n + l) - g n)‖
      ≤ (N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l) := by
    linarith
  have h2 : (M : ℝ) + H - 1 ≤ (N : ℝ) + H - 1 := by linarith
  have h3 : (0 : ℝ) ≤ (N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  calc ((M : ℝ) + H - 1) * ((M : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          ‖∑ n ∈ Finset.Ico (0 : ℤ) ((M : ℤ) - l), e2pi (g (n + l) - g n)‖)
      ≤ ((M : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          dioMaj (6 * α) N (k * l)) := mul_le_mul_of_nonneg_left h1 hfac
    _ ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          dioMaj (6 * α) N (k * l)) := mul_le_mul_of_nonneg_right h2 h3

/-! ## The double sum, through the counting lemma -/

/-- Folding the pairs `(k, l)` onto the product `m = k l`: for a fixed `k` the map `l ↦ k l` is
injective into `(0, H²]`, so the double sum is at most `H` single sums. -/
theorem sum_double_le {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj β N (k * l)
      ≤ (H : ℝ) * (((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q))) := by
  classical
  set B : ℝ := ((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q)) with hB
  have hBnonneg : 0 ≤ B := by
    have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have hqR : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : (0 : ℝ) ≤ (H : ℝ) ^ 2 / q + 1 := by positivity
    have h2 : (0 : ℝ) ≤ 4 * (N : ℝ) + q * (1 + Real.log q) := by nlinarith
    exact mul_nonneg h1 h2
  have hrow : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
      ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj β N (k * l) ≤ B := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have himg : ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj β N (k * l)
        = ∑ m ∈ (Finset.Ioo (0 : ℤ) (H : ℤ)).image (fun l => k * l), dioMaj β N m := by
      refine (Finset.sum_image ?_).symm
      intro x _ y _ hxy
      exact mul_left_cancel₀ (by omega) hxy
    have hsub : (Finset.Ioo (0 : ℤ) (H : ℤ)).image (fun l => k * l)
        ⊆ Finset.Ioc (0 : ℤ) (((H ^ 2 : ℕ) : ℤ)) := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨l, hl, rfl⟩ := hm
      rw [Finset.mem_Ioo] at hl
      rw [Finset.mem_Ioc]
      refine ⟨mul_pos (by omega) (by omega), ?_⟩
      have hstep : k * l ≤ ((H : ℤ) - 1) * ((H : ℤ) - 1) :=
        mul_le_mul (by omega) (by omega) (by omega) (by omega)
      have hH2 : (((H ^ 2 : ℕ)) : ℤ) = (H : ℤ) * (H : ℤ) := by push_cast; ring
      rw [hH2]
      nlinarith [hstep, hk.1, hk.2]
    have hle : ∑ m ∈ (Finset.Ioo (0 : ℤ) (H : ℤ)).image (fun l => k * l), dioMaj β N m
        ≤ ∑ m ∈ Finset.Ioc (0 : ℤ) (((H ^ 2 : ℕ) : ℤ)), dioMaj β N m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => dioMaj_nonneg _ _ _
    have hcount := sum_Ioc_le hq hcop happ (Nat.cast_nonneg N) (dioMaj_nonneg β N)
      (dioMaj_le β N) (dioMaj_mul_intDist_le β N) (H ^ 2)
    rw [himg]
    refine hle.trans ?_
    refine hcount.trans (le_of_eq ?_)
    rw [hB]
    push_cast
    ring
  have hcard : ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj β N (k * l)
      ≤ ∑ _k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), B := Finset.sum_le_sum hrow
  refine hcard.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Int.card_Ioo]
  have hcardle : (((H : ℤ) - 0 - 1).toNat : ℝ) ≤ (H : ℝ) := by
    have : ((H : ℤ) - 0 - 1).toNat ≤ H := by omega
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcardle hBnonneg

/-! ## The assembled inequality -/

/-- **Weyl's inequality for a cubic phase.**  With the number of shifts `H` left free. -/
theorem norm_cubeSum_pow_four_le_of_approx {α : ℝ} {a : ℤ} {q N H : ℕ} (hq : 0 < q)
    (hH : 0 < H) (hHN : H ≤ N) (hcop : IsCoprime (q : ℤ) a)
    (happ : |6 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖cubeSum α N‖ ^ 4
      ≤ 2 * ((N : ℝ) + H - 1) ^ 2 / (H : ℝ) ^ 2
        * ((N : ℝ) ^ 2 + 4 * H * ((N : ℝ) + H - 1)
            * ((N : ℝ) + 2 * (((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q))))) := by
  classical
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHNR : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hHN
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  set P : ℝ := (N : ℝ) + H - 1 with hPdef
  set B : ℝ := ((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q)) with hBdef
  set A : ℝ := ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), cubeInner α N k with hAdef
  set T : ℝ := ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), cubeInner α N k ^ 2 with hTdef
  set D : ℝ := ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
    ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l) with hDdef
  set S : ℝ := ‖cubeSum α N‖ with hSdef
  have hSnonneg : 0 ≤ S := norm_nonneg _
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hPnonneg : 0 ≤ P := by rw [hPdef]; linarith
  have hAnonneg : 0 ≤ A := Finset.sum_nonneg fun k _ => cubeInner_nonneg _ _ _
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hBnonneg : 0 ≤ B := by
    have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have hqR : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h1 : (0 : ℝ) ≤ (H : ℝ) ^ 2 / q + 1 := by positivity
    have h2 : (0 : ℝ) ≤ 4 * (N : ℝ) + q * (1 + Real.log q) := by nlinarith
    exact mul_nonneg h1 h2
  -- the first differencing
  have h1 : (H : ℝ) * S ^ 2 ≤ P * ((N : ℝ) + 2 * A) := mul_normSq_cubeSum_le α N H hH
  -- Cauchy-Schwarz over the shifts
  have hcardle : (((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) ≤ (H : ℝ) := by
    rw [Int.card_Ioo]
    have : ((H : ℤ) - 0 - 1).toNat ≤ H := by omega
    exact_mod_cast this
  have hCS : A ^ 2 ≤ (H : ℝ) * T := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioo (0 : ℤ) (H : ℤ)) (fun _ => (1 : ℝ))
      (fun k => cubeInner α N k)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    calc A ^ 2 ≤ (((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) * T := hcs
      _ ≤ (H : ℝ) * T := mul_le_mul_of_nonneg_right hcardle hTnonneg
  -- the second differencing, summed over the shifts
  have hterm : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), (H : ℝ) * cubeInner α N k ^ 2
      ≤ P * ((N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ), dioMaj (6 * α) N (k * l)) := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    exact mul_sq_cubeInner_le α hH hk.1 (by omega)
  have hsummed : (H : ℝ) * T
      ≤ P * ((((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) * N + 2 * D) := by
    have hle := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hle
    refine hle.trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hDle : D ≤ (H : ℝ) * B := sum_double_le hq hcop happ N H
  have hTle : (H : ℝ) * T ≤ (H : ℝ) * (P * ((N : ℝ) + 2 * B)) := by
    have h : P * ((((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) * N + 2 * D)
        ≤ P * ((H : ℝ) * N + 2 * ((H : ℝ) * B)) := by
      refine mul_le_mul_of_nonneg_left ?_ hPnonneg
      have := mul_le_mul_of_nonneg_right hcardle hNR
      linarith
    calc (H : ℝ) * T ≤ P * ((((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) * N + 2 * D) := hsummed
      _ ≤ P * ((H : ℝ) * N + 2 * ((H : ℝ) * B)) := h
      _ = (H : ℝ) * (P * ((N : ℝ) + 2 * B)) := by ring
  have hA2 : A ^ 2 ≤ (H : ℝ) * (P * ((N : ℝ) + 2 * B)) := hCS.trans hTle
  -- assembling
  have hkey : (H : ℝ) ^ 2 * S ^ 4
      ≤ 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := by
    have hsq : ((H : ℝ) * S ^ 2) ^ 2 ≤ (P * ((N : ℝ) + 2 * A)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have hexpand : (P * ((N : ℝ) + 2 * A)) ^ 2
        ≤ 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := by
      have hstep : ((N : ℝ) + 2 * A) ^ 2 ≤ 2 * ((N : ℝ) ^ 2 + 4 * A ^ 2) := by
        nlinarith [sq_nonneg ((N : ℝ) - 2 * A)]
      have hstep' : 2 * ((N : ℝ) ^ 2 + 4 * A ^ 2)
          ≤ 2 * ((N : ℝ) ^ 2 + 4 * ((H : ℝ) * (P * ((N : ℝ) + 2 * B)))) := by linarith
      calc (P * ((N : ℝ) + 2 * A)) ^ 2 = P ^ 2 * ((N : ℝ) + 2 * A) ^ 2 := by ring
        _ ≤ P ^ 2 * (2 * ((N : ℝ) ^ 2 + 4 * A ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep (sq_nonneg P)
        _ ≤ P ^ 2 * (2 * ((N : ℝ) ^ 2 + 4 * ((H : ℝ) * (P * ((N : ℝ) + 2 * B))))) :=
            mul_le_mul_of_nonneg_left hstep' (sq_nonneg P)
        _ = 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := by ring
    calc (H : ℝ) ^ 2 * S ^ 4 = ((H : ℝ) * S ^ 2) ^ 2 := by ring
      _ ≤ (P * ((N : ℝ) + 2 * A)) ^ 2 := hsq
      _ ≤ 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := hexpand
  have hfinal : S ^ 4
      ≤ 2 * P ^ 2 / (H : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := by
    rw [show 2 * P ^ 2 / (H : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B))
        = 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) / (H : ℝ) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    calc S ^ 4 * (H : ℝ) ^ 2 = (H : ℝ) ^ 2 * S ^ 4 := by ring
      _ ≤ 2 * P ^ 2 * ((N : ℝ) ^ 2 + 4 * H * P * ((N : ℝ) + 2 * B)) := hkey
  exact hfinal

/-- The real-arithmetic core of the cubic bound, isolated from the analysis: the two differencing
steps produce the inequality `hS4`, and with `h ≈ √n` it gives the exponent `7/8`. -/
theorem cubic_bound_numeric {n h P B L R S : ℝ}
    (hn1 : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) (hnh2 : n ≤ h ^ 2)
    (hL1 : 1 ≤ L) (hR1 : 1 ≤ R) (hB0 : 0 ≤ B) (hB : B ≤ 8 * n * L * R)
    (hP : P = n + h - 1)
    (hS4 : S ^ 4 ≤ 2 * P ^ 2 / h ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B))) :
    S ^ 8 ≤ 2 ^ 22 * R ^ 2 * n ^ 7 * L ^ 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hn2 : (0 : ℝ) ≤ n ^ 2 := by positivity
  have hLR1 : (1 : ℝ) ≤ L * R := by nlinarith
  have hP0 : 0 ≤ P := by rw [hP]; linarith
  have hP2 : P ≤ 2 * n := by rw [hP]; linarith
  have hn2B : n + 2 * B ≤ 17 * n * L * R := by
    have h1 : n ≤ n * L * R := by nlinarith
    linarith
  have hn2B0 : (0 : ℝ) ≤ n + 2 * B := by linarith
  have hY : n ^ 2 + 4 * h * P * (n + 2 * B) ≤ 137 * h * n ^ 2 * L * R := by
    have hstep : 4 * h * P ≤ 8 * h * n := by nlinarith
    have h1 : 4 * h * P * (n + 2 * B) ≤ 136 * h * n ^ 2 * L * R := by
      calc 4 * h * P * (n + 2 * B) ≤ (8 * h * n) * (17 * n * L * R) :=
            mul_le_mul hstep hn2B hn2B0 (by positivity)
        _ = 136 * h * n ^ 2 * L * R := by ring
    have h2 : n ^ 2 ≤ h * n ^ 2 * L * R := by
      calc n ^ 2 = n ^ 2 * 1 * 1 := by ring
        _ ≤ n ^ 2 * h * (L * R) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hh1 hn2) hLR1 zero_le_one (by nlinarith)
        _ = h * n ^ 2 * L * R := by ring
    linarith
  have hY0 : (0 : ℝ) ≤ n ^ 2 + 4 * h * P * (n + 2 * B) := by
    have h1 : (0 : ℝ) ≤ 4 * h * P * (n + 2 * B) :=
      mul_nonneg (mul_nonneg (by positivity) hP0) hn2B0
    linarith
  have hbig : 2 * P ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B)) ≤ 1096 * n ^ 4 * L * R * h := by
    have h1 : 2 * P ^ 2 ≤ 8 * n ^ 2 := by nlinarith
    calc 2 * P ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B)) ≤ 8 * n ^ 2 * (137 * h * n ^ 2 * L * R) :=
          mul_le_mul h1 hY hY0 (by positivity)
      _ = 1096 * n ^ 4 * L * R * h := by ring
  have hS4' : S ^ 4 ≤ 1096 * n ^ 4 * L * R / h := by
    refine hS4.trans ?_
    rw [show 2 * P ^ 2 / h ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B))
        = 2 * P ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B)) / h ^ 2 by ring,
      div_le_div_iff₀ (by positivity) hh0]
    calc 2 * P ^ 2 * (n ^ 2 + 4 * h * P * (n + 2 * B)) * h
        ≤ (1096 * n ^ 4 * L * R * h) * h := mul_le_mul_of_nonneg_right hbig (le_of_lt hh0)
      _ = 1096 * n ^ 4 * L * R * h ^ 2 := by ring
  have hsq : (S ^ 4) ^ 2 ≤ (1096 * n ^ 4 * L * R / h) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hS4' 2
  have hdiv : (1096 * n ^ 4 * L * R) ^ 2 / h ^ 2 ≤ (1096 * n ^ 4 * L * R) ^ 2 / n :=
    div_le_div_of_nonneg_left (by positivity) hn0 hnh2
  have hval : (1096 * n ^ 4 * L * R) ^ 2 / n = 1201216 * R ^ 2 * n ^ 7 * L ^ 2 := by
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ R ^ 2 * n ^ 7 * L ^ 2 := by positivity
  calc S ^ 8 = (S ^ 4) ^ 2 := by ring
    _ ≤ (1096 * n ^ 4 * L * R / h) ^ 2 := hsq
    _ = (1096 * n ^ 4 * L * R) ^ 2 / h ^ 2 := by rw [div_pow]
    _ ≤ (1096 * n ^ 4 * L * R) ^ 2 / n := hdiv
    _ = 1201216 * R ^ 2 * n ^ 7 * L ^ 2 := hval
    _ ≤ 2 ^ 22 * R ^ 2 * n ^ 7 * L ^ 2 := by linarith

/-- **The cubic Weyl bound.**  With `H = ⌊√N⌋ + 1`, a coprime approximation
`|6α − a/q| ≤ 1/q²` with `q ≤ 4N` gives
`‖∑_{0 ≤ n < N} e(α n³)‖⁸ ≤ 2²² (4N/q + 1)² N⁷ (1 + log 4N)²`. -/
theorem norm_cubeSum_pow_eight_le_of_approx {α : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hqN : (q : ℝ) ≤ 4 * N) (hcop : IsCoprime (q : ℤ) a)
    (happ : |6 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖cubeSum α N‖ ^ 8
      ≤ 2 ^ 22 * (4 * (N : ℝ) / q + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set L : ℝ := 1 + Real.log (4 * N) with hLdef
  set R : ℝ := 4 * (N : ℝ) / q + 1 with hRdef
  have hL1 : 1 ≤ L := by
    have : (0 : ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    rw [hLdef]; linarith
  have hR1 : 1 ≤ R := by
    have : (0 : ℝ) ≤ 4 * (N : ℝ) / q := by positivity
    rw [hRdef]; linarith
  have hgoal : ‖cubeSum α N‖ ^ 8 ≤ 2 ^ 22 * R ^ 2 * (N : ℝ) ^ 7 * L ^ 2 := by
    rcases Nat.lt_or_ge N 2 with hsmall | hbig
    · -- the trivial bound covers the single small case `N = 1`
      have hN1 : N = 1 := by omega
      have htriv : ‖cubeSum α N‖ ≤ 1 := by
        rw [hN1]
        refine le_trans (norm_sum_le _ _) ?_
        simp [norm_e2pi]
      have h8 : ‖cubeSum α N‖ ^ 8 ≤ 1 := pow_le_one₀ (norm_nonneg _) htriv
      refine h8.trans ?_
      have hN1R : (N : ℝ) = 1 := by rw [hN1]; norm_num
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
      rw [hN1R]
      nlinarith [hL2, hR2]
    · set H : ℕ := Nat.sqrt N + 1 with hHdef
      have hH : 0 < H := Nat.succ_pos _
      have hNH2 : N < H ^ 2 := by
        have := Nat.lt_succ_sqrt' N
        rw [hHdef]; nlinarith [this]
      have hH24N : H ^ 2 ≤ 4 * N := by
        have h1 : 1 ≤ Nat.sqrt N := by
          have := Nat.sqrt_le_sqrt (show 1 ≤ N by omega)
          simpa using this
        have h2 := Nat.sqrt_le' N
        rw [hHdef]; nlinarith [h1, h2]
      have hHN : H ≤ N := by
        have h2 := Nat.sqrt_lt_self (show 1 < N by omega)
        rw [hHdef]; omega
      have hmain := norm_cubeSum_pow_four_le_of_approx hq hH hHN hcop happ
      have hh1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      have hh0 : (0 : ℝ) < (H : ℝ) := by linarith
      have hhn : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hHN
      have hnh2 : (N : ℝ) ≤ (H : ℝ) ^ 2 := by
        have : (N : ℝ) < ((H ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNH2
        push_cast at this; linarith
      have hh24n : (H : ℝ) ^ 2 ≤ 4 * (N : ℝ) := by
        have : ((H ^ 2 : ℕ) : ℝ) ≤ ((4 * N : ℕ) : ℝ) := by exact_mod_cast hH24N
        push_cast at this; linarith
      -- the diophantine factor and the logarithm
      have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hQ1
      have hlogq : 1 + Real.log q ≤ L := by
        have : Real.log q ≤ Real.log (4 * N) := Real.log_le_log hQ0 hqN
        rw [hLdef]; linarith
      have hfactor : 4 * (N : ℝ) + q * (1 + Real.log q) ≤ 8 * (N : ℝ) * L := by
        have h2 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
        have h1 : (q : ℝ) * (1 + Real.log q) ≤ 4 * (N : ℝ) * L := by
          nlinarith [hqN, hlogq, h2, hQ0]
        nlinarith [hL1, hn0]
      have hratio : (H : ℝ) ^ 2 / q + 1 ≤ R := by
        have : (H : ℝ) ^ 2 / q ≤ 4 * (N : ℝ) / q := by gcongr
        rw [hRdef]; linarith
      have hratio0 : (0 : ℝ) ≤ (H : ℝ) ^ 2 / q + 1 := by positivity
      have hfac0 : (0 : ℝ) ≤ 4 * (N : ℝ) + q * (1 + Real.log q) := by positivity
      have hB : ((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q)) ≤ 8 * (N : ℝ) * L * R := by
        calc ((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q))
            ≤ R * (8 * (N : ℝ) * L) := mul_le_mul hratio hfactor hfac0 (by linarith)
          _ = 8 * (N : ℝ) * L * R := by ring
      have hB0 : (0 : ℝ) ≤ ((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q)) :=
        mul_nonneg hratio0 hfac0
      exact cubic_bound_numeric hnR hh1 hhn hnh2 hL1 hR1 hB0 hB rfl hmain
  exact hgoal

/-- **An unconditional rate for a badly approximable coefficient.** -/
theorem norm_cubeSum_pow_eight_le_of_badlyApproximable {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |6 * α - (a : ℝ) / q|) {N : ℕ}
    (hN : 0 < N) :
    ‖cubeSum α N‖ ^ 8
      ≤ 2 ^ 22 * (4 / c + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨a, q, hq, hqle, hcop, happ⟩ := exists_coprime_approx (6 * α) hN
  have hQ0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqleR : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqle
  have happ2 : |6 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.trans ?_
    have h1 : (q : ℝ) ^ 2 ≤ (q : ℝ) * ((N : ℝ) + 1) := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) h1
  have hqbig : c * ((N : ℝ) + 1) ≤ q := le_den_of_badlyApproximable hbad hq happ
  have hq4N : (q : ℝ) ≤ 4 * N := by linarith
  have hmain := norm_cubeSum_pow_eight_le_of_approx hN hq hq4N hcop happ2
  refine hmain.trans ?_
  have hR : 4 * (N : ℝ) / q + 1 ≤ 4 / c + 1 := by
    have h1 : 4 * (N : ℝ) / q ≤ 4 / c := by
      rw [div_le_div_iff₀ hQ0 hc]
      nlinarith [hqbig, hnR, hc]
    linarith
  have hR0 : (0 : ℝ) ≤ 4 * (N : ℝ) / q + 1 := by positivity
  have hRsq : (4 * (N : ℝ) / q + 1) ^ 2 ≤ (4 / c + 1) ^ 2 := pow_le_pow_left₀ hR0 hR 2
  have hrest : (0 : ℝ) ≤ (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by
    have : (0 : ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    positivity
  calc 2 ^ 22 * (4 * (N : ℝ) / q + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2
      = 2 ^ 22 * (4 * (N : ℝ) / q + 1) ^ 2 * ((N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2) := by ring
    _ ≤ 2 ^ 22 * (4 / c + 1) ^ 2 * ((N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hrest
        have : (0 : ℝ) ≤ (2 : ℝ) ^ 22 := by positivity
        nlinarith [hRsq]
    _ = 2 ^ 22 * (4 / c + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by ring

/-- **The explicit instance** `α = √2/6`, for which `6α = √2` is badly approximable with `c = 1/4`:
`‖∑_{0 ≤ n < N} e((√2/6) n³)‖⁸ ≤ 2³¹ N⁷ (1 + log 4N)²`. -/
theorem norm_cubeSum_sqrt_two_le {N : ℕ} (hN : 0 < N) :
    ‖cubeSum (Real.sqrt 2 / 6) N‖ ^ 8
      ≤ 2 ^ 31 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbad : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ |6 * (Real.sqrt 2 / 6) - (a : ℝ) / q| := by
    intro a q hq
    have h6 : 6 * (Real.sqrt 2 / 6) = Real.sqrt 2 := by ring
    rw [h6]
    exact badlyApproximable_sqrt_two a q hq
  have hmain := norm_cubeSum_pow_eight_le_of_badlyApproximable (by norm_num : (0 : ℝ) < 1 / 4)
    hbad hN
  refine hmain.trans ?_
  have hrest : (0 : ℝ) ≤ (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by
    have : (0 : ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    positivity
  have hconst : (2 : ℝ) ^ 22 * (4 / (1 / 4 : ℝ) + 1) ^ 2 ≤ 2 ^ 31 := by norm_num
  calc 2 ^ 22 * (4 / (1 / 4 : ℝ) + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2
      = (2 ^ 22 * (4 / (1 / 4 : ℝ) + 1) ^ 2) * ((N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2) := by
        ring
    _ ≤ 2 ^ 31 * ((N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2) :=
        mul_le_mul_of_nonneg_right hconst hrest
    _ = 2 ^ 31 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 := by ring

end WeylCubic

end RiemannHypothesis
