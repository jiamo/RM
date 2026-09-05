/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylGeneral
import RiemannHypothesis.DivisorBound

/-!
# Weyl's inequality with the classical exponent: folding the shifts with the divisor bound

`RiemannHypothesis.WeylGeneral` proves Weyl's inequality in degree `d`,

`‖S‖^(2^(d-1)) · H^(d-1) (N + H) ≤ 8^(2^(d-1)) (N + H)^(2^(d-1)) · W_{d-1}(d! α)`,

and estimates the `(d − 1)`-fold majorant sum `W_{d-1}` by folding the tuples of shifts onto
their product *crudely*: each of the `H^{d-2}` remaining tuples is allowed a whole
one-dimensional sum.  That costs a factor `H^{d-2}` and leaves the exponent
`1 − 1/((d−1) 2^(d−1))`, weaker than Weyl's `1 − 1/2^(d−1)`; the open boundary of
`M1-WEYL-GENERAL` named the missing ingredient, the divisor bound.

This file supplies it.  `RiemannHypothesis.DivisorBound.sum_mul_divisor_le` says that folding one
variable into the product multiplies the weight by one factor of `τ`, so that the `r + 1`-fold
majorant sum satisfies

`W_{r+1}(β, N, H, m) ≤ (r + 1) H^r N + ∑_{u ≤ H^{r+1}} τ(u)^r · min(N, 1/(2‖β m u‖))`

(`weylMulti_le_divisorSum`), the term `(r + 1) H^r N` being the tuples with a zero entry.  The
divisor bound `τ(u) ≤ C_ε u^ε` then costs only `C_ε^r H^{(r+1) r ε}` instead of `H^r`, and with
the number of shifts taken as large as the range, `H = N`, the classical exponent follows.

## Main results

* `weylMulti_le_divisorSum` — the `r + 1`-fold majorant sum folded onto the product of the shifts,
  each product weighted by the number `τ^r` of its factorizations;
* `sum_divisorWeight_le` — that weighted sum estimated by the divisor bound and the counting
  lemma of `RiemannHypothesis.WeylMinSum`;
* `weylMulti_le_of_approx_divisor` — the two combined, from a coprime approximation
  `|β − a/q| ≤ 1/q²`;
* `norm_monomialSum_pow_mul_le_of_approx_divisor` — **Weyl's inequality for the monomial phase
  `α n^(r+2)` with the classical exponent**: if `|(r+2)! α − a/q| ≤ 1/q²` with `q` coprime to `a`
  and `N ≤ q ≤ N^(r+1)`, then

  `‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · N`
  `  ≤ 16^(2^(r+1)) N^(2^(r+1)) · D · (r + 11 + 2(r+1) log N)`

  with `D = (C_ε N^((r+1) ε))^r` the divisor loss;
* `exists_norm_monomialSum_pow_mul_le` — the same with the loss absorbed into `N^ε`: for every
  `ε > 0` there is a constant `C` with
  `‖∑_{n<N} e(α n^(r+2))‖^(2^(r+1)) · N ≤ C N^(2^(r+1)) N^ε`, i.e.
  `‖∑_{n<N} e(α n^d)‖ ≤ C' N^(1 − 1/2^(d−1) + ε)` for `d = r + 2`, **Weyl's exponent**.

## Scope

The hypothesis `N ≤ q ≤ N^(d-1)` on the denominator is what taking `H = N` shifts allows; the
classical statement covers `q ≤ N^d` and carries the three terms `1/q + 1/N + q/N^d`, which is not
proved here.  The constants are not optimized.  Vinogradov's mean value theorem — what degrees
beyond the reach of Weyl's method need — is not formalized.  Nothing about `ζ` follows: polynomial
phases are not zeta phases.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace WeylDivisor

open KusminLandau WeylQuadratic WeylCubic WeylGeneral DivisorBound

/-! ## Folding the shifts onto their product -/

/-- The majorant at the shift `0` is the trivial bound `N`. -/
theorem dioMaj_zero (β : ℝ) (N : ℕ) : dioMaj β N 0 = (N : ℝ) := by
  simp [dioMaj, intDist]

/-- Reindexing `[1, M]` as `{1 + i : i < M}`. -/
theorem sum_Icc_one_eq_range {M : ℕ} (f : ℕ → ℝ) :
    ∑ u ∈ Finset.Icc 1 M, f u = ∑ i ∈ Finset.range M, f (1 + i) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp

/-- The base case of `weylMulti_le_divisorSum`: one shift, no divisor weight. -/
theorem weylMulti_le_divisorSum_base (β : ℝ) (N H : ℕ) (m : ℤ) :
    weylMulti β N H 1 m
      ≤ (N : ℝ) + ∑ u ∈ Finset.Icc 1 H, (#u.divisors : ℝ) ^ 0 * dioMaj β N (m * (u : ℤ)) := by
  classical
  rw [weylMulti_succ]
  have hIcc : ∑ u ∈ Finset.Icc 1 H, (#u.divisors : ℝ) ^ 0 * dioMaj β N (m * (u : ℤ))
      = ∑ i ∈ Finset.range H, dioMaj β N (m * ((1 + i : ℕ) : ℤ)) := by
    rw [sum_Icc_one_eq_range (fun u => (#u.divisors : ℝ) ^ 0 * dioMaj β N (m * (u : ℤ)))]
    simp
  rw [hIcc]
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun k => weylMulti β N (H' + 1) 0 (m * (k : ℤ))) H']
    have hzero : weylMulti β N (H' + 1) 0 (m * ((0 : ℕ) : ℤ)) = (N : ℝ) := by
      simp [weylMulti_zero, dioMaj_zero]
    rw [hzero]
    have hterms : ∑ i ∈ Finset.range H', weylMulti β N (H' + 1) 0 (m * ((i + 1 : ℕ) : ℤ))
        = ∑ i ∈ Finset.range H', dioMaj β N (m * ((i + 1 : ℕ) : ℤ)) := by
      simp [weylMulti_zero]
    rw [hterms]
    have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℤ) = ((1 + i : ℕ) : ℤ) := by intro i; push_cast; ring
    simp_rw [hcast]
    have hsub : ∑ i ∈ Finset.range H', dioMaj β N (m * ((1 + i : ℕ) : ℤ))
        ≤ ∑ i ∈ Finset.range (H' + 1), dioMaj β N (m * ((1 + i : ℕ) : ℤ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => dioMaj_nonneg _ _ _)
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    linarith

/-- **The majorant sum folded onto the product of the shifts, with the divisor weight.**  The
tuples with a zero entry contribute the trivial bound `N` each — at most `(r + 1) H^r` of them —
and every other tuple is counted with its product `u ≤ H^(r+1)`, a product being reached by at
most `τ(u)^r` tuples. -/
theorem weylMulti_le_divisorSum (β : ℝ) (N H : ℕ) :
    ∀ (s : ℕ) (m : ℤ), weylMulti β N H (s + 1) m
      ≤ ((s : ℝ) + 1) * (H : ℝ) ^ s * N
        + ∑ u ∈ Finset.Icc 1 (H ^ (s + 1)), (#u.divisors : ℝ) ^ s * dioMaj β N (m * (u : ℤ)) := by
  intro s
  induction s with
  | zero => intro m; simpa using weylMulti_le_divisorSum_base β N H m
  | succ s ih =>
    intro m
    rw [weylMulti_succ]
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    · obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
      set Hn : ℕ := H' + 1 with hHn
      rw [Finset.sum_range_succ' (fun k => weylMulti β N Hn (s + 1) (m * (k : ℤ))) H']
      have hzero : weylMulti β N Hn (s + 1) (m * ((0 : ℕ) : ℤ)) = (Hn : ℝ) ^ (s + 1) * N := by
        simpa using weylMulti_zero_arg β N Hn (s + 1)
      rw [hzero]
      set F : ℕ → ℝ := fun w => dioMaj β N (m * (w : ℤ)) with hF
      have hFnn : ∀ w, 0 ≤ F w := fun w => dioMaj_nonneg _ _ _
      have hterm : ∀ i ∈ Finset.range H',
          weylMulti β N Hn (s + 1) (m * ((i + 1 : ℕ) : ℤ))
            ≤ ((s : ℝ) + 1) * (Hn : ℝ) ^ s * N
              + ∑ u ∈ Finset.Icc 1 (Hn ^ (s + 1)), (#u.divisors : ℝ) ^ s * F ((1 + i) * u) := by
        intro i _
        have hIH := ih (m * ((i + 1 : ℕ) : ℤ))
        refine hIH.trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl (fun u _ => ?_)
        have hEq : F ((1 + i) * u) = dioMaj β N (m * ((i + 1 : ℕ) : ℤ) * (u : ℤ)) := by
          simp only [hF]
          congr 1
          push_cast
          ring
        rw [hEq]
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hdouble : ∑ i ∈ Finset.range H',
            ∑ u ∈ Finset.Icc 1 (Hn ^ (s + 1)), (#u.divisors : ℝ) ^ s * F ((1 + i) * u)
          = ∑ k ∈ Finset.Icc 1 H',
            ∑ u ∈ Finset.Icc 1 (Hn ^ (s + 1)), (#u.divisors : ℝ) ^ s * F (k * u) := by
        rw [sum_Icc_one_eq_range
          (fun k => ∑ u ∈ Finset.Icc 1 (Hn ^ (s + 1)), (#u.divisors : ℝ) ^ s * F (k * u))]
      have hfold := sum_mul_divisor_le H' (Hn ^ (s + 1)) s F hFnn
      have hmono : ∑ v ∈ Finset.Icc 1 (H' * Hn ^ (s + 1)), (#v.divisors : ℝ) ^ (s + 1) * F v
          ≤ ∑ v ∈ Finset.Icc 1 (Hn ^ (s + 1 + 1)), (#v.divisors : ℝ) ^ (s + 1) * F v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun v _ _ => mul_nonneg (by positivity) (hFnn v))
        refine Finset.Icc_subset_Icc_right ?_
        calc H' * Hn ^ (s + 1) ≤ Hn * Hn ^ (s + 1) := Nat.mul_le_mul_right _ (by omega)
          _ = Hn ^ (s + 1 + 1) := by ring
      have hH'le : (H' : ℝ) ≤ (Hn : ℝ) := by rw [hHn]; push_cast; linarith
      have hkey : (H' : ℝ) * (((s : ℝ) + 1) * (Hn : ℝ) ^ s * N)
          ≤ ((s : ℝ) + 1) * (Hn : ℝ) ^ (s + 1) * N := by
        have h1 : (H' : ℝ) * (((s : ℝ) + 1) * (Hn : ℝ) ^ s * N)
            ≤ (Hn : ℝ) * (((s : ℝ) + 1) * (Hn : ℝ) ^ s * N) :=
          mul_le_mul_of_nonneg_right hH'le (by positivity)
        calc (H' : ℝ) * (((s : ℝ) + 1) * (Hn : ℝ) ^ s * N)
            ≤ (Hn : ℝ) * (((s : ℝ) + 1) * (Hn : ℝ) ^ s * N) := h1
          _ = ((s : ℝ) + 1) * (Hn : ℝ) ^ (s + 1) * N := by ring
      rw [hdouble] at hsum
      push_cast at hsum hfold hmono hkey ⊢
      linarith [hsum, hfold, hmono, hkey]

/-! ## Estimating the folded sum -/

/-- The majorant sum along the multiples of `m`, compared with the one-dimensional majorant sum. -/
theorem sum_Icc_dioMaj_mul_le (β : ℝ) (N V : ℕ) {m : ℤ} (hm : 0 < m) :
    ∑ u ∈ Finset.Icc 1 V, dioMaj β N (m * (u : ℤ)) ≤ dioSum β N (m * (V : ℤ)) := by
  classical
  have himg : ∑ u ∈ Finset.Icc 1 V, dioMaj β N (m * (u : ℤ))
      = ∑ t ∈ (Finset.Icc 1 V).image (fun u : ℕ => m * (u : ℤ)), dioMaj β N t := by
    refine (Finset.sum_image ?_).symm
    intro x _ y _ hxy
    have hxy' : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ (by omega) hxy
    exact_mod_cast hxy'
  rw [himg, dioSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => dioMaj_nonneg _ _ _
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  rw [Finset.mem_Icc] at hu
  rw [Finset.mem_Ioc]
  refine ⟨?_, mul_le_mul_of_nonneg_left (by exact_mod_cast hu.2) hm.le⟩
  have h1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu.1
  positivity

/-- **The divisor weight, discharged by the divisor bound.**  On `[1, V]` the weight `τ(u)^s` is at
most `(C V^ε)^s`, so the weighted sum is at most that constant times the one-dimensional majorant
sum. -/
theorem sum_divisorWeight_le {β : ℝ} {N : ℕ} {m : ℤ} (hm : 0 < m) (V s : ℕ)
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    ∑ u ∈ Finset.Icc 1 V, (#u.divisors : ℝ) ^ s * dioMaj β N (m * (u : ℤ))
      ≤ (C * (V : ℝ) ^ ε) ^ s * dioSum β N (m * (V : ℤ)) := by
  have hstep : ∀ u ∈ Finset.Icc 1 V, (#u.divisors : ℝ) ^ s * dioMaj β N (m * (u : ℤ))
      ≤ (C * (V : ℝ) ^ ε) ^ s * dioMaj β N (m * (u : ℤ)) := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    exact mul_le_mul_of_nonneg_right
      (card_divisors_pow_le hε hC hbound s V u (by omega) hu.2) (dioMaj_nonneg _ _ _)
  calc ∑ u ∈ Finset.Icc 1 V, (#u.divisors : ℝ) ^ s * dioMaj β N (m * (u : ℤ))
      ≤ ∑ u ∈ Finset.Icc 1 V, (C * (V : ℝ) ^ ε) ^ s * dioMaj β N (m * (u : ℤ)) :=
        Finset.sum_le_sum hstep
    _ = (C * (V : ℝ) ^ ε) ^ s * ∑ u ∈ Finset.Icc 1 V, dioMaj β N (m * (u : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ (C * (V : ℝ) ^ ε) ^ s * dioSum β N (m * (V : ℤ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_dioMaj_mul_le β N V hm) (by positivity)

/-- **The `r + 1`-fold majorant sum, estimated with the divisor bound.**  The loss over the
one-dimensional sum is the divisor factor `(C (H^(r+1))^ε)^r`, not the factor `H^r` of
`RiemannHypothesis.WeylGeneral.weylMulti_le_of_approx`. -/
theorem weylMulti_le_of_approx_divisor {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hcop : IsCoprime (q : ℤ) a) (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H s : ℕ)
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    weylMulti β N H (s + 1) 1
      ≤ ((s : ℝ) + 1) * (H : ℝ) ^ s * N
        + (C * ((H : ℝ) ^ (s + 1)) ^ ε) ^ s
          * (((H : ℝ) ^ (s + 1) / q + 1) * (4 * N + q * (1 + Real.log q))) := by
  have hfold := weylMulti_le_divisorSum β N H s 1
  have hweight := sum_divisorWeight_le (β := β) (N := N) (m := 1) one_pos (H ^ (s + 1)) s
    hε hC hbound
  have hcount := dioSum_le_of_approx hq hcop happ N (H ^ (s + 1))
  have hVcast : ((H ^ (s + 1) : ℕ) : ℝ) = (H : ℝ) ^ (s + 1) := by push_cast; ring
  have hVcastZ : ((1 : ℤ) * ((H ^ (s + 1) : ℕ) : ℤ)) = ((H ^ (s + 1) : ℕ) : ℤ) := one_mul _
  rw [hVcastZ] at hweight
  rw [hVcast] at hweight
  have hDnn : (0 : ℝ) ≤ (C * ((H : ℝ) ^ (s + 1)) ^ ε) ^ s := by positivity
  have hchain : (C * ((H : ℝ) ^ (s + 1)) ^ ε) ^ s * dioSum β N ((H ^ (s + 1) : ℕ) : ℤ)
      ≤ (C * ((H : ℝ) ^ (s + 1)) ^ ε) ^ s
        * (((H : ℝ) ^ (s + 1) / q + 1) * (4 * N + q * (1 + Real.log q))) := by
    refine mul_le_mul_of_nonneg_left ?_ hDnn
    rw [← hVcast]
    exact hcount
  linarith [hfold, hweight, hchain]

/-! ## Weyl's inequality with the classical exponent -/

/-- **Weyl's inequality for the monomial phase `α n^(r+2)`, with the classical exponent.**  With
`H = N` shifts, a coprime approximation `|(r+2)! α − a/q| ≤ 1/q²` whose denominator satisfies
`N ≤ q ≤ N^(r+1)` gives

`‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · N ≤ 16^(2^(r+1)) N^(2^(r+1)) D (r + 11 + 2(r+1) log N)`,

`D = (C (N^(r+1))^ε)^r` being the divisor loss. -/
theorem norm_monomialSum_pow_mul_le_of_approx_divisor {α : ℝ} {a : ℤ} {q : ℕ} (r : ℕ)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N) (hqN : N ≤ q) (hqNr : (q : ℝ) ≤ (N : ℝ) ^ (r + 1))
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * N
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r * ((r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N) := by
  set K : ℕ := 2 ^ (r + 1) with hKdef
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ with hS
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqNR : (N : ℝ) ≤ q := by exact_mod_cast hqN
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNpow : (0 : ℝ) < (N : ℝ) ^ (r + 1) := by positivity
  set D : ℝ := (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r with hD
  have hDone : 1 ≤ D := by
    have hb : (1 : ℝ) ≤ ((N : ℝ) ^ (r + 1)) ^ ε := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (r + 1) := one_le_pow₀ hN1
      exact Real.one_le_rpow h1 hε.le
    have : (1 : ℝ) ≤ C * ((N : ℝ) ^ (r + 1)) ^ ε := by nlinarith
    exact one_le_pow₀ this
  set L : ℝ := (r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N with hL
  have hLnn : 0 ≤ L := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) * Real.log N := by positivity
    rw [hL]; linarith
  -- Weyl differencing with `H = N` shifts
  have hmain := WeylGeneral.norm_polyPhaseSum_pow_le (r + 1)
    (WeylGeneral.isPolyPhase_monomial (r + 2) α) N N hN
  have hfac : (r + 1 + 1).factorial = (r + 2).factorial := rfl
  rw [hfac] at hmain
  -- the majorant sum, folded with the divisor bound
  have hcount := weylMulti_le_of_approx_divisor hq hcop happ N N r hε hC hbound
  -- the counting bracket
  have hinner : 4 * (N : ℝ) + q * (1 + Real.log q) ≤ (q : ℝ) * (5 + Real.log q) := by
    have hexp : (q : ℝ) * (5 + Real.log q) = 4 * q + q * (1 + Real.log q) := by ring
    linarith
  have hlogqN : Real.log q ≤ ((r : ℝ) + 1) * Real.log N := by
    have h1 : Real.log q ≤ Real.log ((N : ℝ) ^ (r + 1)) := Real.log_le_log hqR hqNr
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have hprod : ((N : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))
      ≤ (N : ℝ) ^ (r + 1) * (10 + 2 * ((r : ℝ) + 1) * Real.log N) := by
    have hfr : (0 : ℝ) ≤ (N : ℝ) ^ (r + 1) / q + 1 := by positivity
    have hstep1 : ((N : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))
        ≤ ((N : ℝ) ^ (r + 1) / q + 1) * ((q : ℝ) * (5 + Real.log q)) :=
      mul_le_mul_of_nonneg_left hinner hfr
    have hid : ((N : ℝ) ^ (r + 1) / q + 1) * ((q : ℝ) * (5 + Real.log q))
        = ((N : ℝ) ^ (r + 1) + q) * (5 + Real.log q) := by
      field_simp
    have hstep2 : ((N : ℝ) ^ (r + 1) + q) * (5 + Real.log q)
        ≤ (2 * (N : ℝ) ^ (r + 1)) * (5 + Real.log q) := by
      refine mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hstep3 : (2 * (N : ℝ) ^ (r + 1)) * (5 + Real.log q)
        ≤ (2 * (N : ℝ) ^ (r + 1)) * (5 + ((r : ℝ) + 1) * Real.log N) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hid2 : (2 * (N : ℝ) ^ (r + 1)) * (5 + ((r : ℝ) + 1) * Real.log N)
        = (N : ℝ) ^ (r + 1) * (10 + 2 * ((r : ℝ) + 1) * Real.log N) := by ring
    linarith
  have hbracket : ((r : ℝ) + 1) * (N : ℝ) ^ r * N
        + D * (((N : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q)))
      ≤ D * ((N : ℝ) ^ (r + 1) * L) := by
    have hDnn : (0 : ℝ) ≤ D := by linarith
    have h1 : D * (((N : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q)))
        ≤ D * ((N : ℝ) ^ (r + 1) * (10 + 2 * ((r : ℝ) + 1) * Real.log N)) :=
      mul_le_mul_of_nonneg_left hprod hDnn
    have h2 : ((r : ℝ) + 1) * (N : ℝ) ^ r * N ≤ D * ((N : ℝ) ^ (r + 1) * ((r : ℝ) + 1)) := by
      have hid : ((r : ℝ) + 1) * (N : ℝ) ^ r * N = 1 * ((N : ℝ) ^ (r + 1) * ((r : ℝ) + 1)) := by
        rw [pow_succ]; ring
      rw [hid]
      refine mul_le_mul_of_nonneg_right hDone ?_
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      positivity
    have hid3 : D * ((N : ℝ) ^ (r + 1) * L)
        = D * ((N : ℝ) ^ (r + 1) * ((r : ℝ) + 1))
          + D * ((N : ℝ) ^ (r + 1) * (10 + 2 * ((r : ℝ) + 1) * Real.log N)) := by
      rw [hL]; ring
    linarith
  have hpre : (0 : ℝ) ≤ 8 ^ K * ((N : ℝ) + N) ^ K := by positivity
  have hstep : S ^ K * ((N : ℝ) ^ (r + 1) * ((N : ℝ) + N))
      ≤ 8 ^ K * ((N : ℝ) + N) ^ K * (D * ((N : ℝ) ^ (r + 1) * L)) :=
    hmain.trans (mul_le_mul_of_nonneg_left (hcount.trans hbracket) hpre)
  -- cancel the common factor `N^(r+1)`
  have h2N : ((N : ℝ) + N) ^ K = 2 ^ K * (N : ℝ) ^ K := by
    rw [show (N : ℝ) + N = 2 * N by ring, mul_pow]
  have h16 : (16 : ℝ) ^ K = 8 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  have hcancel : (S ^ K * N * 2) * (N : ℝ) ^ (r + 1)
      ≤ (16 ^ K * (N : ℝ) ^ K * D * L) * (N : ℝ) ^ (r + 1) := by
    calc (S ^ K * N * 2) * (N : ℝ) ^ (r + 1)
        = S ^ K * ((N : ℝ) ^ (r + 1) * ((N : ℝ) + N)) := by ring
      _ ≤ 8 ^ K * ((N : ℝ) + N) ^ K * (D * ((N : ℝ) ^ (r + 1) * L)) := hstep
      _ = (16 ^ K * (N : ℝ) ^ K * D * L) * (N : ℝ) ^ (r + 1) := by rw [h2N, h16]; ring
  have hred : S ^ K * N * 2 ≤ 16 ^ K * (N : ℝ) ^ K * D * L :=
    le_of_mul_le_mul_right hcancel hNpow
  have hSnn : (0 : ℝ) ≤ S ^ K * N := by positivity
  linarith

/-- **Weyl's exponent.**  For every `ε > 0` there is a constant `C` such that, whenever
`|(r+2)! α − a/q| ≤ 1/q²` with `q` coprime to `a` and `N ≤ q ≤ N^(r+1)`,

`‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · N ≤ C N^(2^(r+1)) N^ε`;

that is, `‖∑_{n<N} e(α n^d)‖ ≤ C' N^(1 − 1/2^(d−1) + ε)` for `d = r + 2`. -/
theorem exists_norm_monomialSum_pow_mul_le (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (a : ℤ) (q N : ℕ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N → N ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * N
        ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
  set e0 : ℝ := ε / (2 * (((r : ℝ) + 1) * r + 1)) with he0
  have hden : (0 : ℝ) < 2 * (((r : ℝ) + 1) * r + 1) := by positivity
  have he0pos : 0 < e0 := div_pos hε hden
  obtain ⟨C0, hC0, hbound⟩ := DivisorBound.exists_card_divisors_le he0pos
  set A : ℝ := (r : ℝ) + 11 + 4 * ((r : ℝ) + 1) / ε with hA
  have hA1 : 1 ≤ A := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (0 : ℝ) ≤ 4 * ((r : ℝ) + 1) / ε := by positivity
    rw [hA]; linarith
  refine ⟨16 ^ (2 ^ (r + 1)) * C0 ^ r * A, ?_, ?_⟩
  · have h16 : (1 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) := one_le_pow₀ (by norm_num)
    have hC0r : (1 : ℝ) ≤ C0 ^ r := one_le_pow₀ hC0
    have hprod : (1 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * C0 ^ r := by nlinarith
    nlinarith
  intro α a q N hq hcop happ hN hqN hqNr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hmain := norm_monomialSum_pow_mul_le_of_approx_divisor r hq hcop happ hN hqN hqNr
    he0pos hC0 hbound
  -- the divisor loss `D` is at most `C0^r N^(ε/2)`
  have hrpow : ((N : ℝ) ^ (r + 1)) ^ e0 = (N : ℝ) ^ (((r : ℝ) + 1) * e0) := by
    rw [← Real.rpow_natCast (N : ℝ) (r + 1), ← Real.rpow_mul hNpos.le]
    push_cast
    ring_nf
  have hDle : (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r ≤ C0 ^ r * (N : ℝ) ^ (ε / 2) := by
    rw [mul_pow, hrpow, ← Real.rpow_natCast ((N : ℝ) ^ (((r : ℝ) + 1) * e0)) r,
      ← Real.rpow_mul hNpos.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hne : (2 * (((r : ℝ) + 1) * r + 1)) ≠ 0 := ne_of_gt hden
    have hid : ε / 2 = e0 * (((r : ℝ) + 1) * r + 1) := by
      rw [he0]; field_simp
    have hdiff : e0 * (((r : ℝ) + 1) * r + 1) - ((r : ℝ) + 1) * e0 * r = e0 := by ring
    rw [hid]
    linarith [he0pos]
  -- the logarithm is absorbed into `N^(ε/2)`
  have hhalf : 0 < ε / 2 := by linarith
  have hNhalf : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 hhalf.le
  have hlog : Real.log N ≤ (N : ℝ) ^ (ε / 2) / (ε / 2) :=
    Real.log_le_rpow_div hNpos.le hhalf
  have hLle : (r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N ≤ A * (N : ℝ) ^ (ε / 2) := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : 2 * ((r : ℝ) + 1) * Real.log N
        ≤ 2 * ((r : ℝ) + 1) * ((N : ℝ) ^ (ε / 2) / (ε / 2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h3 : 2 * ((r : ℝ) + 1) * ((N : ℝ) ^ (ε / 2) / (ε / 2))
        = (4 * ((r : ℝ) + 1) / ε) * (N : ℝ) ^ (ε / 2) := by
      field_simp
      ring
    have h4 : (r : ℝ) + 11 ≤ ((r : ℝ) + 11) * (N : ℝ) ^ (ε / 2) := by nlinarith
    have h5 : A * (N : ℝ) ^ (ε / 2)
        = ((r : ℝ) + 11) * (N : ℝ) ^ (ε / 2) + (4 * ((r : ℝ) + 1) / ε) * (N : ℝ) ^ (ε / 2) := by
      rw [hA]; ring
    linarith
  -- assemble
  have hLnn : (0 : ℝ) ≤ (r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) * Real.log N := by
      have := Real.log_nonneg hN1
      positivity
    linarith
  have hpre : (0 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) := by positivity
  have hstep : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r * ((r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N)
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) * (A * (N : ℝ) ^ (ε / 2)) := by
    have hD0 : (0 : ℝ) ≤ (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r := by positivity
    have h1 : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
          * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r
        ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hDle hpre
    have h2 : (0 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) := by positivity
    calc 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
            * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r
            * ((r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N)
        ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2))
            * ((r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N) :=
          mul_le_mul_of_nonneg_right h1 hLnn
      _ ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2))
            * (A * (N : ℝ) ^ (ε / 2)) := mul_le_mul_of_nonneg_left hLle h2
  have hsplit : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hfinal : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) * (A * (N : ℝ) ^ (ε / 2))
      = 16 ^ (2 ^ (r + 1)) * C0 ^ r * A * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
    rw [← hsplit]; ring
  linarith [hmain.trans hstep, le_of_eq hfinal]

end WeylDivisor

end RiemannHypothesis
