/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylCubic

/-!
# Weyl's inequality in arbitrary degree: the A process iterated `d − 1` times

`RiemannHypothesis.WeylQuadratic` applies van der Corput's A process once, to a quadratic phase,
and `RiemannHypothesis.WeylCubic` applies it twice, to a cubic one.  This file carries out the
induction: for a polynomial phase of degree `d` the process is applied `d − 1` times, each step
lowering the degree by one, until the phase is linear and is summed by the geometric-series bound.
That closes the case named as missing by the open boundaries of `M1-WEYL-QUADRATIC` and
`M1-WEYL-CUBIC` ("the general degree-`d` Weyl inequality, by induction on `d`").

## The statement

Write `K = 2^(d-1)`, let `f` be any real polynomial phase of degree at most `d` whose coefficient
of `n^d` is `α`, and let `S = ∑_{0 ≤ n < N} e(f n)`.  With `H ≥ 1` shifts,

  `‖S‖^K · H^(d-1) (N + H) ≤ 8^K (N + H)^K · W_{d-1}(d! α, N, H, 1)`,

where `W_r` is the `r`-fold shifted majorant sum

  `W_0(β, N, H, m) = min(N, 1/(2‖β m‖))`,   `W_{r+1}(β, N, H, m) = ∑_{0 ≤ k < H} W_r(β, N, H, m k)`

(the majorant `dioMaj` of `RiemannHypothesis.WeylCubic`, whose value at `m = 0` is `N`).  The zero
shifts are *included* in `W`, and they are what absorbs the diagonal term `N` of each application
of the A process; this is why the statement has no additive error term.

## The mechanism

The A process, `RiemannHypothesis.WeylDifferencing.norm_sq_sum_e2pi_le`, gives

  `H ‖S‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} ‖S_k‖)`,   `S_k = ∑_n e(f(n+k) − f n)`,

and `f(· + k) − f(·)` is again a polynomial phase, of degree `d − 1`, with leading coefficient
`d k α` (`IsPolyPhase.diff`).  Feeding the inductive hypothesis into the shifts, after Hölder
`(∑_k ‖S_k‖)^K ≤ H^(K−1) ∑_k ‖S_k‖^K`, folds the shift `k` into the outermost variable of `W`,
because `W_r(β c, N, H, m) = W_r(β, N, H, c m)`; and the diagonal `N` is absorbed by the term
`k = 0` of the same sum, which equals `H^(r) N`.  The constants multiply as
`C_{d+1} = 2^(K−1) + 2^(2K−1) C_d`, which `8^K` dominates.

## Main results

* `weylMulti` — the `r`-fold shifted majorant sum, defined by recursion on `r`;
* `IsPolyPhase` — "`f` is a polynomial phase of degree at most `d` with `n^d`-coefficient `α`";
* `IsPolyPhase.diff` — differencing lowers the degree and multiplies the leading coefficient
  by `d k`;
* `norm_polyPhaseSum_pow_le` — **Weyl's inequality in degree `d`**, the displayed inequality above;
* `dioSum`, `weylMulti_le_dioSum` — the `r`-fold majorant sum folded onto the one-dimensional
  majorant sum in the product of the shifts;
* `weylMulti_le_of_approx` — the majorant sum estimated through the counting lemma
  `RiemannHypothesis.WeylQuadratic.sum_Ioc_le` (of `RiemannHypothesis.WeylMinSum`), from a
  coprime approximation `|d! α − a/q| ≤ 1/q²`;
* `norm_monomialSum_pow_le_of_approx` — the two combined, for the monomial phase `α n^d`;
* `norm_monomialSum_pow_mul_le_of_approx` — the resulting power saving, in the explicit form
  `‖∑_{n<N} e(α n^d)‖^(2^(d−1)) H ≤ 16^(2^(d−1)) N^(2^(d−1)) (d + 9 + 2 log N)` valid whenever
  `H^(d−1) ≤ q ≤ N`, which for `H` of size `N^(1/(d−1))` is a saving of `N^(−1/((d−1) 2^(d−1)))`
  over the trivial bound, up to the logarithm.

## Scope

The exponent obtained is `1 − 1/((d−1) 2^(d−1))`, weaker than the classical Weyl exponent
`1 − 1/2^(d−1)`: the loss is the crude folding of the `(d−1)`-tuples of shifts onto their product,
where the classical argument uses the average divisor bound `∑_{m ≤ M} τ(m) ≪ M log M`, which is
not formalized here.  For `d = 3` the two agree with the `7/8` of `RiemannHypothesis.WeylCubic`.
The constants are not optimized, the logarithm is not removed, and Vinogradov's mean value
theorem — what degrees beyond the reach of Weyl's method need — is not formalized.  As it must be,
the bound is conditional on a rational approximation to `d! α` with a large denominator.  Nothing
about `ζ` follows: polynomial phases are not zeta phases.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylGeneral

open KusminLandau WeylDifferencing WeylQuadratic WeylCubic

/-! ## The `r`-fold shifted majorant sum -/

/-- The `r`-fold shifted majorant sum: `W_0 (β, N, H, m) = dioMaj β N m` and
`W_{r+1}(β, N, H, m) = ∑_{0 ≤ k < H} W_r (β, N, H, m k)`.  The shift `k = 0` is included; the
corresponding term is `N`, and it is what absorbs the diagonal term of the A process. -/
def weylMulti (β : ℝ) (N H : ℕ) : ℕ → ℤ → ℝ
  | 0, m => dioMaj β N m
  | (r + 1), m => ∑ k ∈ Finset.range H, weylMulti β N H r (m * (k : ℤ))

theorem weylMulti_zero (β : ℝ) (N H : ℕ) (m : ℤ) : weylMulti β N H 0 m = dioMaj β N m := rfl

theorem weylMulti_succ (β : ℝ) (N H : ℕ) (r : ℕ) (m : ℤ) :
    weylMulti β N H (r + 1) m = ∑ k ∈ Finset.range H, weylMulti β N H r (m * (k : ℤ)) := rfl

theorem weylMulti_nonneg (β : ℝ) (N H : ℕ) (r : ℕ) (m : ℤ) : 0 ≤ weylMulti β N H r m := by
  induction r generalizing m with
  | zero => exact dioMaj_nonneg _ _ _
  | succ r ih => exact Finset.sum_nonneg fun k _ => ih _

/-- The value at `m = 0`: every leaf is `dioMaj β N 0 = N`. -/
theorem weylMulti_zero_arg (β : ℝ) (N H : ℕ) (r : ℕ) :
    weylMulti β N H r 0 = (H : ℝ) ^ r * N := by
  induction r with
  | zero =>
      simp [weylMulti, dioMaj, intDist]
  | succ r ih =>
      rw [weylMulti_succ]
      simp only [zero_mul, ih]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Scaling the frequency is the same as scaling the argument. -/
theorem weylMulti_mul (β : ℝ) (N H : ℕ) (r : ℕ) (c m : ℤ) :
    weylMulti (β * (c : ℝ)) N H r m = weylMulti β N H r (c * m) := by
  induction r generalizing m with
  | zero =>
      simp only [weylMulti_zero, dioMaj]
      have : β * (c : ℝ) * (m : ℝ) = β * ((c * m : ℤ) : ℝ) := by push_cast; ring
      rw [this]
  | succ r ih =>
      rw [weylMulti_succ, weylMulti_succ]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih]
      congr 1
      ring

/-- The majorant is monotone in the length `N`. -/
theorem dioMaj_mono_length {β : ℝ} {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) (m : ℤ) :
    dioMaj β N₁ m ≤ dioMaj β N₂ m := by
  have hR : (N₁ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast h
  unfold dioMaj
  split_ifs with h0
  · exact hR
  · exact min_le_min hR le_rfl

theorem weylMulti_mono_length {β : ℝ} {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) (H : ℕ) (r : ℕ) (m : ℤ) :
    weylMulti β N₁ H r m ≤ weylMulti β N₂ H r m := by
  induction r generalizing m with
  | zero => exact dioMaj_mono_length h m
  | succ r ih => exact Finset.sum_le_sum fun k _ => ih _

/-- A sum of a nonnegative function over the positive integers below `H` is at most the sum over
all natural numbers below `H`. -/
theorem sum_Ioo_le_sum_range {g : ℤ → ℝ} (hg : ∀ m : ℤ, 0 ≤ g m) (H : ℕ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), g k ≤ ∑ k ∈ Finset.range H, g (k : ℤ) := by
  classical
  have hset : Finset.Ioo (0 : ℤ) (H : ℤ)
      = ((Finset.range H).filter (fun j => 0 < j)).image (fun j : ℕ => (j : ℤ)) := by
    ext n
    simp only [Finset.mem_Ioo, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨n.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hset, Finset.sum_image (by intro x _ y _ h; simpa using h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hg _

/-- Every partial sum over positive shifts is at most the full sum. -/
theorem sum_Ioo_weylMulti_le (β : ℝ) (N H : ℕ) (r : ℕ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), weylMulti β N H r k ≤ weylMulti β N H (r + 1) 1 := by
  rw [weylMulti_succ]
  simpa using sum_Ioo_le_sum_range (g := fun m => weylMulti β N H r m)
    (fun m => weylMulti_nonneg _ _ _ _ _) H

/-- The `k = 0` term alone: `H^r N ≤ W_{r+1}`. -/
theorem weylMulti_ge_diagonal (β : ℝ) (N H : ℕ) (r : ℕ) (hH : 0 < H) :
    (H : ℝ) ^ r * N ≤ weylMulti β N H (r + 1) 1 := by
  classical
  rw [weylMulti_succ]
  have h0 : (0 : ℕ) ∈ Finset.range H := Finset.mem_range.mpr hH
  have := Finset.single_le_sum (f := fun k : ℕ => weylMulti β N H r ((1 : ℤ) * (k : ℤ)))
    (fun k _ => weylMulti_nonneg _ _ _ _ _) h0
  simpa [weylMulti_zero_arg] using this

/-! ## Polynomial phases -/

/-- `f` is a polynomial phase of degree at most `d` whose coefficient of `n^d` is `α`. -/
def IsPolyPhase (d : ℕ) (α : ℝ) (f : ℤ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, c d = α ∧ ∀ n : ℤ, f n = ∑ j ∈ Finset.range (d + 1), c j * (n : ℝ) ^ j

/-- The monomial phase `α n^d`. -/
theorem isPolyPhase_monomial (d : ℕ) (α : ℝ) :
    IsPolyPhase d α (fun n : ℤ => α * (n : ℝ) ^ d) := by
  classical
  refine ⟨fun j => if j = d then α else 0, by simp, fun n => ?_⟩
  rw [Finset.sum_eq_single d]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.self_mem_range_succ d) h

/-- **Differencing lowers the degree.**  The difference of a polynomial phase of degree `d + 1`
with leading coefficient `α` is a polynomial phase of degree `d` with leading coefficient
`(d + 1) k α`. -/
theorem IsPolyPhase.diff {d : ℕ} {α : ℝ} {f : ℤ → ℝ} (hf : IsPolyPhase (d + 1) α f) (k : ℤ) :
    IsPolyPhase d ((d + 1 : ℕ) * (k : ℝ) * α) (fun n => f (n + k) - f n) := by
  classical
  obtain ⟨c, hcd, hc⟩ := hf
  refine ⟨fun i => ∑ j ∈ Finset.Ioc i (d + 1), c j * (j.choose i : ℝ) * (k : ℝ) ^ (j - i),
    ?_, ?_⟩
  · have hIoc : Finset.Ioc d (d + 1) = {d + 1} := Nat.Ioc_succ_singleton d
    have hs : d + 1 - d = 1 := by omega
    simp only [hIoc, Finset.sum_singleton, hcd, Nat.choose_succ_self_right, hs, pow_one]
    ring
  · intro n
    simp only [hc]
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ j : ℕ, c j * (((n + k : ℤ)) : ℝ) ^ j - c j * (n : ℝ) ^ j
        = ∑ i ∈ Finset.range j, c j * ((n : ℝ) ^ i * (k : ℝ) ^ (j - i) * (j.choose i : ℝ)) := by
      intro j
      have hexp : (((n + k : ℤ)) : ℝ) ^ j
          = ∑ i ∈ Finset.range (j + 1), (n : ℝ) ^ i * (k : ℝ) ^ (j - i) * (j.choose i : ℝ) := by
        push_cast
        exact add_pow (n : ℝ) (k : ℝ) j
      rw [hexp, Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
      rw [mul_add, Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    have hswap : ∑ j ∈ Finset.range (d + 1 + 1), ∑ i ∈ Finset.range j,
          c j * ((n : ℝ) ^ i * (k : ℝ) ^ (j - i) * (j.choose i : ℝ))
        = ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.Ioc i (d + 1),
          c j * ((n : ℝ) ^ i * (k : ℝ) ^ (j - i) * (j.choose i : ℝ)) := by
      refine Finset.sum_comm' ?_
      intro j i
      simp only [Finset.mem_range, Finset.mem_Ioc]
      omega
    rw [hswap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ## The algebraic assembly of one inductive step -/

/-- The arithmetic of one step of the induction, isolated from the exponential sums.  With
`K = K' + 1` shifts' worth of Hölder, `hA` the A process, `hTle` the inductive hypothesis summed
over the shifts, `hHolder` the power-mean inequality and `hdiag` the diagonal term, the bound for
the doubled exponent follows. -/
theorem weyl_assembly {Hr P Nr S Sg T W : ℝ} {d K' : ℕ}
    (hHr : 1 ≤ Hr) (hP : 0 < P) (hN : 0 ≤ Nr) (hNP : Nr ≤ P) (hSg : 0 ≤ Sg) (hW : 0 ≤ W)
    (hA : Hr * S ^ 2 ≤ P * (Nr + 2 * Sg))
    (hTle : Hr ^ d * T ≤ 8 ^ (K' + 1) * P ^ K' * W)
    (hHolder : Sg ^ (K' + 1) ≤ Hr ^ K' * T)
    (hdiag : Hr ^ d * Nr ≤ W) :
    S ^ (2 * (K' + 1)) * (Hr ^ (d + 1) * P) ≤ 8 ^ (2 * (K' + 1)) * P ^ (2 * (K' + 1)) * W := by
  set K : ℕ := K' + 1 with hK
  have hHr0 : (0 : ℝ) < Hr := by linarith
  have hHK' : (1 : ℝ) ≤ Hr ^ K' := one_le_pow₀ hHr
  have hA' : (S ^ 2) ^ K * Hr ^ K ≤ P ^ K * (Nr + 2 * Sg) ^ K := by
    calc (S ^ 2) ^ K * Hr ^ K = (Hr * S ^ 2) ^ K := by rw [mul_pow]; ring
      _ ≤ (P * (Nr + 2 * Sg)) ^ K := pow_le_pow_left₀ (by positivity) hA K
      _ = P ^ K * (Nr + 2 * Sg) ^ K := mul_pow _ _ _
  have hB : (Nr + 2 * Sg) ^ K ≤ 2 ^ K' * (Nr ^ K + (2 * Sg) ^ K) := by
    have := add_pow_le hN (by linarith : (0 : ℝ) ≤ 2 * Sg) K
    simpa [hK] using this
  have hNK : Hr ^ d * Nr ^ K ≤ P ^ K' * W := by
    have hNP' : Nr ^ K' ≤ P ^ K' := pow_le_pow_left₀ hN hNP K'
    have h1 : (0 : ℝ) ≤ Hr ^ d * Nr := by positivity
    calc Hr ^ d * Nr ^ K = Nr ^ K' * (Hr ^ d * Nr) := by rw [hK, pow_succ]; ring
      _ ≤ P ^ K' * W := by
          have h2 : (0 : ℝ) ≤ Nr ^ K' := by positivity
          nlinarith [pow_nonneg hP.le K']
  have hSigK : Hr ^ d * (2 * Sg) ^ K ≤ 2 ^ K * (Hr ^ K' * (8 ^ K * P ^ K' * W)) := by
    have h1 : (2 * Sg) ^ K = 2 ^ K * Sg ^ K := by rw [mul_pow]
    have h2 : Hr ^ d * Sg ^ K ≤ Hr ^ K' * (Hr ^ d * T) := by
      have h3 : Sg ^ K ≤ Hr ^ K' * T := by rw [hK]; exact hHolder
      nlinarith [pow_nonneg hHr0.le d]
    have h4 : Hr ^ K' * (Hr ^ d * T) ≤ Hr ^ K' * (8 ^ K * P ^ K' * W) :=
      mul_le_mul_of_nonneg_left hTle (by positivity)
    calc Hr ^ d * (2 * Sg) ^ K = 2 ^ K * (Hr ^ d * Sg ^ K) := by rw [h1]; ring
      _ ≤ 2 ^ K * (Hr ^ K' * (8 ^ K * P ^ K' * W)) :=
          mul_le_mul_of_nonneg_left (h2.trans h4) (by positivity)
  have hconst : (2 : ℝ) ^ K' * (1 + 2 ^ K * 8 ^ K * Hr ^ K') ≤ Hr ^ K' * 8 ^ (2 * K) := by
    have h16 : (2 : ℝ) ^ K * 8 ^ K = 2 ^ (4 * K) := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
      ring_nf
    have h64 : (8 : ℝ) ^ (2 * K) = 2 ^ (6 * K) := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      ring_nf
    have hexp2 : (2 : ℝ) ^ K' * 2 ^ (4 * K + 1) ≤ 2 ^ (6 * K) := by
      rw [← pow_add]
      refine pow_le_pow_right₀ (by norm_num) ?_
      omega
    calc (2 : ℝ) ^ K' * (1 + 2 ^ K * 8 ^ K * Hr ^ K')
        = 2 ^ K' * (1 + 2 ^ (4 * K) * Hr ^ K') := by rw [h16]
      _ ≤ 2 ^ K' * (Hr ^ K' * 2 ^ (4 * K + 1)) := by
          have hinner : 1 + 2 ^ (4 * K) * Hr ^ K' ≤ Hr ^ K' * 2 ^ (4 * K + 1) := by
            have hone : (1 : ℝ) ≤ 2 ^ (4 * K) := one_le_pow₀ (by norm_num)
            have hX : (2 : ℝ) ^ (4 * K) ≤ 2 ^ (4 * K) * Hr ^ K' :=
              le_mul_of_one_le_right (by positivity) hHK'
            rw [pow_succ]
            linarith
          exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = Hr ^ K' * (2 ^ K' * 2 ^ (4 * K + 1)) := by ring
      _ ≤ Hr ^ K' * 2 ^ (6 * K) := mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = Hr ^ K' * 8 ^ (2 * K) := by rw [h64]
  have hkey : Hr ^ K' * (S ^ (2 * K) * (Hr ^ (d + 1) * P))
      ≤ Hr ^ K' * (8 ^ (2 * K) * P ^ (2 * K) * W) := by
    have hlhs : Hr ^ K' * (S ^ (2 * K) * (Hr ^ (d + 1) * P))
        = (S ^ 2) ^ K * Hr ^ K * (Hr ^ d * P) := by
      rw [pow_mul, hK]; ring
    rw [hlhs]
    have hstep1 : (S ^ 2) ^ K * Hr ^ K * (Hr ^ d * P)
        ≤ P ^ K * (Nr + 2 * Sg) ^ K * (Hr ^ d * P) :=
      mul_le_mul_of_nonneg_right hA' (by positivity)
    have hstep2 : P ^ K * (Nr + 2 * Sg) ^ K * (Hr ^ d * P)
        ≤ P ^ K * (2 ^ K' * (Nr ^ K + (2 * Sg) ^ K)) * (Hr ^ d * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity)
    have hstep3 : P ^ K * (2 ^ K' * (Nr ^ K + (2 * Sg) ^ K)) * (Hr ^ d * P)
        = 2 ^ K' * P ^ (K + 1) * (Hr ^ d * Nr ^ K + Hr ^ d * (2 * Sg) ^ K) := by
      rw [pow_succ]; ring
    have hstep5 : 2 ^ K' * P ^ (K + 1) * (Hr ^ d * Nr ^ K + Hr ^ d * (2 * Sg) ^ K)
        ≤ 2 ^ K' * P ^ (K + 1) * (P ^ K' * W + 2 ^ K * (Hr ^ K' * (8 ^ K * P ^ K' * W))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hstep6 : 2 ^ K' * P ^ (K + 1) * (P ^ K' * W + 2 ^ K * (Hr ^ K' * (8 ^ K * P ^ K' * W)))
        = 2 ^ K' * (1 + 2 ^ K * 8 ^ K * Hr ^ K') * P ^ (K + 1 + K') * W := by
      rw [pow_add]; ring
    have hKK : K + 1 + K' = 2 * K := by omega
    have hstep7 : 2 ^ K' * (1 + 2 ^ K * 8 ^ K * Hr ^ K') * P ^ (K + 1 + K') * W
        ≤ Hr ^ K' * (8 ^ (2 * K) * P ^ (2 * K) * W) := by
      rw [hKK]
      have hPW : (0 : ℝ) ≤ P ^ (2 * K) * W := by positivity
      nlinarith [hconst, hPW]
    linarith [hstep1, hstep2, hstep5, hstep7, le_of_eq hstep3, le_of_eq hstep6]
  exact le_of_mul_le_mul_left hkey (by positivity)

/-! ## Weyl's inequality in degree `d` -/

/-- **Weyl's inequality in degree `d + 1`.**  For a polynomial phase of degree at most `d + 1`
with coefficient `α` at `n^(d+1)`, and `H ≥ 1` shifts,
`‖S‖^(2^d) · H^d (N + H) ≤ 8^(2^d) (N + H)^(2^d) W_d((d+1)! α, N, H, 1)`. -/
theorem norm_polyPhaseSum_pow_le (d : ℕ) {α : ℝ} {f : ℤ → ℝ} (hf : IsPolyPhase (d + 1) α f)
    (N H : ℕ) (hH : 0 < H) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ (2 ^ d) * ((H : ℝ) ^ d * ((N : ℝ) + H))
      ≤ 8 ^ (2 ^ d) * ((N : ℝ) + H) ^ (2 ^ d)
        * weylMulti ((d + 1).factorial * α) N H d 1 := by
  induction d generalizing α f N with
  | zero =>
      obtain ⟨c, hcd, hc⟩ := hf
      have hphase : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          e2pi (f n) = e2pi (α * ((1 : ℤ) : ℝ) * (n : ℝ) + c 0) := by
        intro n _
        congr 1
        rw [hc n, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hcd]
        push_cast
        ring
      have hS : ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ≤ dioMaj α N 1 := by
        rw [Finset.sum_congr rfl hphase]
        exact norm_linSum_le_dioMaj (le_refl (N : ℤ))
      have hPnonneg : (0 : ℝ) ≤ (N : ℝ) + H := by positivity
      have hMnonneg : (0 : ℝ) ≤ dioMaj α N 1 := dioMaj_nonneg _ _ _
      have hval : weylMulti ((Nat.factorial 1 : ℕ) * α) N H 0 1 = dioMaj α N 1 := by
        simp [weylMulti_zero, Nat.factorial]
      simp only [pow_zero, pow_one, hval, one_mul]
      nlinarith [norm_nonneg (∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n))]
  | succ d ih =>
      classical
      obtain ⟨K', hKeq⟩ : ∃ K', 2 ^ d = K' + 1 :=
        ⟨2 ^ d - 1, by have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega⟩
      set γ : ℝ := ((d + 1 + 1).factorial : ℝ) * α with hγdef
      set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ with hSdef
      set Sk : ℤ → ℝ :=
        fun k => ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (f (n + k) - f n)‖ with hSkdef
      set W : ℝ := weylMulti γ N H (d + 1) 1 with hWdef
      have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
      have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hPpos : (0 : ℝ) < (N : ℝ) + H := by linarith
      have hSknonneg : ∀ k, 0 ≤ Sk k := fun k => norm_nonneg _
      have hSignonneg : (0 : ℝ) ≤ ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k :=
        Finset.sum_nonneg fun k _ => hSknonneg k
      have hWnonneg : 0 ≤ W := weylMulti_nonneg _ _ _ _ _
      -- the A process
      have hA : (H : ℝ) * S ^ 2
          ≤ ((N : ℝ) + H) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k) := by
        refine (norm_sq_sum_e2pi_le f N H hH).trans ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      -- the inductive hypothesis, applied to each differenced phase
      have hstep : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          Sk k ^ (K' + 1) * (H : ℝ) ^ d
            ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K' * weylMulti γ N H d k := by
        intro k hk
        rw [Finset.mem_Ioo] at hk
        have hWk : 0 ≤ weylMulti γ N H d k := weylMulti_nonneg _ _ _ _ _
        by_cases hkN : k ≤ (N : ℤ)
        · set M : ℕ := ((N : ℤ) - k).toNat with hMdef
          have hMZ : ((M : ℕ) : ℤ) = (N : ℤ) - k := Int.toNat_of_nonneg (by omega)
          have hMN : M ≤ N := by omega
          have hMP : (M : ℝ) + H ≤ (N : ℝ) + H := by
            have : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
            linarith
          have hMHpos : (0 : ℝ) < (M : ℝ) + H := by positivity
          have hIH := ih (hf.diff k) M
          rw [hKeq] at hIH
          have hsum : ‖∑ n ∈ Finset.Ico (0 : ℤ) ((M : ℕ) : ℤ),
                e2pi ((fun n => f (n + k) - f n) n)‖ = Sk k := by
            rw [hMZ]
          rw [hsum] at hIH
          have hfac : ((d + 1 + 1).factorial : ℝ)
              = ((d + 1 + 1 : ℕ) : ℝ) * ((d + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          have hcoeff : ((d + 1).factorial : ℝ) * ((d + 1 + 1 : ℕ) * (k : ℝ) * α)
              = γ * (k : ℝ) := by
            rw [hγdef, hfac]
            ring
          rw [hcoeff, weylMulti_mul, mul_one] at hIH
          have hmono : weylMulti γ M H d k ≤ weylMulti γ N H d k :=
            weylMulti_mono_length hMN H d k
          have hcancel : Sk k ^ (K' + 1) * (H : ℝ) ^ d * ((M : ℝ) + H)
              ≤ 8 ^ (K' + 1) * ((M : ℝ) + H) ^ K' * weylMulti γ N H d k * ((M : ℝ) + H) := by
            calc Sk k ^ (K' + 1) * (H : ℝ) ^ d * ((M : ℝ) + H)
                = Sk k ^ (K' + 1) * ((H : ℝ) ^ d * ((M : ℝ) + H)) := by ring
              _ ≤ 8 ^ (K' + 1) * ((M : ℝ) + H) ^ (K' + 1) * weylMulti γ M H d k := hIH
              _ ≤ 8 ^ (K' + 1) * ((M : ℝ) + H) ^ (K' + 1) * weylMulti γ N H d k :=
                  mul_le_mul_of_nonneg_left hmono (by positivity)
              _ = 8 ^ (K' + 1) * ((M : ℝ) + H) ^ K' * weylMulti γ N H d k * ((M : ℝ) + H) := by
                  rw [pow_succ]; ring
          have hle : Sk k ^ (K' + 1) * (H : ℝ) ^ d
              ≤ 8 ^ (K' + 1) * ((M : ℝ) + H) ^ K' * weylMulti γ N H d k :=
            le_of_mul_le_mul_right hcancel hMHpos
          refine hle.trans ?_
          have hpow : ((M : ℝ) + H) ^ K' ≤ ((N : ℝ) + H) ^ K' :=
            pow_le_pow_left₀ (by positivity) hMP K'
          have h8 : (0 : ℝ) ≤ (8 : ℝ) ^ (K' + 1) := by positivity
          exact mul_le_mul_of_nonneg_right (by nlinarith [hpow, h8]) hWk
        · have hempty : Finset.Ico (0 : ℤ) ((N : ℤ) - k) = ∅ := by
            rw [Finset.Ico_eq_empty]
            omega
          have hz : Sk k = 0 := by rw [hSkdef]; simp [hempty]
          rw [hz]
          have : (0 : ℝ) ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K' * weylMulti γ N H d k := by
            positivity
          simpa using this
      -- summing the shifts
      have hT : (H : ℝ) ^ d * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k ^ (K' + 1)
          ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K' * W := by
        have hsum := Finset.sum_le_sum hstep
        rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
        have hfold : ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), weylMulti γ N H d k ≤ W :=
          sum_Ioo_weylMulti_le γ N H d
        have h8P : (0 : ℝ) ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K' := by positivity
        calc (H : ℝ) ^ d * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k ^ (K' + 1)
            = (∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k ^ (K' + 1)) * (H : ℝ) ^ d := by ring
          _ ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K'
              * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), weylMulti γ N H d k := hsum
          _ ≤ 8 ^ (K' + 1) * ((N : ℝ) + H) ^ K' * W := mul_le_mul_of_nonneg_left hfold h8P
      -- Hölder over the shifts
      have hHolder : (∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k) ^ (K' + 1)
          ≤ (H : ℝ) ^ K' * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k ^ (K' + 1) := by
        have hcs := pow_sum_le_card_mul_sum_pow
          (s := Finset.Ioo (0 : ℤ) (H : ℤ)) (f := Sk) (fun k _ => hSknonneg k) K'
        refine hcs.trans ?_
        have hcard : (((Finset.Ioo (0 : ℤ) (H : ℤ)).card : ℕ) : ℝ) ≤ (H : ℝ) := by
          rw [Int.card_Ioo]
          have : ((H : ℤ) - 0 - 1).toNat ≤ H := by omega
          exact_mod_cast this
        have hTnonneg : (0 : ℝ) ≤ ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), Sk k ^ (K' + 1) :=
          Finset.sum_nonneg fun k _ => pow_nonneg (hSknonneg k) _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard K') hTnonneg
      -- the diagonal term
      have hdiag : (H : ℝ) ^ d * N ≤ W := weylMulti_ge_diagonal γ N H d hH
      have hexp : 2 ^ (d + 1) = 2 * (K' + 1) := by
        rw [pow_succ, hKeq]; ring
      rw [hexp]
      exact weyl_assembly hH1 hPpos hNnonneg (by linarith) hSignonneg hWnonneg hA hT hHolder hdiag

/-! ## Estimating the majorant sum -/

/-- The one-dimensional majorant sum `∑_{0 < t ≤ M} min(N, 1/(2‖β t‖))`. -/
def dioSum (β : ℝ) (N : ℕ) (M : ℤ) : ℝ := ∑ t ∈ Finset.Ioc (0 : ℤ) M, dioMaj β N t

theorem dioSum_nonneg (β : ℝ) (N : ℕ) (M : ℤ) : 0 ≤ dioSum β N M :=
  Finset.sum_nonneg fun _ _ => dioMaj_nonneg _ _ _

theorem dioSum_mono (β : ℝ) (N : ℕ) {M₁ M₂ : ℤ} (h : M₁ ≤ M₂) :
    dioSum β N M₁ ≤ dioSum β N M₂ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => dioMaj_nonneg _ _ _
  intro t ht
  rw [Finset.mem_Ioc] at ht ⊢
  exact ⟨ht.1, ht.2.trans h⟩

/-- **The fibre bound in one variable.**  For a fixed `m > 0` the map `i ↦ m (i + 1)` is injective
and lands in `(0, m (H' + 1)]`. -/
theorem sum_range_dioMaj_mul_le (β : ℝ) (N H' : ℕ) {m : ℤ} (hm : 0 < m) :
    ∑ i ∈ Finset.range H', dioMaj β N (m * ((i : ℤ) + 1))
      ≤ dioSum β N (m * ((H' : ℤ) + 1)) := by
  classical
  have himg : ∑ i ∈ Finset.range H', dioMaj β N (m * ((i : ℤ) + 1))
      = ∑ t ∈ (Finset.range H').image (fun i : ℕ => m * ((i : ℤ) + 1)), dioMaj β N t := by
    refine (Finset.sum_image ?_).symm
    intro x _ y _ hxy
    have : (x : ℤ) + 1 = (y : ℤ) + 1 := mul_left_cancel₀ (by omega) hxy
    omega
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => dioMaj_nonneg _ _ _
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  rw [Finset.mem_range] at hi
  rw [Finset.mem_Ioc]
  refine ⟨by positivity, ?_⟩
  have h1 : (i : ℤ) + 1 ≤ (H' : ℤ) + 1 := by omega
  exact mul_le_mul_of_nonneg_left h1 hm.le

/-- **The majorant sum, folded onto one variable.**  The tuples of shifts with a zero entry
contribute `N` each, and among the remaining ones the last entry is determined by the others and
by the product, so the `r + 1`-fold sum is at most `H^r` one-dimensional sums. -/
theorem weylMulti_le_dioSum (β : ℝ) (N H : ℕ) (r : ℕ) {m : ℤ} (hm : 0 < m) :
    weylMulti β N H (r + 1) m
      ≤ ((r : ℝ) + 1) * (H : ℝ) ^ r * N + (H : ℝ) ^ r * dioSum β N (m * (H : ℤ) ^ (r + 1)) := by
  induction r generalizing m with
  | zero =>
      rw [weylMulti_succ]
      rcases Nat.eq_zero_or_pos H with rfl | hH
      · simp
        linarith [dioSum_nonneg β N 0, Nat.cast_nonneg (α := ℝ) N]
      · obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
        rw [Finset.sum_range_succ']
        have hterms : ∀ i ∈ Finset.range H',
            weylMulti β N (H' + 1) 0 (m * ((i : ℕ) + 1 : ℕ)) = dioMaj β N (m * ((i : ℤ) + 1)) := by
          intro i _
          rw [weylMulti_zero]
          congr 2
        rw [Finset.sum_congr rfl hterms]
        have hfib := sum_range_dioMaj_mul_le β N H' hm
        have hzero : weylMulti β N (H' + 1) 0 (m * ((0 : ℕ) : ℤ)) = (N : ℝ) := by
          simp [weylMulti_zero, dioMaj, intDist]
        rw [hzero]
        have hcast : ((H' : ℤ) + 1) = ((H' + 1 : ℕ) : ℤ) ^ (0 + 1) := by push_cast; ring
        rw [hcast] at hfib
        simp only [pow_zero, Nat.cast_zero, zero_add, one_mul]
        linarith
  | succ r ih =>
      rw [weylMulti_succ]
      rcases Nat.eq_zero_or_pos H with rfl | hH
      · simp [weylMulti]
      · obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
        set Hn : ℕ := H' + 1 with hHn
        have hHR : (1 : ℝ) ≤ (Hn : ℝ) := by
          rw [hHn]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) H']
        rw [Finset.sum_range_succ']
        have hzero : weylMulti β N Hn (r + 1) (m * ((0 : ℕ) : ℤ)) = (Hn : ℝ) ^ (r + 1) * N := by
          simpa using weylMulti_zero_arg β N Hn (r + 1)
        rw [hzero]
        have hterm : ∀ i ∈ Finset.range H',
            weylMulti β N Hn (r + 1) (m * ((i : ℕ) + 1 : ℕ))
              ≤ ((r : ℝ) + 1) * (Hn : ℝ) ^ r * N
                + (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2)) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hcast : ((i : ℕ) + 1 : ℕ) = ((i : ℤ) + 1 : ℤ) := by push_cast; ring
          have hmi : 0 < m * ((i : ℤ) + 1) := by positivity
          have hIH := ih (m := m * ((i : ℤ) + 1)) hmi
          have heq : (m * (((i : ℕ) + 1 : ℕ) : ℤ)) = m * ((i : ℤ) + 1) := by push_cast; ring
          rw [heq]
          refine hIH.trans ?_
          have hmono : dioSum β N (m * ((i : ℤ) + 1) * (Hn : ℤ) ^ (r + 1))
              ≤ dioSum β N (m * (Hn : ℤ) ^ (r + 2)) := by
            refine dioSum_mono β N ?_
            have hile : (i : ℤ) + 1 ≤ (Hn : ℤ) := by
              rw [hHn]; push_cast; omega
            have hpow : (0 : ℤ) < (Hn : ℤ) ^ (r + 1) := by positivity
            calc m * ((i : ℤ) + 1) * (Hn : ℤ) ^ (r + 1)
                ≤ m * (Hn : ℤ) * (Hn : ℤ) ^ (r + 1) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hile hm.le) hpow.le
              _ = m * (Hn : ℤ) ^ (r + 2) := by ring
          have hHr : (0 : ℝ) ≤ (Hn : ℝ) ^ r := by positivity
          nlinarith [hmono, hHr]
        have hbase : (0 : ℝ) ≤ ((r : ℝ) + 1) * (Hn : ℝ) ^ r * N
            + (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2)) := by
          have h0 := dioSum_nonneg β N (m * (Hn : ℤ) ^ (r + 2))
          have h1 : (0 : ℝ) ≤ (Hn : ℝ) ^ r := by positivity
          have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have h4 : (0 : ℝ) ≤ ((r : ℝ) + 1) * (Hn : ℝ) ^ r * N := by positivity
          have h5 : (0 : ℝ) ≤ (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2)) :=
            mul_nonneg h1 h0
          linarith
        have hsum : ∑ i ∈ Finset.range H',
              weylMulti β N Hn (r + 1) (m * ((i : ℕ) + 1 : ℕ))
            ≤ (H' : ℝ) * (((r : ℝ) + 1) * (Hn : ℝ) ^ r * N
                + (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2))) := by
          have hs := Finset.sum_le_sum hterm
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
          exact hs
        have hH'le : (H' : ℝ) ≤ (Hn : ℝ) := by rw [hHn]; push_cast; linarith
        have hsum' : ∑ i ∈ Finset.range H',
              weylMulti β N Hn (r + 1) (m * ((i : ℕ) + 1 : ℕ))
            ≤ (Hn : ℝ) * (((r : ℝ) + 1) * (Hn : ℝ) ^ r * N
                + (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2))) :=
          hsum.trans (mul_le_mul_of_nonneg_right hH'le hbase)
        have hgoal : (Hn : ℝ) ^ (r + 1) * N
              + (Hn : ℝ) * (((r : ℝ) + 1) * (Hn : ℝ) ^ r * N
                + (Hn : ℝ) ^ r * dioSum β N (m * (Hn : ℤ) ^ (r + 2)))
            = ((r : ℝ) + 1 + 1) * (Hn : ℝ) ^ (r + 1) * N
              + (Hn : ℝ) ^ (r + 1) * dioSum β N (m * (Hn : ℤ) ^ (r + 1 + 1)) := by
          rw [show r + 1 + 1 = r + 2 from rfl, pow_succ]
          ring
        push_cast
        push_cast at hgoal hsum'
        linarith [hsum', le_of_eq hgoal]

/-- **The one-dimensional majorant sum, estimated by the counting lemma.**  If `β` has a rational
approximation `|β − a/q| ≤ 1/q²` with `q` coprime to `a`, then `∑_{0 < t ≤ M} min(N, 1/(2‖β t‖))`
is at most `(M/q + 1)(4N + q(1 + log q))`. -/
theorem dioSum_le_of_approx {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N M : ℕ) :
    dioSum β N (M : ℤ) ≤ ((M : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) :=
  WeylQuadratic.sum_Ioc_le hq hcop happ (Nat.cast_nonneg N) (dioMaj_nonneg β N) (dioMaj_le β N)
    (dioMaj_mul_intDist_le β N) M

/-- **The `r`-fold majorant sum, estimated by the counting lemma.**  Folding the `r + 1` shifts onto
their product and applying `dioSum_le_of_approx` to the resulting one-dimensional sum. -/
theorem weylMulti_le_of_approx {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |β - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H r : ℕ) :
    weylMulti β N H (r + 1) 1
      ≤ ((r : ℝ) + 1) * (H : ℝ) ^ r * N
        + (H : ℝ) ^ r * (((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))) := by
  have hfold := weylMulti_le_dioSum β N H r (m := 1) one_pos
  have hcast : ((1 : ℤ) * (H : ℤ) ^ (r + 1)) = ((H ^ (r + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hcast] at hfold
  have hcount := dioSum_le_of_approx hq hcop happ N (H ^ (r + 1))
  have hHr : (0 : ℝ) ≤ (H : ℝ) ^ r := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hHr
  have hpow : ((H ^ (r + 1) : ℕ) : ℝ) = (H : ℝ) ^ (r + 1) := by push_cast; ring
  rw [hpow] at hmul
  linarith

/-- **Weyl's inequality for a monomial phase, with the majorant sum evaluated.**  For the phase
`α n^(r+2)`, an approximation `|(r+2)! α − a/q| ≤ 1/q²` with `q` coprime to `a` gives an explicit
bound on the `2^(r+1)`-th power of the exponential sum. -/
theorem norm_monomialSum_pow_le_of_approx {α : ℝ} {a : ℤ} {q : ℕ} (r : ℕ) (hq : 0 < q)
    (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N H : ℕ) (hH : 0 < H) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1))
        * ((H : ℝ) ^ (r + 1) * ((N : ℝ) + H))
      ≤ 8 ^ (2 ^ (r + 1)) * ((N : ℝ) + H) ^ (2 ^ (r + 1))
        * (((r : ℝ) + 1) * (H : ℝ) ^ r * N
          + (H : ℝ) ^ r * (((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q)))) := by
  have hmain := norm_polyPhaseSum_pow_le (r + 1) (isPolyPhase_monomial (r + 2) α) N H hH
  have hcount := weylMulti_le_of_approx (β := ((r + 2).factorial : ℝ) * α) hq hcop happ N H r
  have hfac : (r + 1 + 1).factorial = (r + 2).factorial := rfl
  rw [hfac] at hmain
  have hpos : (0 : ℝ) ≤ 8 ^ (2 ^ (r + 1)) * ((N : ℝ) + H) ^ (2 ^ (r + 1)) := by positivity
  exact hmain.trans (mul_le_mul_of_nonneg_left hcount hpos)

/-- **The power saving, in a clean form.**  Suppose `|(r+2)! α − a/q| ≤ 1/q²` with `q` coprime
to `a`, and that the number of shifts satisfies `H^(r+1) ≤ q ≤ N`.  Then

  `‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · H ≤ 16^(2^(r+1)) N^(2^(r+1)) (r + 11 + 2 log N)`.

Choosing `H` of size about `N^(1/(r+1))` — which is what the hypothesis `H^(r+1) ≤ q` allows when
the denominator `q` is of size about `N` — this is a saving of `N^(-1/((r+1) 2^(r+1)))` over the
trivial bound `N`, up to the logarithm. -/
theorem norm_monomialSum_pow_mul_le_of_approx {α : ℝ} {a : ℤ} {q : ℕ} (r : ℕ) (hq : 0 < q)
    (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N H : ℕ} (hH : 0 < H) (hHq : (H : ℝ) ^ (r + 1) ≤ q) (hqN : q ≤ N) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * H
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * ((r : ℝ) + 11 + 2 * Real.log N) := by
  set K : ℕ := 2 ^ (r + 1) with hKdef
  have hK1 : 1 ≤ K := Nat.one_le_two_pow
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ with hS
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hN1 : (1 : ℝ) ≤ N := le_trans hq1 hqNR
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogN : Real.log q ≤ Real.log N := Real.log_le_log hqR hqNR
  have hlogN0 : 0 ≤ Real.log N := le_trans hlogq hlogN
  set C : ℝ := (r : ℝ) + 11 + 2 * Real.log N with hC
  have hCpos : 0 ≤ C := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    rw [hC]; linarith
  have hmain := norm_monomialSum_pow_le_of_approx r hq hcop happ N H hH
  -- bound the majorant bracket by `H^r N C`
  have hfrac : (H : ℝ) ^ (r + 1) / q + 1 ≤ 2 := by
    have : (H : ℝ) ^ (r + 1) / q ≤ 1 := (div_le_one hqR).mpr hHq
    linarith
  have hinner : 4 * (N : ℝ) + q * (1 + Real.log q) ≤ (N : ℝ) * (5 + Real.log N) := by
    have h1 : (q : ℝ) * (1 + Real.log q) ≤ (N : ℝ) * (1 + Real.log N) :=
      mul_le_mul hqNR (by linarith) (by linarith) (le_of_lt hNpos)
    have hid : (N : ℝ) * (5 + Real.log N) = 4 * N + N * (1 + Real.log N) := by ring
    linarith
  have hinner0 : (0 : ℝ) ≤ 4 * (N : ℝ) + q * (1 + Real.log q) := by positivity
  have hHr : (0 : ℝ) < (H : ℝ) ^ r := by positivity
  have hbracket : ((r : ℝ) + 1) * (H : ℝ) ^ r * N
        + (H : ℝ) ^ r * (((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q)))
      ≤ (H : ℝ) ^ r * ((N : ℝ) * C) := by
    have hprod : ((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))
        ≤ 2 * ((N : ℝ) * (5 + Real.log N)) := by
      calc ((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))
          ≤ 2 * (4 * N + q * (1 + Real.log q)) :=
            mul_le_mul_of_nonneg_right hfrac hinner0
        _ ≤ 2 * ((N : ℝ) * (5 + Real.log N)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hprod hHr.le
    have hid : (H : ℝ) ^ r * ((N : ℝ) * ((r : ℝ) + 11 + 2 * Real.log N))
        = ((r : ℝ) + 1) * (H : ℝ) ^ r * N
          + (H : ℝ) ^ r * (2 * ((N : ℝ) * (5 + Real.log N))) := by ring
    rw [hC]
    linarith
  have hprefac : (0 : ℝ) ≤ 8 ^ K * ((N : ℝ) + H) ^ K := by positivity
  have hstep : S ^ K * ((H : ℝ) ^ (r + 1) * ((N : ℝ) + H))
      ≤ 8 ^ K * ((N : ℝ) + H) ^ K * ((H : ℝ) ^ r * ((N : ℝ) * C)) :=
    hmain.trans (mul_le_mul_of_nonneg_left hbracket hprefac)
  -- cancel the common factor `H^r (N + H)`
  have hsum : (0 : ℝ) < (N : ℝ) + H := by linarith
  have hKsucc : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos (lt_of_lt_of_le one_pos hK1)
  have hsplit : ((N : ℝ) + H) ^ K = ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) + H) := by
    rw [← pow_succ, hKsucc]
  have hcancel : (S ^ K * H) * ((H : ℝ) ^ r * ((N : ℝ) + H))
      ≤ (8 ^ K * ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) * C)) * ((H : ℝ) ^ r * ((N : ℝ) + H)) := by
    calc (S ^ K * H) * ((H : ℝ) ^ r * ((N : ℝ) + H))
        = S ^ K * ((H : ℝ) ^ (r + 1) * ((N : ℝ) + H)) := by rw [pow_succ]; ring
      _ ≤ 8 ^ K * ((N : ℝ) + H) ^ K * ((H : ℝ) ^ r * ((N : ℝ) * C)) := hstep
      _ = (8 ^ K * ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) * C)) * ((H : ℝ) ^ r * ((N : ℝ) + H)) := by
          rw [hsplit]; ring
  have hfac : (0 : ℝ) < (H : ℝ) ^ r * ((N : ℝ) + H) := by positivity
  have hred : S ^ K * H ≤ 8 ^ K * ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) * C) :=
    le_of_mul_le_mul_right hcancel hfac
  -- and `(N + H)^(K-1) ≤ 2^(K-1) N^(K-1)`
  have hHN : (H : ℝ) ≤ N := by
    have h1 : (H : ℝ) ≤ (H : ℝ) ^ (r + 1) := le_self_pow₀ (by exact_mod_cast hH) (by omega)
    linarith
  have hgeom : ((N : ℝ) + H) ^ (K - 1) ≤ 2 ^ (K - 1) * (N : ℝ) ^ (K - 1) := by
    have h1 : (N : ℝ) + H ≤ 2 * N := by linarith
    calc ((N : ℝ) + H) ^ (K - 1) ≤ (2 * (N : ℝ)) ^ (K - 1) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = 2 ^ (K - 1) * (N : ℝ) ^ (K - 1) := by rw [mul_pow]
  have hfinal : 8 ^ K * ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) * C)
      ≤ 16 ^ K * (N : ℝ) ^ K * C := by
    have h8 : (0 : ℝ) ≤ 8 ^ K := by positivity
    have hNC : (0 : ℝ) ≤ (N : ℝ) * C := by positivity
    have hNK : (0 : ℝ) ≤ (N : ℝ) ^ (K - 1) := by positivity
    have h2 : (2 : ℝ) ^ (K - 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    have hgeom2 : ((N : ℝ) + H) ^ (K - 1) ≤ 2 ^ K * (N : ℝ) ^ (K - 1) :=
      hgeom.trans (mul_le_mul_of_nonneg_right h2 hNK)
    have h1 : 8 ^ K * ((N : ℝ) + H) ^ (K - 1) * ((N : ℝ) * C)
        ≤ 8 ^ K * (2 ^ K * (N : ℝ) ^ (K - 1)) * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom2 h8) hNC
    have hN : (N : ℝ) ^ (K - 1) * (N : ℝ) = (N : ℝ) ^ K := by rw [← pow_succ, hKsucc]
    have h4 : 8 ^ K * (2 ^ K * (N : ℝ) ^ (K - 1)) * ((N : ℝ) * C) = 16 ^ K * (N : ℝ) ^ K * C := by
      calc 8 ^ K * (2 ^ K * (N : ℝ) ^ (K - 1)) * ((N : ℝ) * C)
          = (8 : ℝ) ^ K * 2 ^ K * ((N : ℝ) ^ (K - 1) * (N : ℝ)) * C := by ring
        _ = (8 * 2 : ℝ) ^ K * (N : ℝ) ^ K * C := by rw [hN, ← mul_pow]
        _ = 16 ^ K * (N : ℝ) ^ K * C := by norm_num
    exact h1.trans (le_of_eq h4)
  exact hred.trans hfinal

end WeylGeneral

end RiemannHypothesis
