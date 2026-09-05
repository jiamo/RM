/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylDivisor

/-!
# Weyl's inequality in its classical three-term form

`RiemannHypothesis.WeylDivisor` proves Weyl's inequality for the monomial phase `α n^d` with the
classical exponent, but only for denominators in the range `N ≤ q ≤ N^(d-1)`: the estimate is
stated as a single power saving, and the range restriction is what lets the three terms of the
classical statement be collapsed into one.  The open boundary of `M1-WEYL-DIVISOR` named exactly
this gap.

This file removes the restriction.  The same ingredients — Weyl differencing with `H = N` shifts
(`RiemannHypothesis.WeylGeneral.norm_polyPhaseSum_pow_le`), the fold of the shift tuples onto their
product with the divisor weight (`RiemannHypothesis.WeylDivisor.weylMulti_le_of_approx_divisor`),
and the counting lemma of `RiemannHypothesis.WeylMinSum` — are combined without discarding any of
the four terms produced by the counting lemma, which yields the classical shape

`‖∑_{0 ≤ n < N} e(α n^d)‖^(2^(d-1)) ≤ C N^(2^(d-1)) N^ε (1/q + 1/N + q/N^d)`

for *every* coprime approximation `|d! α − a/q| ≤ 1/q²` with `q ≤ N^d`.

## Main results

* `norm_polyPhaseSum_pow_le_three_term` — the inequality with explicit constants and an explicit
  divisor loss, valid for every `q > 0` and every polynomial phase of degree at most `d`;
* `exists_norm_polyPhaseSum_pow_le_three_term` — the divisor loss and the logarithm absorbed into
  `N^ε`, for `q ≤ N^d`;
* `exists_norm_polyPhaseSum_le_three_term` — the same after taking `2^(d-1)`-th roots, in the form
  `‖∑_{n<N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d-1))`, which is the statement found in
  the literature;
* `norm_monomialSum_pow_le_three_term`, `exists_norm_monomialSum_pow_le_three_term` and
  `exists_norm_monomialSum_le_three_term` — the three specialized to the monomial phase `α n^d`.

## Scope

The saving is genuine only when `q` is neither small nor almost as large as `N^d`: for `q` of size
`N^(d/2)` the bracket is of size `N^(-d/2)`, which is the classical minor-arc gain.  The `ε` is not
removed — the constant depends on it through the divisor bound and through `log N ≤ N^δ/δ` — and no
`(log N)^A` refinement is proved.  Vinogradov's mean value theorem, which is what degrees beyond
the reach of Weyl's method need, is not formalized.  As it must be, the bound is conditional on a
rational approximation to `d! α`; for `α` close to a rational with a small denominator there is no
cancellation.  Nothing about `ζ` follows: polynomial phases are not zeta phases, and no
subconvexity bound, approximate functional equation or density estimate is claimed.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace WeylClassical

open KusminLandau WeylQuadratic WeylCubic WeylGeneral WeylDivisor DivisorBound

/-- The three-term bracket of the classical Weyl inequality, `1/q + 1/N + q/N^d`. -/
def weylBracket (q N d : ℕ) : ℝ := 1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ d

theorem weylBracket_pos {q N d : ℕ} (hq : 0 < q) (hN : 0 < N) : 0 < weylBracket q N d := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  unfold weylBracket
  positivity

/-- **Weyl's inequality in its classical three-term form**, with explicit constants, for an
arbitrary polynomial phase `f` of degree at most `r + 2` with `n^(r+2)`-coefficient `α`.  For every
coprime approximation `|(r+2)! α − a/q| ≤ 1/q²`,

`‖∑_{0 ≤ n < N} e(f n)‖^(2^(r+1))`
`  ≤ 16^(2^(r+1)) N^(2^(r+1)) · D · (r + 21 + 4 log q) · (1/q + 1/N + q/N^(r+2))`,

where `D = (C (N^(r+1))^ε)^r` is the divisor loss coming from the divisor bound
`τ(n) ≤ C n^ε`.  No restriction is placed on `q`. -/
theorem norm_polyPhaseSum_pow_le_three_term {α : ℝ} {f : ℤ → ℝ} {a : ℤ} {q : ℕ} (r : ℕ)
    (hf : WeylGeneral.IsPolyPhase (r + 2) α f)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N)
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ (2 ^ (r + 1))
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
        * weylBracket q N (r + 2) := by
  set K : ℕ := 2 ^ (r + 1) with hKdef
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ with hS
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set P : ℝ := (N : ℝ) ^ (r + 1) with hP
  have hPpos : (0 : ℝ) < P := by rw [hP]; positivity
  have hPN : (N : ℝ) ≤ P := by
    rw [hP]
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ (r + 1) := pow_le_pow_right₀ hN1 (by omega)
  have hsucc : (N : ℝ) ^ (r + 2) = P * N := by rw [hP, pow_succ]
  set D : ℝ := (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r with hD
  have hDone : 1 ≤ D := by
    have hb : (1 : ℝ) ≤ ((N : ℝ) ^ (r + 1)) ^ ε :=
      Real.one_le_rpow (one_le_pow₀ hN1) hε.le
    have : (1 : ℝ) ≤ C * ((N : ℝ) ^ (r + 1)) ^ ε := by nlinarith
    exact one_le_pow₀ this
  set T : ℝ := weylBracket q N (r + 2) with hT
  -- the bracket, cleared of denominators
  have hTid : T * (N : ℝ) ^ (r + 2) = (N : ℝ) ^ (r + 2) / q + P + q := by
    rw [hT, hP, weylBracket]
    field_simp
    ring
  have hTpos : 0 < T := weylBracket_pos hq hN
  -- Weyl differencing with `H = N` shifts, and the folded majorant sum
  have hmain := WeylGeneral.norm_polyPhaseSum_pow_le (r + 1) hf N N hN
  have hfac : (r + 1 + 1).factorial = (r + 2).factorial := rfl
  rw [hfac] at hmain
  have hcount := weylMulti_le_of_approx_divisor hq hcop happ N N r hε hC hbound
  -- the term with a zero shift
  have hzero : ((r : ℝ) + 1) * (N : ℝ) ^ r * N ≤ D * (((r : ℝ) + 1) * (T * (N : ℝ) ^ (r + 2))) := by
    have hid : ((r : ℝ) + 1) * (N : ℝ) ^ r * N = ((r : ℝ) + 1) * P := by rw [hP, pow_succ]; ring
    have hle : ((r : ℝ) + 1) * P ≤ ((r : ℝ) + 1) * (T * (N : ℝ) ^ (r + 2)) := by
      rw [hTid]
      have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (r + 2) / q := by positivity
      have hr : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
      nlinarith
    have hDnn : (0 : ℝ) ≤ ((r : ℝ) + 1) * (T * (N : ℝ) ^ (r + 2)) := by positivity
    nlinarith
  -- the counting term
  have hcnt : (P / q + 1) * (4 * N + q * (1 + Real.log q))
      ≤ (20 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2)) := by
    rw [hTid]
    set X : ℝ := P / q with hX
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hXq : X * q = P := div_mul_cancel₀ P (ne_of_gt hqR)
    have hdiv : (N : ℝ) ^ (r + 2) / q = X * N := by
      rw [hsucc, hX]; field_simp
    rw [hdiv]
    nlinarith [mul_nonneg hXnn hlogq, mul_nonneg (mul_nonneg hXnn hlogq) hNR.le,
      mul_nonneg hXnn hNR.le, mul_nonneg hlogq hlogq, mul_nonneg hqR.le hlogq]
  -- the bracket of the folded majorant sum
  have hbrk : ((r : ℝ) + 1) * (N : ℝ) ^ r * N
        + D * ((P / q + 1) * (4 * N + q * (1 + Real.log q)))
      ≤ D * (((r : ℝ) + 21 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2))) := by
    have hDnn : (0 : ℝ) ≤ D := by linarith
    have h2 : D * ((P / q + 1) * (4 * N + q * (1 + Real.log q)))
        ≤ D * ((20 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2))) :=
      mul_le_mul_of_nonneg_left hcnt hDnn
    have hid : D * (((r : ℝ) + 21 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2)))
        = D * (((r : ℝ) + 1) * (T * (N : ℝ) ^ (r + 2)))
          + D * ((20 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2))) := by ring
    linarith
  -- assemble
  have hpre : (0 : ℝ) ≤ 8 ^ K * ((N : ℝ) + N) ^ K := by positivity
  have hstep : S ^ K * (P * ((N : ℝ) + N))
      ≤ 8 ^ K * ((N : ℝ) + N) ^ K
        * (D * (((r : ℝ) + 21 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2)))) :=
    hmain.trans (mul_le_mul_of_nonneg_left (hcount.trans hbrk) hpre)
  have h2N : ((N : ℝ) + N) ^ K = 2 ^ K * (N : ℝ) ^ K := by
    rw [show (N : ℝ) + N = 2 * N by ring, mul_pow]
  have h16 : (16 : ℝ) ^ K = 8 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  have hNpow : (0 : ℝ) < (N : ℝ) ^ (r + 2) := by positivity
  have hcancel : (S ^ K * 2) * (N : ℝ) ^ (r + 2)
      ≤ (16 ^ K * (N : ℝ) ^ K * D * ((r : ℝ) + 21 + 4 * Real.log q) * T)
        * (N : ℝ) ^ (r + 2) := by
    calc (S ^ K * 2) * (N : ℝ) ^ (r + 2) = S ^ K * (P * ((N : ℝ) + N)) := by rw [hsucc]; ring
      _ ≤ 8 ^ K * ((N : ℝ) + N) ^ K
            * (D * (((r : ℝ) + 21 + 4 * Real.log q) * (T * (N : ℝ) ^ (r + 2)))) := hstep
      _ = (16 ^ K * (N : ℝ) ^ K * D * ((r : ℝ) + 21 + 4 * Real.log q) * T)
            * (N : ℝ) ^ (r + 2) := by rw [h2N, h16]; ring
  have hred : S ^ K * 2
      ≤ 16 ^ K * (N : ℝ) ^ K * D * ((r : ℝ) + 21 + 4 * Real.log q) * T :=
    le_of_mul_le_mul_right hcancel hNpow
  have hSnn : (0 : ℝ) ≤ S ^ K := by positivity
  linarith

/-- **Weyl's inequality in its classical three-term form** for the monomial phase `α n^(r+2)`, with
explicit constants and no restriction on `q`. -/
theorem norm_monomialSum_pow_le_three_term {α : ℝ} {a : ℤ} {q : ℕ} (r : ℕ)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N)
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1))
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
        * weylBracket q N (r + 2) :=
  norm_polyPhaseSum_pow_le_three_term r (WeylGeneral.isPolyPhase_monomial (r + 2) α) hq hcop happ
    hN hε hC hbound

/-- **Weyl's inequality in its classical three-term form**, with the divisor loss and the logarithm
absorbed into `N^ε`.  For every `ε > 0` there is a constant `C ≥ 1` such that, for every coprime
approximation `|(r+2)! α − a/q| ≤ 1/q²` with `q ≤ N^(r+2)`,

`‖∑_{0 ≤ n < N} e(f n)‖^(2^(r+1)) ≤ C N^(2^(r+1)) N^ε (1/q + 1/N + q/N^(r+2))`

for every polynomial phase `f` of degree at most `r + 2` with `n^(r+2)`-coefficient `α`. -/
theorem exists_norm_polyPhaseSum_pow_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ),
      WeylGeneral.IsPolyPhase (r + 2) α f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ (2 ^ (r + 1))
        ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * weylBracket q N (r + 2) := by
  set e0 : ℝ := ε / (2 * (((r : ℝ) + 1) * r + 1)) with he0
  have hden : (0 : ℝ) < 2 * (((r : ℝ) + 1) * r + 1) := by positivity
  have he0pos : 0 < e0 := div_pos hε hden
  obtain ⟨C0, hC0, hbound⟩ := DivisorBound.exists_card_divisors_le he0pos
  set A : ℝ := (r : ℝ) + 21 + 8 * ((r : ℝ) + 2) / ε with hA
  have hA1 : 1 ≤ A := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (0 : ℝ) ≤ 8 * ((r : ℝ) + 2) / ε := by positivity
    rw [hA]; linarith
  refine ⟨16 ^ (2 ^ (r + 1)) * C0 ^ r * A, ?_, ?_⟩
  · have h16 : (1 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) := one_le_pow₀ (by norm_num)
    have hC0r : (1 : ℝ) ≤ C0 ^ r := one_le_pow₀ hC0
    have hprod : (1 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * C0 ^ r := by nlinarith
    nlinarith
  intro α f a q N hf hq hcop happ hN hqN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hmain := norm_polyPhaseSum_pow_le_three_term r hf hq hcop happ hN he0pos hC0 hbound
  have hTnn : 0 ≤ weylBracket q N (r + 2) := (weylBracket_pos hq hN).le
  -- the divisor loss is at most `C0^r N^(ε/2)`
  have hrpow : ((N : ℝ) ^ (r + 1)) ^ e0 = (N : ℝ) ^ (((r : ℝ) + 1) * e0) := by
    rw [← Real.rpow_natCast (N : ℝ) (r + 1), ← Real.rpow_mul hNpos.le]
    push_cast
    ring_nf
  have hDle : (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r ≤ C0 ^ r * (N : ℝ) ^ (ε / 2) := by
    rw [mul_pow, hrpow, ← Real.rpow_natCast ((N : ℝ) ^ (((r : ℝ) + 1) * e0)) r,
      ← Real.rpow_mul hNpos.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hid : ε / 2 = e0 * (((r : ℝ) + 1) * r + 1) := by
      rw [he0]; field_simp
    rw [hid]
    nlinarith [he0pos]
  -- the logarithm is absorbed into `N^(ε/2)`
  have hhalf : 0 < ε / 2 := by linarith
  have hlog : Real.log N ≤ (N : ℝ) ^ (ε / 2) / (ε / 2) :=
    Real.log_le_rpow_div hNpos.le hhalf
  have hlogq : Real.log q ≤ ((r : ℝ) + 2) * Real.log N := by
    have h1 : Real.log q ≤ Real.log ((N : ℝ) ^ (r + 2)) := Real.log_le_log hqpos hqN
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have hNhalf : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 hhalf.le
  have hLle : (r : ℝ) + 21 + 4 * Real.log q ≤ A * (N : ℝ) ^ (ε / 2) := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : 4 * Real.log q ≤ 4 * ((r : ℝ) + 2) * Real.log N := by nlinarith
    have h3 : 4 * ((r : ℝ) + 2) * Real.log N
        ≤ 4 * ((r : ℝ) + 2) * ((N : ℝ) ^ (ε / 2) / (ε / 2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h4 : 4 * ((r : ℝ) + 2) * ((N : ℝ) ^ (ε / 2) / (ε / 2))
        = (8 * ((r : ℝ) + 2) / ε) * (N : ℝ) ^ (ε / 2) := by
      field_simp
      ring
    have h5 : (r : ℝ) + 21 ≤ ((r : ℝ) + 21) * (N : ℝ) ^ (ε / 2) := by nlinarith
    have h6 : A * (N : ℝ) ^ (ε / 2)
        = ((r : ℝ) + 21) * (N : ℝ) ^ (ε / 2) + (8 * ((r : ℝ) + 2) / ε) * (N : ℝ) ^ (ε / 2) := by
      rw [hA]; ring
    linarith
  -- assemble
  have hLnn : (0 : ℝ) ≤ (r : ℝ) + 21 + 4 * Real.log q := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
    linarith
  have hpre : (0 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) := by positivity
  have hstep : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) * (A * (N : ℝ) ^ (ε / 2)) := by
    have h1 : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
          * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r
        ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hDle hpre
    have h2 : (0 : ℝ) ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) := by positivity
    calc 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
            * (C0 * ((N : ℝ) ^ (r + 1)) ^ e0) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
        ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2))
            * ((r : ℝ) + 21 + 4 * Real.log q) := mul_le_mul_of_nonneg_right h1 hLnn
      _ ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * (C0 ^ r * (N : ℝ) ^ (ε / 2))
            * (A * (N : ℝ) ^ (ε / 2)) := mul_le_mul_of_nonneg_left hLle h2
  have hsplit : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hfinal : 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C0 ^ r * (N : ℝ) ^ (ε / 2)) * (A * (N : ℝ) ^ (ε / 2))
      = 16 ^ (2 ^ (r + 1)) * C0 ^ r * A * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
    rw [← hsplit]; ring
  have hchain := hmain.trans (mul_le_mul_of_nonneg_right (hstep.trans (le_of_eq hfinal)) hTnn)
  exact hchain

/-- The three-term form with the divisor loss absorbed into `N^ε`, for the monomial phase. -/
theorem exists_norm_monomialSum_pow_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (a : ℤ) (q N : ℕ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1))
        ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * weylBracket q N (r + 2) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_pow_le_three_term r hε
  exact ⟨C, hC1, fun α a q N hq hcop happ hN hqN =>
    hCb α _ a q N (WeylGeneral.isPolyPhase_monomial (r + 2) α) hq hcop happ hN hqN⟩

/-- **Weyl's inequality, classical form.**  For every `ε > 0` there is a constant `C ≥ 1` such
that, for every coprime approximation `|d! α − a/q| ≤ 1/q²` with `q ≤ N^d`, `d = r + 2`,

`‖∑_{0 ≤ n < N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d-1))`,

for every polynomial phase `f` of degree at most `d` with `n^d`-coefficient `α`. -/
theorem exists_norm_polyPhaseSum_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ),
      WeylGeneral.IsPolyPhase (r + 2) α f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖
        ≤ C * (N : ℝ) ^ (1 + ε)
          * (weylBracket q N (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_pow_le_three_term r hε
  refine ⟨C, hC1, ?_⟩
  intro α f a q N hf hq hcop happ hN hqN
  set c : ℝ := (1 : ℝ) / 2 ^ (r + 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc]
    have : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
    rw [div_le_one (by positivity)]
    exact this
  have hcinv : ((2 ^ (r + 1) : ℕ) : ℝ)⁻¹ = c := by rw [hc, one_div]; push_cast; ring
  have hKne : (2 ^ (r + 1) : ℕ) ≠ 0 := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact norm_nonneg _
  set T : ℝ := weylBracket q N (r + 2) with hT
  have hTnn : 0 ≤ T := (weylBracket_pos hq hN).le
  have hB := hCb α f a q N hf hq hcop happ hN hqN
  have hBnn : (0 : ℝ) ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * T := by
    have : (0 : ℝ) ≤ C := by linarith
    positivity
  -- take `2^(r+1)`-th roots
  have hSroot : S ≤ (C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * T) ^ c := by
    have h1 : (S ^ (2 ^ (r + 1))) ^ (((2 ^ (r + 1) : ℕ) : ℝ))⁻¹ = S :=
      Real.pow_rpow_inv_natCast hSnn hKne
    calc S = (S ^ (2 ^ (r + 1))) ^ c := by rw [← hcinv, h1]
      _ ≤ (C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * T) ^ c :=
          Real.rpow_le_rpow (by positivity) hB hcpos.le
  -- and split the right-hand side
  have hsplit : (C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * T) ^ c
      = C ^ c * ((N : ℝ) ^ (2 ^ (r + 1))) ^ c * ((N : ℝ) ^ ε) ^ c * T ^ c := by
    have hC0 : (0 : ℝ) ≤ C := by linarith
    rw [Real.mul_rpow (by positivity) hTnn, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hC0 (by positivity)]
  have hCc : C ^ c ≤ C := by
    calc C ^ c ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 hcle
      _ = C := Real.rpow_one C
  have hNc : ((N : ℝ) ^ (2 ^ (r + 1))) ^ c = (N : ℝ) := by
    rw [← hcinv]
    exact Real.pow_rpow_inv_natCast hNpos.le hKne
  have hNec : ((N : ℝ) ^ ε) ^ c ≤ (N : ℝ) ^ ε := by
    rw [← Real.rpow_mul hNpos.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    nlinarith
  have hNeps : (N : ℝ) * (N : ℝ) ^ ε = (N : ℝ) ^ (1 + ε) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hTc : (0 : ℝ) ≤ T ^ c := Real.rpow_nonneg hTnn c
  have hNepsnn : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg hNpos.le ε
  have hCcnn : (0 : ℝ) ≤ C ^ c := Real.rpow_nonneg (by linarith) c
  calc S ≤ (C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * T) ^ c := hSroot
    _ = C ^ c * (N : ℝ) * ((N : ℝ) ^ ε) ^ c * T ^ c := by rw [hsplit, hNc]
    _ ≤ C * (N : ℝ) * (N : ℝ) ^ ε * T ^ c := by
        have h1 : C ^ c * (N : ℝ) * ((N : ℝ) ^ ε) ^ c ≤ C * (N : ℝ) * (N : ℝ) ^ ε := by
          have hstep1 : C ^ c * (N : ℝ) ≤ C * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hCc hNpos.le
          have hstep2 : ((N : ℝ) ^ ε) ^ c ≤ (N : ℝ) ^ ε := hNec
          have hnn1 : (0 : ℝ) ≤ C ^ c * (N : ℝ) := by positivity
          have hnn2 : (0 : ℝ) ≤ ((N : ℝ) ^ ε) ^ c := Real.rpow_nonneg hNepsnn c
          nlinarith
        exact mul_le_mul_of_nonneg_right h1 hTc
    _ = C * (N : ℝ) ^ (1 + ε) * T ^ c := by rw [← hNeps]; ring

/-- **Weyl's inequality, classical form**, for the monomial phase `α n^d`, `d = r + 2`. -/
theorem exists_norm_monomialSum_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (a : ℤ) (q N : ℕ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 + ε)
          * (weylBracket q N (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_le_three_term r hε
  exact ⟨C, hC1, fun α a q N hq hcop happ hN hqN =>
    hCb α _ a q N (WeylGeneral.isPolyPhase_monomial (r + 2) α) hq hcop happ hN hqN⟩

end WeylClassical

end RiemannHypothesis
