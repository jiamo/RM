/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylClassical
import RiemannHypothesis.WeylBadlyApproximable

/-!
# Weyl's bound for a badly approximable coefficient, in arbitrary degree

Weyl's inequality is conditional on a rational approximation to `d! α` with a denominator in a
prescribed range, and it must be: for `α` rational there is no cancellation at all.  For `d = 2`
(`M1-WEYL-BADLY-APPROXIMABLE`) and for `d = 3` (`M1-WEYL-CUBIC`) the repository removes the
hypothesis for *badly approximable* coefficients, where Dirichlet's theorem is guaranteed to
produce a large denominator; the open boundary of `M1-WEYL-GENERAL` recorded that this was not
carried out in general degree.

This file carries it out, using the three-term form of `RiemannHypothesis.WeylClassical`.  If
`d! α` is badly approximable with constant `c`, then Dirichlet's approximation theorem with
parameter `N` produces a coprime `a/q` with `q ≤ N` and `|d! α − a/q| ≤ 1/(q(N+1))`, and the
badly-approximable hypothesis forces `q ≥ c(N+1)`.  Both ends of the three-term bracket are then
under control:

`1/q + 1/N + q/N^d ≤ (1/c + 2)/N`,

so the classical inequality gives a saving of a whole power of `N`.

## Main results

* `exists_norm_monomialSum_pow_mul_le_of_badlyApproximable` — for every `ε > 0` and every `c > 0`
  there is a `C` such that, whenever `d! α` is badly approximable with constant `c`,

  `‖∑_{0 ≤ n < N} e(α n^d)‖^(2^(d-1)) · N ≤ C N^(2^(d-1)) N^ε`  for every `N ≥ 1`;

* `exists_norm_monomialSum_le_of_badlyApproximable` — the same after taking roots,
  `‖∑_{n<N} e(α n^d)‖ ≤ C N^(1 − 1/2^(d−1) + ε)`, **unconditionally in `N`**;
* `exists_norm_monomialSum_sqrt_two_le` — the explicit example `α = √2/d!`, for which `d! α = √2`
  is badly approximable with constant `1/4`.

## Scope

The `ε` is inherited from the divisor loss of `RiemannHypothesis.WeylClassical` and is not removed.
The constant depends on `c`, on `ε` and on the degree, and is not optimized.  Badly approximable
coefficients are a measure-zero set; for a general irrational `α` the qualitative equidistribution
of `α n^d` is what the repository proves (`M1-WEYL-CRITERION` and
`RiemannHypothesis.WeylPolynomialGeneral`), with no rate.  Nothing about `ζ` follows: polynomial
phases are not zeta phases.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace WeylBadlyGeneral

open KusminLandau WeylClassical WeylQuadratic

/-- **Weyl's bound for a badly approximable coefficient, in arbitrary degree.**  If
`|d! α − a/q| ≥ c/q²` for every fraction `a/q`, then for every polynomial phase `f` of degree at
most `d` with `n^d`-coefficient `α` and every `N ≥ 1`

`‖∑_{0 ≤ n < N} e(f n)‖^(2^(d-1)) · N ≤ C N^(2^(d-1)) N^ε`,  `d = r + 2`,

with `C` depending only on `r`, `ε` and `c`. -/
theorem exists_norm_polyPhaseSum_pow_mul_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ), WeylGeneral.IsPolyPhase (r + 2) α f →
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ (2 ^ (r + 1)) * N
          ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
  obtain ⟨C0, hC01, hCb⟩ := exists_norm_polyPhaseSum_pow_le_three_term r hε
  refine ⟨C0 * (1 / c + 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 / c := by positivity
    nlinarith
  intro α f hf hbad N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨a, q, hq, hqN, hcop, happ⟩ := exists_coprime_approx (((r + 2).factorial : ℝ) * α) hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  -- the badly-approximable hypothesis forces a large denominator
  have hqlow : c * ((N : ℝ) + 1) ≤ q := le_den_of_badlyApproximable hbad hq happ
  -- Dirichlet's approximation is in particular an approximation of quality `1/q²`
  have happ2 : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.trans ?_
    have hle : (q : ℝ) ^ 2 ≤ (q : ℝ) * ((N : ℝ) + 1) := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) hle
  have hqNr : (q : ℝ) ≤ (N : ℝ) ^ (r + 2) := by
    refine hqNR.trans ?_
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ (r + 2) := pow_le_pow_right₀ hN1 (by omega)
  have hB := hCb α f a q N hf hq hcop happ2 hN hqNr
  -- the three-term bracket is `O(1/N)`
  have hbracket : weylBracket q N (r + 2) ≤ (1 / c + 2) / N := by
    have h1 : 1 / (q : ℝ) ≤ (1 / c) / N := by
      have hlow : c * (N : ℝ) ≤ q := by nlinarith
      have hcN : (0 : ℝ) < c * N := by positivity
      have := one_div_le_one_div_of_le hcN hlow
      calc 1 / (q : ℝ) ≤ 1 / (c * N) := this
        _ = (1 / c) / N := by field_simp
    have h2 : (q : ℝ) / (N : ℝ) ^ (r + 2) ≤ 1 / N := by
      rw [div_le_div_iff₀ (by positivity) hNpos]
      calc (q : ℝ) * N ≤ (N : ℝ) * N := by nlinarith
        _ = (N : ℝ) ^ 2 := by ring
        _ ≤ (N : ℝ) ^ (r + 2) := pow_le_pow_right₀ hN1 (by omega)
        _ = 1 * (N : ℝ) ^ (r + 2) := by ring
    have hsum : (1 / c) / N + 1 / (N : ℝ) + 1 / N = (1 / c + 2) / N := by field_simp; ring
    unfold weylBracket
    linarith
  -- combine
  have hSnn : (0 : ℝ) ≤ ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^
      (2 ^ (r + 1)) := by positivity
  have hAnn : (0 : ℝ) ≤ C0 * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
    have : (0 : ℝ) ≤ C0 := by linarith
    positivity
  have hstep : ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ (2 ^ (r + 1))
      ≤ C0 * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * ((1 / c + 2) / N) :=
    hB.trans (mul_le_mul_of_nonneg_left hbracket hAnn)
  have hmulN := mul_le_mul_of_nonneg_right hstep hNpos.le
  have hid : C0 * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε * ((1 / c + 2) / N) * N
      = C0 * (1 / c + 2) * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
    field_simp
  linarith [hmulN, le_of_eq hid]

/-- **Weyl's exponent for a badly approximable coefficient, in arbitrary degree.**  If `d! α` is
badly approximable then, for every `ε > 0` and every polynomial phase `f` of degree at most `d`
with `n^d`-coefficient `α`,

`‖∑_{0 ≤ n < N} e(f n)‖ ≤ C N^(1 − 1/2^(d−1) + ε)` for every `N ≥ 1`,  `d = r + 2`,

with no hypothesis on `N`. -/
theorem exists_norm_polyPhaseSum_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ), WeylGeneral.IsPolyPhase (r + 2) α f →
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C0, hC01, hCb⟩ := exists_norm_polyPhaseSum_pow_mul_le_of_badlyApproximable r hε hc
  refine ⟨C0, hC01, ?_⟩
  intro α f hf hbad N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set K : ℕ := 2 ^ (r + 1) with hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by rw [hK]; positivity
  have hKne : K ≠ 0 := by rw [hK]; positivity
  set c0 : ℝ := ((K : ℕ) : ℝ)⁻¹ with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0le : c0 ≤ 1 := by
    rw [hc0, inv_le_one₀ hKpos]
    rw [hK]
    exact_mod_cast Nat.one_le_two_pow
  set S : ℝ := ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact norm_nonneg _
  have hB := hCb α f hf hbad N hN
  -- divide by `N`
  have hpow : S ^ K ≤ C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε) := by
    have hdiv : S ^ K ≤ C0 * (N : ℝ) ^ K * (N : ℝ) ^ ε / N := by
      rw [le_div_iff₀ hNpos]
      exact hB
    have hid : C0 * (N : ℝ) ^ K * (N : ℝ) ^ ε / N = C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε) := by
      rw [Real.rpow_add hNpos, Real.rpow_sub hNpos, Real.rpow_natCast, Real.rpow_one]
      field_simp
    linarith [hdiv, le_of_eq hid]
  -- take `K`-th roots
  have hCnn : (0 : ℝ) ≤ C0 := by linarith
  have hRnn : (0 : ℝ) ≤ C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε) := by positivity
  have hroot : S ≤ (C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 := by
    have h1 : (S ^ K) ^ c0 = S := by rw [hc0]; exact Real.pow_rpow_inv_natCast hSnn hKne
    calc S = (S ^ K) ^ c0 := h1.symm
      _ ≤ (C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 :=
          Real.rpow_le_rpow (by positivity) hpow hc0pos.le
  have hsplit : (C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0
      = C0 ^ c0 * ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 := Real.mul_rpow hCnn (by positivity)
  have hCc : C0 ^ c0 ≤ C0 := by
    calc C0 ^ c0 ≤ C0 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC01 hc0le
      _ = C0 := Real.rpow_one C0
  have hNc : ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0
      ≤ (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
    rw [← Real.rpow_mul hNpos.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hKR : (K : ℝ) = (2 : ℝ) ^ (r + 1) := by rw [hK]; push_cast; ring
    have hinv : c0 = ((2 : ℝ) ^ (r + 1))⁻¹ := by rw [hc0, hKR]
    rw [hinv]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (r + 1) := by positivity
    have hexp : ((K : ℝ) - 1 + ε) * ((2 : ℝ) ^ (r + 1))⁻¹
        = 1 - 1 / (2 : ℝ) ^ (r + 1) + ε / (2 : ℝ) ^ (r + 1) := by
      rw [hKR]; field_simp
    rw [hexp]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
    have : ε / (2 : ℝ) ^ (r + 1) ≤ ε := by
      rw [div_le_iff₀ h2]
      nlinarith
    linarith
  have hNcnn : (0 : ℝ) ≤ ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 := Real.rpow_nonneg (by positivity) c0
  have hCcnn : (0 : ℝ) ≤ C0 ^ c0 := Real.rpow_nonneg hCnn c0
  calc S ≤ (C0 * (N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 := hroot
    _ = C0 ^ c0 * ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 := hsplit
    _ ≤ C0 * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
        have h1 : C0 ^ c0 * ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0
            ≤ C0 * ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0 :=
          mul_le_mul_of_nonneg_right hCc hNcnn
        have h2 : C0 * ((N : ℝ) ^ ((K : ℝ) - 1 + ε)) ^ c0
            ≤ C0 * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) :=
          mul_le_mul_of_nonneg_left hNc hCnn
        linarith

/-- **Weyl's bound for a badly approximable coefficient**, for the monomial phase `α n^d`. -/
theorem exists_norm_monomialSum_pow_mul_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ α : ℝ,
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * N
          ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_pow_mul_le_of_badlyApproximable r hε hc
  exact ⟨C, hC1, fun α hbad N hN =>
    hCb α _ (WeylGeneral.isPolyPhase_monomial (r + 2) α) hbad N hN⟩

/-- **Weyl's exponent for a badly approximable coefficient**, for the monomial phase `α n^d`. -/
theorem exists_norm_monomialSum_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ α : ℝ,
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (α * (n : ℝ) ^ (r + 2))‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_le_of_badlyApproximable r hε hc
  exact ⟨C, hC1, fun α hbad N hN =>
    hCb α _ (WeylGeneral.isPolyPhase_monomial (r + 2) α) hbad N hN⟩

/-- **An explicit coefficient in every degree.**  For `α = √2/d!` the coefficient `d! α = √2` is
badly approximable with constant `1/4`, so for every `ε > 0`

`‖∑_{0 ≤ n < N} e((√2/d!) n^d)‖ ≤ C N^(1 − 1/2^(d−1) + ε)` for every `N ≥ 1`,  `d = r + 2`. -/
theorem exists_norm_monomialSum_sqrt_two_le (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          e2pi (Real.sqrt 2 / ((r + 2).factorial : ℝ) * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C, hC1, hCb⟩ :=
    exists_norm_monomialSum_le_of_badlyApproximable r hε (c := 1 / 4) (by norm_num)
  refine ⟨C, hC1, ?_⟩
  intro N hN
  refine hCb (Real.sqrt 2 / ((r + 2).factorial : ℝ)) ?_ N hN
  intro a q hq
  have hfac : ((r + 2).factorial : ℝ) ≠ 0 := by
    have := (r + 2).factorial_pos
    positivity
  have hid : ((r + 2).factorial : ℝ) * (Real.sqrt 2 / ((r + 2).factorial : ℝ)) = Real.sqrt 2 := by
    field_simp
  rw [hid]
  exact badlyApproximable_sqrt_two a q hq

end WeylBadlyGeneral

end RiemannHypothesis
