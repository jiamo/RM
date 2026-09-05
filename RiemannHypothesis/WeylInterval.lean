/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylClassical
import RiemannHypothesis.WeylBadlyGeneral

/-!
# Weyl's inequality over an arbitrary interval

Every Weyl bound of this repository is stated for the sum over `Finset.Ico 0 N`, that is, for an
interval starting at the origin.  The applications of Weyl's method — subdividing a long sum into
short ones, or summing over a dyadic block — need the same bound for the sum over an arbitrary
interval `Finset.Ico M (M + N)`, uniformly in the starting point `M`.

The point is that a polynomial phase stays a polynomial phase of the same degree, and with the
*same* leading coefficient, when its argument is translated: writing `f (n + M)` and expanding by
the binomial theorem changes the lower coefficients only.  That is
`WeylGeneral.IsPolyPhase.comp_add`, and everything else in this file is the composition of that
observation with the bounds of `RiemannHypothesis/WeylClassical.lean` and
`RiemannHypothesis/WeylBadlyGeneral.lean`.

The resulting bounds are uniform in `M`: the constants and the exponents are exactly those of the
interval `[0, N)`, because the Diophantine hypothesis is a hypothesis on the leading coefficient
alone, and translation does not move it.

## Main results

* `WeylGeneral.IsPolyPhase.comp_add` — a translate of a polynomial phase is a polynomial phase of
  the same degree with the same leading coefficient;
* `sum_e2pi_Ico_shift` — the sum over `[M, M + N)` is the sum over `[0, N)` of the translate;
* `norm_polyPhaseSum_Ico_pow_le_three_term` — the three-term Weyl inequality with explicit
  constants, over an arbitrary interval;
* `exists_norm_polyPhaseSum_Ico_le_three_term` — the classical form
  `‖∑_{M ≤ n < M + N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d-1))`, uniformly in `M`;
* `exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable` — Weyl's exponent
  `1 − 1/2^(d−1) + ε` for a badly approximable leading coefficient, uniformly in `M`;
* `exists_norm_monomialSum_Ico_le_three_term`,
  `exists_norm_monomialSum_Ico_le_of_badlyApproximable`,
  `exists_norm_monomialSum_Ico_sqrt_two_le` — the monomial phase `α n^d` over an arbitrary
  interval, the last at the explicit coefficient `α = √2/d!`.
-/

open Finset

namespace RiemannHypothesis

namespace WeylGeneral

/-- **A translate of a polynomial phase is a polynomial phase**, of the same degree and with the
same leading coefficient: only the lower coefficients change. -/
theorem IsPolyPhase.comp_add {d : ℕ} {α : ℝ} {f : ℤ → ℝ} (hf : IsPolyPhase d α f) (M : ℤ) :
    IsPolyPhase d α (fun n : ℤ => f (n + M)) := by
  classical
  obtain ⟨c, hcd, hc⟩ := hf
  refine ⟨fun i => ∑ j ∈ Finset.Ico i (d + 1), c j * (j.choose i : ℝ) * (M : ℝ) ^ (j - i), ?_, ?_⟩
  · have hIco : Finset.Ico d (d + 1) = {d} := Nat.Ico_succ_singleton d
    simp [hIco, hcd]
  · intro n
    simp only [hc]
    have hterm : ∀ j : ℕ, c j * (((n + M : ℤ)) : ℝ) ^ j
        = ∑ i ∈ Finset.range (j + 1),
            c j * ((n : ℝ) ^ i * (M : ℝ) ^ (j - i) * (j.choose i : ℝ)) := by
      intro j
      have hexp : (((n + M : ℤ)) : ℝ) ^ j
          = ∑ i ∈ Finset.range (j + 1), (n : ℝ) ^ i * (M : ℝ) ^ (j - i) * (j.choose i : ℝ) := by
        push_cast
        exact add_pow (n : ℝ) (M : ℝ) j
      rw [hexp, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    have hswap : ∑ j ∈ Finset.range (d + 1), ∑ i ∈ Finset.range (j + 1),
          c j * ((n : ℝ) ^ i * (M : ℝ) ^ (j - i) * (j.choose i : ℝ))
        = ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.Ico i (d + 1),
          c j * ((n : ℝ) ^ i * (M : ℝ) ^ (j - i) * (j.choose i : ℝ)) := by
      refine Finset.sum_comm' ?_
      intro j i
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hswap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end WeylGeneral

namespace WeylInterval

open KusminLandau

/-- The exponential sum over `[M, M + N)` is the exponential sum over `[0, N)` of the translated
phase. -/
theorem sum_e2pi_Ico_shift (f : ℤ → ℝ) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Finset.Ico M (M + N), e2pi (f n)
      = ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f (n + M)) := by
  have h : Finset.Ico M (M + (N : ℤ)) = (Finset.Ico (0 : ℤ) (N : ℤ)).map (addRightEmbedding M) := by
    rw [Finset.map_add_right_Ico]
    congr 1 <;> ring
  rw [h, Finset.sum_map]
  rfl

/-- **Weyl's inequality in its classical three-term form over an arbitrary interval**, with
explicit constants and no restriction on `q`.  The bound is uniform in the starting point `M`. -/
theorem norm_polyPhaseSum_Ico_pow_le_three_term {α : ℝ} {f : ℤ → ℝ} {a : ℤ} {q : ℕ} (r : ℕ)
    (hf : WeylGeneral.IsPolyPhase (r + 2) α f)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℤ) {N : ℕ} (hN : 0 < N)
    {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε) :
    ‖∑ n ∈ Finset.Ico M (M + N), e2pi (f n)‖ ^ (2 ^ (r + 1))
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ε) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
        * WeylClassical.weylBracket q N (r + 2) := by
  rw [sum_e2pi_Ico_shift]
  exact WeylClassical.norm_polyPhaseSum_pow_le_three_term r (hf.comp_add M) hq hcop happ hN hε hC
    hbound

/-- The three-term form over an arbitrary interval, with the divisor loss and the logarithm
absorbed into `N^ε`. -/
theorem exists_norm_polyPhaseSum_Ico_pow_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ) (M : ℤ),
      WeylGeneral.IsPolyPhase (r + 2) α f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico M (M + N), e2pi (f n)‖ ^ (2 ^ (r + 1))
        ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ε
          * WeylClassical.weylBracket q N (r + 2) := by
  obtain ⟨C, hC1, hCb⟩ := WeylClassical.exists_norm_polyPhaseSum_pow_le_three_term r hε
  refine ⟨C, hC1, ?_⟩
  intro α f a q N M hf hq hcop happ hN hqN
  rw [sum_e2pi_Ico_shift]
  exact hCb α _ a q N (hf.comp_add M) hq hcop happ hN hqN

/-- **Weyl's inequality, classical form, over an arbitrary interval.**  For every `ε > 0` there is
a constant `C ≥ 1` such that, for every coprime approximation `|d! α − a/q| ≤ 1/q²` with `q ≤ N^d`,
`d = r + 2`, every polynomial phase `f` of degree at most `d` with `n^d`-coefficient `α` and every
starting point `M`,

`‖∑_{M ≤ n < M + N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d-1))`. -/
theorem exists_norm_polyPhaseSum_Ico_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ) (M : ℤ),
      WeylGeneral.IsPolyPhase (r + 2) α f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico M (M + N), e2pi (f n)‖
        ≤ C * (N : ℝ) ^ (1 + ε)
          * (WeylClassical.weylBracket q N (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) := by
  obtain ⟨C, hC1, hCb⟩ := WeylClassical.exists_norm_polyPhaseSum_le_three_term r hε
  refine ⟨C, hC1, ?_⟩
  intro α f a q N M hf hq hcop happ hN hqN
  rw [sum_e2pi_Ico_shift]
  exact hCb α _ a q N (hf.comp_add M) hq hcop happ hN hqN

/-- The classical form over an arbitrary interval, for the monomial phase `α n^d`. -/
theorem exists_norm_monomialSum_Ico_le_three_term (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (a : ℤ) (q N : ℕ) (M : ℤ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico M (M + N), e2pi (α * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 + ε)
          * (WeylClassical.weylBracket q N (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_Ico_le_three_term r hε
  exact ⟨C, hC1, fun α a q N M hq hcop happ hN hqN =>
    hCb α _ a q N M (WeylGeneral.isPolyPhase_monomial (r + 2) α) hq hcop happ hN hqN⟩

/-- **Weyl's exponent for a badly approximable coefficient, over an arbitrary interval.**  If
`|d! α − a/q| ≥ c/q²` for every fraction `a/q`, then for every `ε > 0` there is a `C ≥ 1` with

`‖∑_{M ≤ n < M + N} e(f n)‖ ≤ C N^(1 − 1/2^(d−1) + ε)`,  `d = r + 2`,

for every polynomial phase `f` of degree at most `d` with `n^d`-coefficient `α`, every `N ≥ 1` and
every starting point `M`. -/
theorem exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f : ℤ → ℝ), WeylGeneral.IsPolyPhase (r + 2) α f →
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ (N : ℕ) (M : ℤ), 0 < N →
        ‖∑ n ∈ Finset.Ico M (M + N), e2pi (f n)‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C, hC1, hCb⟩ := WeylBadlyGeneral.exists_norm_polyPhaseSum_le_of_badlyApproximable r hε hc
  refine ⟨C, hC1, ?_⟩
  intro α f hf hbad N M hN
  rw [sum_e2pi_Ico_shift]
  exact hCb α _ (hf.comp_add M) hbad N hN

/-- Weyl's exponent for a badly approximable coefficient over an arbitrary interval, for the
monomial phase `α n^d`. -/
theorem exists_norm_monomialSum_Ico_le_of_badlyApproximable (r : ℕ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ α : ℝ,
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * α - (a : ℝ) / q|) →
      ∀ (N : ℕ) (M : ℤ), 0 < N →
        ‖∑ n ∈ Finset.Ico M (M + N), e2pi (α * (n : ℝ) ^ (r + 2))‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C, hC1, hCb⟩ := exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable r hε hc
  exact ⟨C, hC1, fun α hbad N M hN =>
    hCb α _ (WeylGeneral.isPolyPhase_monomial (r + 2) α) hbad N M hN⟩

/-- **An explicit coefficient over an arbitrary interval.**  For `α = √2/d!` and every `ε > 0`,

`‖∑_{M ≤ n < M + N} e((√2/d!) n^d)‖ ≤ C N^(1 − 1/2^(d−1) + ε)`,  `d = r + 2`,

for every `N ≥ 1` and every starting point `M`. -/
theorem exists_norm_monomialSum_Ico_sqrt_two_le (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (M : ℤ), 0 < N →
      ‖∑ n ∈ Finset.Ico M (M + N),
          e2pi (Real.sqrt 2 / ((r + 2).factorial : ℝ) * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ε) := by
  obtain ⟨C, hC1, hCb⟩ :=
    exists_norm_monomialSum_Ico_le_of_badlyApproximable r hε (c := 1 / 4) (by norm_num)
  refine ⟨C, hC1, ?_⟩
  intro N M hN
  refine hCb (Real.sqrt 2 / ((r + 2).factorial : ℝ)) ?_ N M hN
  intro a q hq
  have hfac : ((r + 2).factorial : ℝ) ≠ 0 := by
    have := (r + 2).factorial_pos
    positivity
  have hid : ((r + 2).factorial : ℝ) * (Real.sqrt 2 / ((r + 2).factorial : ℝ)) = Real.sqrt 2 := by
    field_simp
  rw [hid]
  exact WeylQuadratic.badlyApproximable_sqrt_two a q hq

end WeylInterval

end RiemannHypothesis
