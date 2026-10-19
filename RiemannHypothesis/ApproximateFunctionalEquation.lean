/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZetaChi
import RiemannHypothesis.SqrtHarmonic

/-!
# The approximate functional equation on the critical line

The *approximate functional equation* of Hardy and Littlewood is the statement that, on the
critical line, `ζ` is — up to an error smaller than either piece — the sum of **two** Dirichlet
polynomials of length `√(t/2π)`, the second one reflected by the factor `χ` of the functional
equation:

`ζ(1/2 + i t) = ∑_{n ≤ x} n^(-1/2-i t) + χ(1/2 + i t) ∑_{n ≤ x} n^(-1/2+i t) + O(t^(-1/4))`,
`x = √(t/2π)`.

Compare it with what is *unconditionally* available in this repository.  The Euler–Maclaurin
representation (`RiemannHypothesis.Continuation`, `RiemannHypothesis.StripMeanSquareBernoulli`)
also writes `ζ` as a Dirichlet polynomial plus an error, but its error is only small when the
polynomial is *longer* than `t`; the successive Euler–Maclaurin corrections are of relative size
`(t/N)^k`, so at `N ≍ t` the expansion stops gaining and at `N ≍ √t` it says nothing at all.
Halving the length of the sum, from `t` to `√t`, is exactly the content of the approximate
functional equation and exactly what Euler–Maclaurin cannot do.

## What this file contains, and what it does not

`AFECriticalLine C` below is the **statement** of the approximate functional equation with an
explicit constant, as a `Prop`.  It is *not proved in this file*; it is proved, with `C = 250`, in
`RiemannHypothesis.AFECriticalLineProof` (`afeCriticalLine : AFECriticalLine 250`), by exact
Poisson summation between half-integers and a stationary-phase evaluation of the resulting
integrals.  This file proves the parts of the surrounding theory that are unconditional, and one
consequence stated with the approximate functional equation as a hypothesis:

* `zetaSum`, `zetaSumDual` — the two Dirichlet polynomials, `∑_{n ≤ N} n^(-s)` and
  `∑_{n ≤ N} n^(s-1)`;
* `zetaSumDual_criticalLine` — on the critical line the second is the complex conjugate of the
  first, so the two terms of the approximate functional equation are conjugate up to the phase
  `χ` (`RiemannHypothesis.ZetaChi.norm_zetaChi_criticalLine`);
* `norm_zetaSum_criticalLine_le` — the trivial bound `‖∑_{n ≤ N} n^(-1/2-i t)‖ ≤ 2 √N`,
  uniform in `t`;
* `norm_riemannZeta_criticalLine_le_of_afe` — **conditionally on the approximate functional
  equation**, the log-free convexity bound `‖ζ(1/2 + i t)‖ ≤ (C + 4) t^(1/4)`.

  With `afeCriticalLine` it is unconditional:
  `RiemannHypothesis.norm_riemannZeta_criticalLine_le` gives `‖ζ(1/2 + i t)‖ ≤ 254 t^(1/4)` for
  `t ≥ 2`.  (The log-free convexity bound is also proved, by Phragmén–Lindelöf, in
  `RiemannHypothesis.ConvexityLogFree`.)  Note that the *trivial* estimate of the two sums
  is all that is used: no cancellation in either Dirichlet polynomial is exploited.  Exploiting
  it — with the van der Corput machinery of `RiemannHypothesis.VanDerCorputSums` — is what would
  give the subconvexity exponent `1/6`.

## Hypothesis hygiene (AGENTS.md)

1. **Direction.**  When the statement was recorded, nothing in this repository gave either half
   of `AFECriticalLine`; the free statement of the same shape was the Euler–Maclaurin
   approximation with a sum of length `≥ t` and no `χ`-term (`RiemannHypothesis.Continuation`),
   *weaker* in exactly the direction that matters.  Since 2026-10-19 the statement itself is a
   theorem: `afeCriticalLine : AFECriticalLine 250` (`RiemannHypothesis.AFECriticalLineProof`).
2. **Strength.**  `AFECriticalLine` yields the log-free convexity bound `t^(1/4)` (proved below),
   and with cancellation it yields `t^(1/6)`; it does not yield, and is not equivalent to, the
   Lindelöf hypothesis, let alone the Riemann hypothesis.  It is a statement about `ζ` on a
   *single* line, with an error term that is a power of `t` — no zero-free region and no
   information about zeroes follows from it.
3. **Non-triviality.**  It is a classical unconditional theorem of Hardy and Littlewood (1921);
   its standard proofs go through the Riemann–Siegel contour integral, or through truncated
   Poisson summation followed by a stationary-phase evaluation (van der Corput's B process).
   It is proved in this repository (`RiemannHypothesis.AFECriticalLineProof`, constant `250`) by
   a variant of the second route: exact Poisson summation between half-integers
   (`RiemannHypothesis.PoissonSummationInterval`) and the exact Mellin evaluation of the complete
   stationary-phase integral (`RiemannHypothesis.ZetaMellinPhase`).  It is in no way derived from
   the Riemann hypothesis.
4. **Attribution.**  The statement is Theorem 4.12 of Titchmarsh's *The Theory of the Riemann
   Zeta-Function* specialized to `σ = 1/2`, `x = y = √(t/2π)`, where the error term is
   `O(x^(-σ) + t^(1/2-σ) y^(σ-1)) = O(t^(-1/4))`.  It quantifies over `ζ` on the critical line
   and over nothing else.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

/-- The Dirichlet polynomial `∑_{1 ≤ n ≤ N} n^(-s)`. -/
def zetaSum (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

/-- The reflected Dirichlet polynomial `∑_{1 ≤ n ≤ N} n^(s-1)`, the one that the approximate
functional equation multiplies by `χ(s)`. -/
def zetaSumDual (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (s - 1)

/-- On the critical line the reflected sum is the complex conjugate of the direct sum. -/
theorem zetaSumDual_criticalLine (N : ℕ) (t : ℝ) :
    zetaSumDual N (1 / 2 + (t : ℂ) * I) = (starRingEnd ℂ) (zetaSum N (1 / 2 + (t : ℂ) * I)) := by
  rw [zetaSumDual, zetaSum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_nonneg hn0.le]
    exact Real.pi_ne_zero.symm
  have hconj : (starRingEnd ℂ) ((n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)))
      = (n : ℂ) ^ ((starRingEnd ℂ) (-(1 / 2 + (t : ℂ) * I))) := by
    rw [Complex.cpow_conj _ _ harg]
    congr 2
    simp
  rw [hconj]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- The trivial bound for the Dirichlet polynomial on the critical line: `‖∑_{n ≤ N} n^(-1/2-it)‖
≤ 2 √N`, uniformly in `t`. -/
theorem norm_zetaSum_criticalLine_le (N : ℕ) (t : ℝ) :
    ‖zetaSum N (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * Real.sqrt N := by
  refine le_trans (norm_sum_le _ _) (le_trans (le_of_eq ?_) (sum_one_div_sqrt_le N))
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := hn1
  rw [Complex.norm_natCast_cpow_of_pos hn0]
  have hre : (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2) := by simp
  rw [hre, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]

/-- The length of the two sums in the approximate functional equation at height `t`:
`⌊√(t/2π)⌋`. -/
def afeLength (t : ℝ) : ℕ := ⌊Real.sqrt (t / (2 * Real.pi))⌋₊

/-- **The approximate functional equation of Hardy and Littlewood, on the critical line**, with
an explicit constant `C`:

`‖ζ(1/2+it) − ∑_{n ≤ x} n^(-1/2-it) − χ(1/2+it) ∑_{n ≤ x} n^(-1/2+it)‖ ≤ C t^(-1/4)`,
`x = √(t/2π)`, for every `t ≥ 2`.

This is a **statement**, not a theorem of this repository: it is assumed, never proved, and every
result that uses it takes it as a hypothesis.  See the module docstring for the four hypothesis
hygiene questions of `AGENTS.md`. -/
def AFECriticalLine (C : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t →
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ C * t ^ (-(1 / 4) : ℝ)

/-- `√(afeLength t) ≤ t^(1/4)` for `t ≥ 0`: the sums of the approximate functional equation have
`√(t/2π) ≤ √t` terms. -/
theorem sqrt_afeLength_le {t : ℝ} (ht : 0 ≤ t) : Real.sqrt (afeLength t) ≤ t ^ ((1 : ℝ) / 4) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : ((afeLength t : ℕ) : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (t / (2 * Real.pi)) ≤ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : Real.sqrt (afeLength t) ≤ Real.sqrt (Real.sqrt t) :=
    Real.sqrt_le_sqrt (le_trans h1 h2)
  refine h3.trans_eq ?_
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  norm_num

/-- **Conditionally on the approximate functional equation, the log-free convexity bound on the
critical line**: `‖ζ(1/2 + i t)‖ ≤ (C + 4) t^(1/4)` for `t ≥ 2`.

Unconditionally the repository has only `‖ζ(1/2+it)‖ = O(√t log t)`
(`RiemannHypothesis.StripGrowth`). Only the *trivial* bound for the two Dirichlet polynomials is
used here; no cancellation is exploited. -/
theorem norm_riemannZeta_criticalLine_le_of_afe {C : ℝ} (hafe : AFECriticalLine C) {t : ℝ}
    (ht : 2 ≤ t) : ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ (C + 4) * t ^ ((1 : ℝ) / 4) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have h := hafe t ht
  have hquarter : (0 : ℝ) < t ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right hquarter).mp (le_trans (norm_nonneg _) h)
  have hexp : t ^ (-(1 / 4) : ℝ) ≤ t ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hS : ‖zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * t ^ ((1 : ℝ) / 4) := by
    refine (norm_zetaSum_criticalLine_le (afeLength t) t).trans ?_
    have := sqrt_afeLength_le ht0.le
    linarith
  have hD : ‖zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 2 * t ^ ((1 : ℝ) / 4) := by
    rw [norm_mul, norm_zetaChi_criticalLine, one_mul, zetaSumDual_criticalLine, RCLike.norm_conj]
    exact hS
  have hsplit : riemannZeta (1 / 2 + (t : ℂ) * I)
      = (riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
          - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I))
        + zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        + zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I) := by
    ring
  rw [hsplit]
  refine le_trans norm_add₃_le ?_
  have hCmul : C * t ^ (-(1 / 4) : ℝ) ≤ C * t ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left hexp hC
  linarith

end RiemannHypothesis
