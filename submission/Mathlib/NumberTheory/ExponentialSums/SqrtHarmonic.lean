/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
/-
## Extraction note

This file was extracted from `RiemannHypothesis/SqrtHarmonic.lean` in the `riemann_hypothesis_formalization` repository
(Lean 4 / mathlib4 v4.28.0 snapshot, 2026-09-16) as the proposed mathlib contribution
`Mathlib/NumberTheory/ExponentialSums/SqrtHarmonic.lean`. The theorem statements and proofs are transcribed
unchanged; only packaging changed: narrowed imports, removal of the upstream project's private
definitions (helpers such as `e2pi`, `cotPi` and `expI` are local where needed), and, where
present, replacement of fragile API usages by self-contained local arguments
(`Nat.findGreatest` -> `lastIndexWith`, `monotoneOn_of_hasDerivWithinAt_nonneg` -> the mean value
theorem).

To build in a mathlib checkout: place this tree under `Mathlib/NumberTheory/ExponentialSums/`
and run `lake build Mathlib.NumberTheory.ExponentialSums.SqrtHarmonic`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Two elementary square-root sums

The two comparisons `∑_{n ≤ N} 1/√n ≤ 2 √N` and `∑_{n ≤ N} √n ≤ N √N`, used both by the
trivial estimate of the Dirichlet polynomials of the approximate functional equation
(`RiemannHypothesis.ApproximateFunctionalEquation`) and by the summation over the shifts of
van der Corput's A process (`RiemannHypothesis.VanDerCorputThird`).
-/

noncomputable section

/-- `∑_{n ≤ N} 1/√n ≤ 2 √N`. -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 / Real.sqrt n) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : 1 / Real.sqrt ((N : ℝ) + 1) ≤ 2 * Real.sqrt ((N : ℝ) + 1) - 2 * Real.sqrt N := by
        have h1 : (0 : ℝ) < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have h2 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
        have h3 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
        have h4 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
        rw [div_le_iff₀ h1]
        nlinarith [Real.sqrt_nonneg (N : ℝ), h1, h2, h3, h4]
      push_cast
      linarith

/-- `∑_{n < N} √n ≤ N √N`, the trivial termwise bound. -/
theorem sum_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.sqrt n ≤ (N : ℝ) * Real.sqrt N := by
  calc ∑ n ∈ Finset.range N, Real.sqrt n ≤ ∑ _n ∈ Finset.range N, Real.sqrt N :=
        Finset.sum_le_sum fun n hn =>
          Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_range.mp hn).le)
    _ = (N : ℝ) * Real.sqrt N := by simp [Finset.sum_const]

