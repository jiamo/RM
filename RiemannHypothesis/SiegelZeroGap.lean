/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization

The proofs of the main theorems are the native absorption of openai/math, family 003
(github.com/openai/math, revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache 2.0; see
NOTICE and LICENSES/openai-math-LICENSE), ported under `RiemannHypothesis/Family003/`.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Main

/-!
# A uniform logarithmic gap for real zeroes of real primitive Dirichlet `L`-functions

* `exists_absolute_real_zero_gap` — there is an absolute constant `c > 0` such that for every
  modulus `q ≥ 3`, every primitive non-trivial Dirichlet character `χ` modulo `q` with real
  values, and every real `β ∈ (0, 1)` with `L(β, χ) = 0` (Mathlib's
  `DirichletCharacter.LFunction`), one has `c ≤ (1 - β) log q`.  This is upstream
  `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` (openai/math `fd4aeeb`,
  module `OAI.NumberTheory.SiegelZeros.Main`, comparator `ComparatorChallenges/SiegelZeros`).
* `dirichletRealZeroBound` — the same statement with the three conditions on `β` conjoined
  (upstream `OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof`).

The constant `c` does not depend on `q` or `χ`, and both parities of `χ` are covered.  The
statements mention only Mathlib's `DirichletCharacter`, `DirichletCharacter.IsPrimitive` and
`DirichletCharacter.LFunction`; no hypothesis besides the displayed ones appears, and the axioms
are `propext`, `Classical.choice`, `Quot.sound`.

This is a statement about real zeroes of `L(s, χ)` for real characters (the "exceptional"
or Landau–Siegel zeroes); it says nothing about the Riemann hypothesis.
-/

namespace RiemannHypothesis.SiegelZeroGap

/-- **No Landau–Siegel zeroes.**  There is an absolute constant `c > 0` such that every real
zero `β ∈ (0, 1)` of the `L`-function of a real primitive non-trivial Dirichlet character of
modulus `q ≥ 3` satisfies `c ≤ (1 - β) log q`. -/
theorem exists_absolute_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) :=
  RiemannHypothesis.Family003.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap

/-- The same, with the conditions on `β` conjoined. -/
theorem dirichletRealZeroBound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) :=
  RiemannHypothesis.Family003.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof

end RiemannHypothesis.SiegelZeroGap
