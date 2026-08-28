/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ExplicitFormula
import RiemannHypothesis.Main

/-!
# Weil's positivity criterion

The explicit formula (`RiemannHypothesis.weil_explicit_formula`) writes a sum over the
nontrivial zeroes of `ζ` as an arithmetic term plus an archimedean term.  Weil's criterion
reads that identity backwards: the Riemann hypothesis is equivalent to the nonnegativity of
the resulting quadratic form on a suitable class of test functions.

## Definitions

* `weilFunctional k` — the right-hand side of the explicit formula, i.e.
  `h(i/2) + h(−i/2) − ∑ₙ Λ(n) n^{−1/2}(k(log n) + k(−log n))`
  `+ (1/2π)∫ h(r)(Re ψ(1/4+ir/2) − log π) dr`, where `h = testTransform k`.  By the
  explicit formula it equals `∑_ρ m_ρ h(γ_ρ)`.
* `IsPositiveTestFunction k` — `k` is `C²` with compact support and its transform `h` is real
  and nonnegative on the real axis.  This is the property that the classical class of test
  functions `k = k₀ ⋆ k₀^*` has, since then `h(r) = |h₀(r)|²` for real `r`.
* `WeilPositivityCriterion` — the criterion itself, as a `Prop`:
  `ZetaForm ↔ ∀ k, IsPositiveTestFunction k → 0 ≤ Re (weilFunctional k)`.

## Main results

* `weilFunctional_eq_zeroSum` — the explicit formula in this vocabulary.
* `zeroOrdinate_eq_ofReal` — a zero on the critical line has a real ordinate.
* `weilFunctional_nonneg_of_zetaForm` — **the easy direction of Weil's criterion**: the
  Riemann hypothesis implies the positivity.  Under `ZetaForm` every nontrivial zero lies on
  the critical line, so every ordinate `γ_ρ` is real, every term `m_ρ h(γ_ρ)` is a nonnegative
  real, and the (absolutely convergent) sum is nonnegative.

The converse — positivity implies the Riemann hypothesis — is *not* proved here.  It is the
substance of Weil's criterion and requires constructing, from a hypothetical zero off the
line, a test function on which the form is negative.  `WeilPositivityCriterion` is therefore
recorded as a `Prop` only, and no term of that type exists in this repository.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology ArithmeticFunction

namespace RiemannHypothesis

/-- The **Weil functional** of a test function `k`: the right-hand side of the explicit
formula. -/
def weilFunctional (k : ℝ → ℂ) : ℂ :=
  testTransform k (I / 2) + testTransform k (-I / 2)
    - ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
    + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, testTransform k r * (archimedeanBracket r : ℂ)

/-- The class of test functions on which Weil's criterion is stated: `C²` with compact
support, and with a transform that is real and nonnegative on the real axis.  A convolution
square `k = k₀ ⋆ k₀^*` has this property, its transform being `|h₀|²` there. -/
def IsPositiveTestFunction (k : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
    ∀ r : ℝ, ∃ c : ℝ, 0 ≤ c ∧ testTransform k r = (c : ℂ)

/-- **Weil's positivity criterion**, as a proposition: the Riemann hypothesis holds if and
only if the Weil functional is nonnegative on every positive test function.  This is stated,
not proved; only the forward implication is proved below
(`weilFunctional_nonneg_of_zetaForm`). -/
def WeilPositivityCriterion : Prop :=
  ZetaForm ↔ ∀ k : ℝ → ℂ, IsPositiveTestFunction k → 0 ≤ (weilFunctional k).re

/-- The explicit formula, restated: the Weil functional of `k` is the sum over the nontrivial
zeroes of `m_ρ h(γ_ρ)`. -/
theorem weilFunctional_eq_zeroSum (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    ∑' ρ : nontrivialZeroSet,
        (zeroMultiplicity ρ : ℂ) * testTransform k (zeroOrdinate ρ) = weilFunctional k :=
  (weil_explicit_formula k hk hkc).2

/-- A zero on the critical line has a real ordinate: `γ_ρ = (ρ − 1/2)/i = Im ρ`. -/
theorem zeroOrdinate_eq_ofReal {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    zeroOrdinate ρ = (ρ.im : ℂ) := by
  unfold zeroOrdinate Zeta23.gammaOf
  rw [Complex.div_I]
  apply Complex.ext <;> simp [hre]

/-- **The easy direction of Weil's criterion**: the Riemann hypothesis implies that the Weil
functional is nonnegative on every positive test function.

Under `ZetaForm` every `ρ` in the critical strip with `ζ(ρ) = 0` has `Re ρ = 1/2`, so its
ordinate `γ_ρ` is real and `h(γ_ρ) ≥ 0` by hypothesis on `k`; the sum over the zeroes
converges absolutely by the explicit formula, so its real part is a sum of nonnegative
reals. -/
theorem weilFunctional_nonneg_of_zetaForm (h : ZetaForm) (k : ℝ → ℂ)
    (hk : IsPositiveTestFunction k) : 0 ≤ (weilFunctional k).re := by
  obtain ⟨hC2, hcs, hpos⟩ := hk
  have hsum := (weil_explicit_formula k hC2 hcs).1
  rw [← weilFunctional_eq_zeroSum k hC2 hcs, Complex.re_tsum hsum]
  refine tsum_nonneg (fun ρ => ?_)
  have hmem : (ρ : ℂ) ∈ nontrivialZeroSet := ρ.2
  have hre : (ρ : ℂ).re = 1 / 2 :=
    (zeta_iff_zeta_strip.mp h) (ρ : ℂ) hmem.2.1 hmem.2.2 hmem.1
  obtain ⟨c, hc, hval⟩ := hpos (ρ : ℂ).im
  rw [zeroOrdinate_eq_ofReal hre, hval]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end RiemannHypothesis

end
