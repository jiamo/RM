/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeta23Bridge
import Zeta23.WeilEF.Main
import Zeta23.FromPNTPlus.MediumPNT

/-!
# Perron's formula and the explicit formula

Two of the classical analytic identities behind the prime number theorem and the
distribution of the zeroes, recorded here in this repository's vocabulary.  Both are
supplied by the vendored `Zeta23` library (`vendor/zeta23`, Apache 2.0).

## Perron's formula, smoothed

`smoothedChebyshev ν ε X` is the vertical contour integral

`(1/2πi) ∫_{(σ)} (−ζ'/ζ)(s) · 𝓜[ν_ε](s) · X^s ds`,  `σ = 1 + 1/log X`,

of the logarithmic derivative of `ζ` against the Mellin transform of a smoothing kernel.

* `smoothedChebyshev_eq_vonMangoldt_sum` — the contour integral equals the smoothed
  von Mangoldt sum `∑ₙ Λ(n) ν_ε(n/X)`: Perron's formula;
* `smoothedChebyshev_sub_chebyshevPsi_bound` — the smoothed sum differs from `ψ(X)`
  by at most `C ε X log X`, so it does compute `∑_{n ≤ X} Λ(n)` in the limit `ε → 0`.

## The explicit formula

`weil_explicit_formula` is the Riemann–von Mangoldt / Weil explicit formula in its
test-function form: for `k ∈ C_c²(ℝ)`, writing `h(z) = ∫ k(u) e^{izu} du` and
`γ_ρ = (ρ − 1/2)/i` for the ordinate of a zero,

`∑_ρ m_ρ h(γ_ρ) = h(i/2) + h(−i/2) − ∑_n Λ(n) n^{−1/2} (k(log n) + k(−log n))
                   + (1/2π) ∫_ℝ h(r) [Re ψ(1/4 + ir/2) − log π] dr`,

the sum over the nontrivial zeroes converging absolutely.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology ArithmeticFunction

namespace RiemannHypothesis

/-! ## Perron's formula for the Chebyshev function -/

/-- The integrand of Perron's formula: `(−ζ'/ζ)(s) · 𝓜[ν_ε](s) · X^s`. -/
def perronIntegrand (ν : ℝ → ℝ) (ε X : ℝ) : ℂ → ℂ :=
  SmoothedChebyshevIntegrand ν ε X

/-- The smoothed Chebyshev function, defined as the vertical contour integral of
`(−ζ'/ζ)(s) · 𝓜[ν_ε](s) · X^s` along `Re s = 1 + 1/log X`. -/
def smoothedChebyshev (ν : ℝ → ℝ) (ε X : ℝ) : ℂ := SmoothedChebyshev ν ε X

/-- **Perron's formula** (smoothed): the contour integral of `−ζ'/ζ` against the Mellin
transform of the smoothing kernel equals the smoothed von Mangoldt sum. -/
theorem smoothedChebyshev_eq_vonMangoldt_sum {ν : ℝ → ℝ} (hν : ContDiff ℝ 1 ν)
    (hνpos : ∀ x > 0, 0 ≤ ν x) (hνsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (hνmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (hX : 3 < X) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    smoothedChebyshev ν ε X =
      ((∑' n : ℕ, Λ n * Smooth1 ν ε (n / X) : ℝ) : ℂ) :=
  SmoothedChebyshevDirichlet hν hνpos hνsupp hνmass hX hε hε1

/-- The smoothed Chebyshev function is within `C ε X log X` of `ψ(X)`; letting `ε → 0`
recovers `∑_{n ≤ X} Λ(n)` from the contour integral. -/
theorem smoothedChebyshev_sub_chebyshevPsi_bound {ν : ℝ → ℝ} (hν : ContDiff ℝ 1 ν)
    (hνsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (hνpos : ∀ x > 0, 0 ≤ ν x)
    (hνmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖smoothedChebyshev ν ε X - Chebyshev.psi X‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨C, hC, h⟩ := SmoothedChebyshevClose hν hνsupp hνpos hνmass
  exact ⟨C, hC, fun X hX ε hε hε1 hXε => h X hX ε hε hε1 hXε⟩

/-! ## The Weil / von Mangoldt explicit formula -/

/-- `h(z) = ∫ k(u) e^{izu} du`, the transform of the test function `k` appearing in the
explicit formula. -/
def testTransform (k : ℝ → ℂ) (z : ℂ) : ℂ := Zeta23.paperFT k z

/-- The ordinate `γ_ρ = (ρ − 1/2)/i` of a zero `ρ`. -/
def zeroOrdinate (ρ : ℂ) : ℂ := Zeta23.gammaOf ρ

/-- The archimedean bracket `Re ψ(1/4 + ir/2) − log π` of the explicit formula. -/
def archimedeanBracket (r : ℝ) : ℝ := Zeta23.EF.gammaBracket r

/-- **The explicit formula** (Riemann–von Mangoldt, Weil's test-function form): for every
`k ∈ C_c²(ℝ)`, with `h = testTransform k`,

`∑_ρ m_ρ h(γ_ρ) = h(i/2) + h(−i/2) − ∑_n Λ(n) n^{−1/2}(k(log n) + k(−log n))
   + (1/2π) ∫_ℝ h(r)(Re ψ(1/4 + ir/2) − log π) dr`,

the sum over the nontrivial zeroes being absolutely convergent. -/
theorem weil_explicit_formula (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : nontrivialZeroSet =>
        (zeroMultiplicity ρ : ℂ) * testTransform k (zeroOrdinate ρ)) ∧
      ∑' ρ : nontrivialZeroSet,
          (zeroMultiplicity ρ : ℂ) * testTransform k (zeroOrdinate ρ)
        = testTransform k (I / 2) + testTransform k (-I / 2)
          - ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
          + (1 / (2 * Real.pi) : ℂ) *
              ∫ r : ℝ, testTransform k r * (archimedeanBracket r : ℂ) :=
  Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam k hk hkc

end RiemannHypothesis

end
