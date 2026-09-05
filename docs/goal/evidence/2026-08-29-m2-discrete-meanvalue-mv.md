# M2-DISCRETE-MEANVALUE-MV — the discrete bound with the error term inside the sum

Date: 2026-08-29
File: `RiemannHypothesis/GaussianMeanValueDiscrete.lean`

## Claim

`RiemannHypothesis/GallagherDiscrete.lean` bounds `∑_i ‖D(σ + i t_i)‖²` over `δ`-separated
points by combining Gallagher's Sobolev lemma with the *elementary* mean value theorem, and so
carries the error term `8 N (1 + log N)` outside the sum.  Replacing that input by the
Montgomery–Vaughan shape of M2-MEANVALUE-MV moves the error term inside the sum:

```lean
theorem sum_normSq_dirichletPoly_at_separated_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 6 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)

theorem card_le_of_dirichletPoly_large_separated_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ} (hδ : 0 < δ) (hT : 6 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)) / V ^ 2
```

## Proof

Gallagher's lemma gives

`δ ∑_i ‖D(σ + i t_i)‖² ≤ 2 ∫₀ᵀ ‖D‖² + δ² ∫₀ᵀ ‖D'‖²`,

and `hasDerivAt_dirichletPoly_line` identifies `D'` along the line with `−i` times the Dirichlet
polynomial with coefficients `a n log n`.  Both integrals are then estimated by
`integral_Icc_normSq_dirichletPoly_le_mv`; for the second one
`sum_normSq_logCoeff_weighted_le` transfers the pointwise comparison
`‖a n log n‖² ≤ (log N)² ‖a n‖²` to the `(T + n)`-weighted mean-square weight.  Dividing by `δ`
gives the stated bound, and Chebyshev (`R V² ≤ ∑_i ‖D(σ + i t_i)‖²`) gives the counting form.

## Scope

* The constant `58` is inherited from `integral_normSq_dirichletPoly_le_mv` and is not sharp,
  and the Sobolev step still costs the factor `2/δ + δ (log N)²` of the elementary Gallagher
  inequality.  Only the shape of the error term is improved.
* The statement is about Dirichlet polynomials, not about `ζ`: no approximation of `ζ` in the
  strip is used or proved here, so **no zero-density estimate follows** and no zero of `ζ` is
  located.

## Gates

* `lake build RiemannHypothesis.GaussianMeanValueDiscrete` succeeds; the module contains no
  `sorry` and is imported by the root `RiemannHypothesis.lean`.
* `#print axioms` on the results gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
