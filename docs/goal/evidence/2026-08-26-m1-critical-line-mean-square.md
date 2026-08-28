# M1-CRITICAL-LINE-MEAN-SQUARE — moments of ζ **on** the critical line

Date: 2026-08-26
File: `RiemannHypothesis/CriticalLineMeanSquare.lean`
Related: `RiemannHypothesis/StripMeanSquareBohrLandau.lean` (the Euler–Maclaurin expansion of
arbitrary order and the same argument for `1/2 < σ < 1`),
`RiemannHypothesis/StripMeanSquare.lean` (the off-diagonal estimate `offDiagSum_one_le'`)

## Claim

For every `ε > 0` there is a constant `C > 0` such that for every `T ≥ 1`

    ∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ≤ C · T^(1+ε)      (exists_integral_normSq_riemannZeta_le_critical_line)
    ∫₀ᵀ ‖ζ(1/2 + i t)‖  dt ≤ C · T^(1+ε)      (exists_integral_norm_riemannZeta_le_critical_line)

and the large-values form: for every `V > 0`

    vol {t ∈ (0,T] : ‖ζ(1/2 + i t)‖ ≥ V} ≤ C · T^(1+ε) / V².
                                    (exists_volume_norm_riemannZeta_ge_le_critical_line)

Until now the repository had no moment bound *on* the critical line at all: every earlier row
covered `σ > 1/2` with a constant that blows up as `σ ↓ 1/2`.

## Proof

The same route as `exists_integral_normSq_riemannZeta_le_half`, run at `σ = 1/2`.  Fix `ε` and
choose an order `m` of the Euler–Maclaurin expansion with `2m/(2m−1) ≤ 1 + ε`.  With
`N ≍ T^e`, `e = 2m/(2m−1)`,

* `exists_norm_riemannZeta_sub_dirichletPoly_le_em` bounds `ζ(1/2+it)` by the Dirichlet
  polynomial `∑_{n ≤ N} n^{-1/2-it}` up to an error that is `O(1)` uniformly for `|t| ≤ T`;
* `integral_normSq_dirichletPoly_one_le_half` bounds the mean square of that polynomial by the
  diagonal `∑_{n ≤ N} n^{-1}` plus the off-diagonal sum, which `offDiagSum_one_le'` — restated in
  this pass with the weakened hypothesis `1/2 ≤ σ`, the hypothesis its proof actually uses —
  controls at `σ = 1/2`;
* Cauchy–Schwarz turns the second moment into the first, and Chebyshev turns it into the
  large-values estimate.

## Scope, and what is *not* claimed

* The sharp Hardy–Littlewood asymptotic `∫₀ᵀ ‖ζ(1/2+it)‖² dt ∼ T log T` is **not** claimed.  The
  `T^ε` loss is exactly the loss of the elementary Euler–Maclaurin approximation, which needs a
  Dirichlet polynomial slightly longer than `T`; removing it needs the approximate functional
  equation, which shortens the polynomial to length `√(T/2π)`.
* No fourth moment, and hence no Ingham density estimate, follows from these.
* No zero of `ζ` is located, and RH is neither proved nor disproved.

## Adversarial revalidation: M1-CRITICAL-LINE-MEAN-SQUARE

* The module is imported by `RiemannHypothesis.lean`, `lake build` succeeds, and the file
  contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  results.
* The statements are not vacuous: they quantify over all `T ≥ 1` and give a finite bound; the
  integrand is a genuine `ζ` value on the critical line, not a truncation.
* The statements are unconditional: no unproved `Prop` of this repository occurs as a hypothesis,
  so `docs/goal/conditional-theorems.txt` is unchanged.
* The weakening of `offDiagSum_one_le` to `offDiagSum_one_le'` keeps the original statement in
  place as a one-line corollary, so no existing caller and no statement pin was invalidated.
