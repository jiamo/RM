# M2-WEIL-POSITIVITY — the criterion stated, the easy direction proved

Date: 2026-08-22
Module: `RiemannHypothesis/WeilPositivity.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `weilFunctional k` — the right-hand side of the explicit formula
  (`RiemannHypothesis.weil_explicit_formula`, M1-EXPLICIT), written as a definition:
  `h(i/2) + h(−i/2) − ∑ₙ Λ(n) n^{−1/2}(k(log n) + k(−log n)) + (1/2π)∫ h(r)·(Re ψ(1/4+ir/2) − log π) dr`,
  with `h = testTransform k`.
* `weilFunctional_eq_zeroSum` — the explicit formula restated: for `k ∈ C_c²(ℝ)`,
  `∑_ρ m_ρ h(γ_ρ) = weilFunctional k`.
* `IsPositiveTestFunction k` — `k` is `C²`, compactly supported, and `h` is real and
  nonnegative on the real axis.
* `WeilPositivityCriterion` — the criterion as a `Prop`:
  `ZetaForm ↔ ∀ k, IsPositiveTestFunction k → 0 ≤ Re (weilFunctional k)`.
* `zeroOrdinate_eq_ofReal` — a zero with `Re ρ = 1/2` has real ordinate `γ_ρ = Im ρ`.
* `weilFunctional_nonneg_of_zetaForm` — **the forward implication**: `ZetaForm` implies the
  positivity.  Under the Riemann hypothesis every nontrivial zero lies on the critical line, so
  each `γ_ρ` is real, each term `m_ρ h(γ_ρ)` is a nonnegative real, and the sum — absolutely
  convergent by the explicit formula — has nonnegative real part.

## What is *not* proved

* The converse (positivity implies the Riemann hypothesis).  That is the substance of Weil's
  criterion: from a hypothetical zero off the critical line one must build a test function on
  which the form is negative.  No term of type `WeilPositivityCriterion` exists in this
  repository, so the row stays `DONE_WEAK`.
* Non-vacuity of `IsPositiveTestFunction` beyond `k = 0`.  Every convolution square
  `k = k₀ ⋆ k₀^*` belongs to the class, because then `h(r) = |h₀(r)|²` for real `r`; that
  identity (a Fourier convolution theorem for `testTransform`, together with the smoothness and
  support of the convolution) is not formalized here, and no explicit nonzero witness is
  constructed.  Note that the *criterion* is not weakened by using the larger pointwise class:
  quantifying over more test functions only makes the right-hand side of the equivalence
  stronger.

## Gates

* `lake build RiemannHypothesis.WeilPositivity` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.
