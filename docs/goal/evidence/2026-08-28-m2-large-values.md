# M2-LARGE-VALUES — the Halász–Montgomery large-values estimate for Dirichlet polynomials

Date: 2026-08-28
File: `RiemannHypothesis/HalaszMontgomery.lean`

## Claim

The Halász–Montgomery inequality, in a complex inner product space:

```lean
theorem halasz_montgomery {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (φ : ι → E) (ξ : E) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖⟪φ i, φ j⟫_ℂ‖ ≤ Δ) :
    ∑ i ∈ s, ‖⟪φ i, ξ⟫_ℂ‖ ^ 2 ≤ Δ * ‖ξ‖ ^ 2
```

specialized to the vectors `n ↦ n^{i t}` that produce the values of a Dirichlet polynomial:

```lean
theorem sum_normSq_dirichletPoly_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ℕ → ℂ) (N : ℕ)
    {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s,
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ ≤ Δ) :
    ∑ i ∈ s, ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖ ^ 2
      ≤ Δ * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2

theorem card_le_of_dirichletPoly_large {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ℕ → ℂ) (N : ℕ)
    {Δ V : ℝ} (hΔ0 : 0 ≤ Δ) (hV : 0 < V)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s,
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ ≤ Δ)
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((t i : ℂ) * Complex.I)‖) :
    (s.card : ℝ) ≤ Δ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / V ^ 2
```

The second is the large-values counting statement `R ≤ Δ ‖a‖² / V²`: the number of well-separated
points at which a Dirichlet polynomial of length `N` is at least `V` in modulus is bounded by the
Gram row-sum bound `Δ` divided by `V²`.

## Proof

The engine is the coordinate form `sum_normSq_le_of_rowSum_le` (duality + Cauchy–Schwarz + the
Gram row-sum bound); `halasz_montgomery` is the same argument written in an inner product space,
`sum_normSq_dirichletPoly_le` is its specialization, and `card_le_of_dirichletPoly_large` follows
by bounding the left side below by `R V²`.  The identification of the Gram entries uses
`conj_cpow_I_mul` (`conj (n^{i u}) = n^{−i u}` for `n ≥ 1`) and `conj_cpow_mul_cpow`.

## The ceiling

`exists_sharp_rowSum` exhibits the orthonormal configuration `φ i n = [i = n]`, `ξ n = V`: the
Gram row sums are all `1`, every value has modulus exactly `V`, and `∑_n ‖ξ n‖² = R V²`, so the
inequality is an *equality* at `Δ = 1`.  Hence `largeValues_constant_ge_one`: if a constant `c`
makes `R ≤ c Δ ‖ξ‖²/V²` valid for every configuration with Gram row sums at most `Δ`, then
`c ≥ 1`.  The constant of the large-values estimate is therefore already optimal, and any
improvement to the count has to come from extra information about the vectors — which is exactly
what the modern large-values estimates supply, and what this file does not.

## Scope

What is proved is the *reduction*: the large-values count is bounded in terms of the Gram row-sum
bound `Δ`, which is left as a hypothesis.  The two classical ways of supplying `Δ` are not
formalized here as a single packaged estimate:

* the mean-value route `Δ ≪ T + N log N`, whose ingredient
  `integral_normSq_dirichletPoly_mvt_zero` is in `RiemannHypothesis/DirichletPolyMeanValue.lean`,
  is a bound for an *integral*, and converting it into a bound over discrete separated points
  needs a Sobolev/Gallagher-type step that is not in the repository;
* the large sieve route, for exponential polynomials rather than Dirichlet polynomials, is
  M2-LARGE-SIEVE.

Consequently no numerical large-values theorem of the form `R ≪ (T + N) N V^{−2} + T N^{...}` is
claimed, and no zero-density estimate follows from this module.

## Gates

* `lake build RiemannHypothesis.HalaszMontgomery` succeeds; the module contains no `sorry` and is
  imported by the root `RiemannHypothesis.lean`.
* `#print axioms` gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
