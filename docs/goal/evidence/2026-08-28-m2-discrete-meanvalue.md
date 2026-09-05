# M2-DISCRETE-MEANVALUE — Gallagher's lemma and the discrete mean value theorem

Date: 2026-08-28
File: `RiemannHypothesis/GallagherDiscrete.lean`

## Claim

`RiemannHypothesis/DirichletPolyMeanValue.lean` bounds the *continuous* mean square of a
Dirichlet polynomial `D(s) = ∑_{1 ≤ n ≤ N} a n n^{−s}`.  The large-values machinery of
M2-LARGE-VALUES needs instead a bound for the *discrete* sum `∑_r ‖D(σ + i t_r)‖²` over
`δ`-separated points.  The bridge is Gallagher's Sobolev-type lemma, proved here for an arbitrary
continuously differentiable `f : ℝ → ℂ`:

```lean
theorem Gallagher.sum_normSq_le_of_separated {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ)
    (hAB : A ≤ B) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ 2 * (∫ x in A..B, ‖f x‖ ^ 2) + δ ^ 2 * ∫ x in A..B, ‖f' x‖ ^ 2
```

Specialized to a Dirichlet polynomial — whose derivative along a vertical line is again a
Dirichlet polynomial, with coefficients `a n log n` — this gives the discrete mean value theorem
and its large-values consequence:

```lean
theorem hasDerivAt_dirichletPoly_line (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I))
      (-I * dirichletPoly (logCoeff a) N ((σ : ℂ) + (t : ℂ) * I)) t

theorem sum_normSq_dirichletPoly_at_separated_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)

theorem card_le_of_dirichletPoly_large_separated (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / V ^ 2
```

## Proof

1. *The derivative of the square modulus.*  `hasDerivAt_normSq_comp` differentiates
   `x ↦ ‖f x‖² = (Re f)² + (Im f)²` to `2 Re(conj (f x) · f' x)`, and
   `abs_two_mul_re_conj_mul_le` bounds this by `2 ‖f x‖ ‖f' x‖` (`|Re z| ≤ ‖z‖` applied to
   `conj (f x) f' x`).
2. *One interval.*  For `c ∈ [u, v]` the fundamental theorem of calculus gives
   `‖f c‖² − ‖f x‖² = ∫_x^c (‖f‖²)'`, whose absolute value is at most
   `J := ∫_u^v |(‖f‖²)'| ≤ ∫_u^v 2 ‖f‖ ‖f'‖` for every `x ∈ [u, v]`.  Integrating the resulting
   inequality `‖f c‖² ≤ ‖f x‖² + J` over `x ∈ [u, v]` gives
   `(v−u) ‖f c‖² ≤ ∫_u^v ‖f‖² + (v−u) J` (`mul_normSq_le_integral_of_mem_Icc`).  The elementary
   inequality `2 x y ≤ δ⁻¹ x² + δ y²` with `δ = v − u` then removes the cross term, at the price
   of the constant `2`:
   `(v−u) ‖f c‖² ≤ 2 ∫_u^v ‖f‖² + (v−u)² ∫_u^v ‖f'‖²`.
3. *Summing.*  The windows `Ioc (t_i − δ/2, t_i + δ/2)` around `δ`-separated points are pairwise
   disjoint and contained in `Ioc A B`, so `∑_i ∫_{window i} h ≤ ∫_A^B h` for any continuous
   `h ≥ 0` (`sum_integral_window_le`, via `integral_biUnion_finset` and `setIntegral_mono_set`).
   Adding the one-interval bounds over `i` gives Gallagher's lemma.
4. *Dirichlet polynomials.*  `d/dt n^{−(σ+it)} = −i log n · n^{−(σ+it)}`, so the derivative of
   `t ↦ D(σ+it)` is `−i` times the Dirichlet polynomial with coefficients `a n log n`; since
   `0 ≤ log n ≤ log N` for `1 ≤ n ≤ N`, its mean-square weight is at most `(log N)²` times that
   of `a`.  Feeding the continuous mean value theorem
   `∫₀ᵀ ‖D‖² ≤ (T + 8 N (1 + log N)) ∑ ‖a n‖² n^{−2σ}` into Gallagher's lemma and dividing by `δ`
   gives the discrete bound; Chebyshev (`R V² ≤ ∑_i ‖D(σ+it_i)‖²`) gives the counting form.

## Scope

* The error term inherits the factor `N log N` of the repository's elementary continuous mean
  value theorem rather than the `N` of the Montgomery–Vaughan theorem, and the Sobolev step
  contributes the extra factor `2/δ + δ (log N)²` instead of the sharper
  `δ⁻¹ + (log N) · (Cauchy–Schwarz cross term)` of the classical Gallagher inequality.  Both
  losses are logarithmic.
* The bound is about Dirichlet polynomials, not about `ζ`: no approximation of `ζ` in the strip
  is used or proved here, and consequently **no zero-density estimate** follows and no zero of
  `ζ` is located.

## Gates

* `lake build RiemannHypothesis.GallagherDiscrete` succeeds; the module contains no `sorry` and
  is imported by the root `RiemannHypothesis.lean`.
* `#print axioms` on the results gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
