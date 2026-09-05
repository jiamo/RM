# M2-LARGE-SIEVE — the large sieve inequality for exponential polynomials

Date: 2026-08-28
Files: `RiemannHypothesis/HalaszMontgomery.lean`, `RiemannHypothesis/LargeSieve.lean`

## Claim

For points `t i` that are pairwise `δ`-separated modulo one, the values of an exponential
polynomial of length `N` at those points are controlled by its coefficients:

```lean
theorem large_sieve {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹))) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2
```

Here `intDist θ = |θ − round θ|` is the distance to the nearest integer, written `‖θ‖` in the
literature, and `e2pi θ = exp(2 π i θ)`.

The counting form is recorded in the same file:

```lean
theorem card_le_of_large_values {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ V : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ i ∈ s, V ≤ ‖∑ n ∈ Finset.range N, a n * e2pi ((n : ℝ) * t i)‖) :
    (s.card : ℝ) ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)))
      * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) / V ^ 2
```

## Proof

The inequality is an instance of the Halász–Montgomery / Schur bound proved in
`RiemannHypothesis/HalaszMontgomery.lean`:

```lean
theorem sum_normSq_le_of_rowSum_le {ι κ : Type*} (s : Finset ι) (m : Finset κ)
    (φ : ι → κ → ℂ) (ξ : κ → ℂ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * φ j n‖ ≤ Δ) :
    ∑ i ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * ξ n‖ ^ 2 ≤ Δ * ∑ n ∈ m, ‖ξ n‖ ^ 2
```

(the duality argument: write `Q = ∑_i |⟨φ i, ξ⟩|²` as `∑_n ξ n B n`, apply Cauchy–Schwarz, and
bound `∑_n |B n|²` by `Δ Q` using the Gram row sums).  Its inner-product-space form is
`halasz_montgomery`.

Applied with `φ i n = e(−n t i)`, the Gram matrix is the Dirichlet kernel
`kernel N θ = ∑_{n < N} e(n θ)` evaluated at `t i − t j`, so what is needed is a row-sum bound
`∑_j ‖kernel N (t i − t j)‖ ≤ Δ`.  That is `sum_norm_kernel_row_le`, and it comes from

* `norm_kernel_le_card`: the diagonal term contributes `N`;
* `norm_kernel_le_inv_intDist`: `‖kernel N θ‖ ≤ 1/(2 ‖θ‖)`, via the geometric sum and
  `two_mul_intDist_le_abs_sin` (Jordan's inequality `2‖θ‖ ≤ |sin(π θ)|`, obtained from
  `Real.mul_le_sin` and `Real.sin_add_int_mul_pi`);
* a bucket argument: with `K = ⌊(2δ)⁻¹⌋₊`, the map `j ↦ (sign, ⌈‖t i − t j‖/δ⌉)` into
  `Bool ×ˢ Icc 1 K` is injective on the separated points, so the off-diagonal row sum is at most
  `δ⁻¹ ∑_{k ≤ K} 1/k ≤ δ⁻¹ (1 + log K)`, using the repository's `sum_inv_Icc_le`.

## The ceiling

The same file records how much room is left, in the style of `MethodCeiling.lean`.  Call
`C : ℝ → ℕ → ℝ` an *admissible* large-sieve constant (`AdmissibleConstant`) if the inequality with
constant `C δ N` holds for every family of `δ`-separated points and every coefficient vector of
length `N`.  Two configurations bound any such `C` from below:

* one point with all coefficients equal to `1`: `‖∑_{n<N} a_n‖² = N²` against `∑_n ‖a_n‖² = N`,
  so `C δ N ≥ N` (`length_le_of_admissibleConstant`);
* the `⌊(2δ)⁻¹⌋ + 1` points `0, δ, 2δ, …`, which are `δ`-separated modulo one
  (`intDist_eq_abs_of_abs_le_half`), with the coefficient vector supported at `n = 0`: every value
  is `1`, so `C δ N ≥ ⌊(2δ)⁻¹⌋ + 1` (`separation_le_of_admissibleConstant`).

Together (`le_of_admissibleConstant`): `max N (2δ)⁻¹ ≤ C δ N`.  So neither term of the constant
can be removed, and the constant proved here is within a factor `O(1 + log (2δ)⁻¹)` of the best
possible one — the logarithm is the only thing that is open.

## Scope

The constant obtained is `N + δ⁻¹(1 + log (2δ)⁻¹)`, not the sharp `N + δ⁻¹` of Montgomery–Vaughan
and Selberg: the logarithmic factor is the cost of the elementary Schur test used here, and
removing it needs Selberg's majorant construction, which is not formalized.  No consequence for
`ζ` is drawn in these modules: no mean-value theorem for `ζ` is improved, and no density estimate
follows.

## Gates

* `lake build RiemannHypothesis.LargeSieve` and `lake build RiemannHypothesis.HalaszMontgomery`
  succeed; both modules contain no `sorry` and both are imported by the root
  `RiemannHypothesis.lean`.
* `#print axioms` on `large_sieve`, `halasz_montgomery` and the derived estimates gives exactly
  `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
