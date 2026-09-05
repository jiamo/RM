# M2-MEANVALUE-MV — the mean value theorem with the error term inside the sum

Date: 2026-08-29
File: `RiemannHypothesis/GaussianMeanValue.lean`

## Claim

`RiemannHypothesis/DirichletPolyMeanValue.lean` proves the elementary mean value theorem for a
Dirichlet polynomial `D(s) = ∑_{1 ≤ n ≤ N} a n · n^{−s}`,

`∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^{−2σ}`,

whose error term sits *outside* the sum.  The Carlson–Ingham density argument needs the
Montgomery–Vaughan shape, with the error term *inside* it.  That is what is proved here:

```lean
theorem integral_normSq_dirichletPoly_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)

theorem integral_Icc_normSq_dirichletPoly_le_mv (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)
```

## Proof

The route is the Gaussian majorant, not Montgomery and Vaughan's generalized Hilbert inequality.

1. *The Gaussian oscillatory integral.*  `integral_exp_mul_I_gaussian` evaluates
   `∫_ℝ exp (i θ t) exp (−b t²) dt = √(π/b) exp (−θ²/(4b))` from mathlib's
   `fourierIntegral_gaussian`.

2. *The weighted mean square as a bilinear form.*  Expanding the square with the repository's
   `normSq_dirichletPoly_eq` and integrating term by term,
   `integral_normSq_dirichletPoly_gaussian_le` gives

   `∫_ℝ ‖D(σ + i t)‖² e^{−b t²} dt ≤ √(π/b) ∑_{m, n ≤ N} c_m c_n exp (−(log n − log m)²/(4b))`,

   where `c_m = ‖a m‖ m^{−σ}`.

3. *The row sums of the kernel.*  With `L² = 1/(4b)`, `sum_exp_neg_sq_log_sub_le` bounds
   `∑_{n ≤ N} exp (−L² (log n − log m)²)` by `1 + 6 m / L` for `L ≥ 3`, splitting at `n = 2m`:

   * near the diagonal, `abs_log_sub_log_ge` (`|y − x| / max x y ≤ |log y − log x|`) turns the
     logarithmic separation into the integer separation `|n − m| / (2m)`, and the integral test
     `sum_Icc_exp_neg_mul_sq_le` sums the resulting Gaussian in `Nat.dist n m` to
     `1 + 2 √π m / L`;
   * far from it, `exp_neg_sq_log_sub_le_far` dominates the kernel by `(m²/n²) C` with
     `C = exp (−(L² (log 2)² − 2 log 2))`, and `exp_far_const_bound` gives `C ≤ 4/L`; with
     `∑_{n > 2m} 1/n² ≤ 1/(2m)` this contributes `2 m / L`.

4. *Schur's test.*  The kernel is symmetric, so `2 c_m c_n ≤ c_m² + c_n²` and
   `bilinear_gaussian_kernel_le` bound the bilinear form by `∑_m c_m² (1 + 6 m / L)`.

5. *Removing the weight.*  Taking `b = 1/T²`, so `L = T/2 ≥ 3` for `T ≥ 6`, one has
   `1 ≤ e · e^{−b t²}` on `[−T, T]`, hence
   `∫_{−T}^{T} ‖D‖² ≤ e ∫_ℝ ‖D‖² e^{−b t²} ≤ e √π ∑_m c_m² (T + 12 m)`.  Since `T + 12 m ≤
   12 (T + m)` and `12 e √π < 58`, this is the stated bound; the `[0, T]` form follows because
   the integrand is nonnegative.

## Scope

* The constant `58` is not sharp.  Montgomery and Vaughan's theorem has the asymptotically
  optimal main term, `∑ ‖a n‖² n^{−2σ} (T + O(n))` with constant `1 + o(1)`.  The losses here
  are the majorant `e · exp(−t²/T²)` for the indicator of `[−T, T]` and the crude row-sum count
  `1 + 6 m / L`; only the *shape* of the error term is claimed.
* The statement is about Dirichlet polynomials, not about `ζ`: no approximation of `ζ` in the
  strip is used or proved here, so **no zero-density estimate follows** and no zero of `ζ` is
  located.

## Gates

* `lake build RiemannHypothesis.GaussianMeanValue` succeeds; the module contains no `sorry` and
  is imported by the root `RiemannHypothesis.lean`.
* `#print axioms` on the results gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
