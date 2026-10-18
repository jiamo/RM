# The weighted cosecant inequality and the weighted large sieve, with the constant `5√2/π`

Date: 2026-10-18
Task: `M2-LARGE-SIEVE-WEIGHTED` (new, `DONE_STRONG`)
Modules: `RiemannHypothesis/HilbertCosecantWeighted.lean` (new; imports `HilbertCosecant` and
`LocalSpacingMaximal`), `RiemannHypothesis/LargeSieveWeighted.lean` (new; imports
`HilbertCosecantWeighted` and `LargeSieveMV`). `RiemannHypothesis/LocalSpacingMaximal.lean`
(new in this round) was generalized from `Fin n` to an arbitrary `Fintype` index, so that it
applies to the periodized points; its statements are otherwise unchanged.

## Claim

```lean
theorem weightedCosecantInequality {n : ℕ} (α δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ intDist (α r - α s)) (u : Fin n → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖
      ≤ 5 * Real.sqrt 2 / Real.pi * ∑ r, ‖u r‖ ^ 2 / δ r

theorem weightedCosecantInequality_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t δ : ι → ℝ) (x : ι → ℂ) (hδ : ∀ i ∈ s, 0 < δ i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j)) :
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)‖
      ≤ 5 * Real.sqrt 2 / Real.pi * ∑ i ∈ s, ‖x i‖ ^ 2 / δ i

theorem large_sieve_weighted_dual {ι : Type*} {s : Finset ι} {t δ : ι → ℝ}
    (hδ : ∀ i ∈ s, 0 < δ i) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ‖∑ i ∈ s, x i * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ∑ i ∈ s, ((N : ℝ) + 5 * Real.sqrt 2 / Real.pi / δ i) * ‖x i‖ ^ 2

theorem large_sieve_weighted {ι : Type*} {s : Finset ι} {t δ : ι → ℝ}
    (hδ : ∀ i ∈ s, 0 < δ i) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ((N : ℝ) + 5 * Real.sqrt 2 / Real.pi / δ i)⁻¹
        * ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ∑ n ∈ range N, ‖a n‖ ^ 2
```

(namespaces `RiemannHypothesis.HilbertCosecantWeighted` and
`RiemannHypothesis.LargeSieveWeighted`; `intDist` and `e2pi x = e^{2πix}` are the existing
definitions of `LargeSieve.lean` and `KusminLandau`).

**The constant.** Montgomery and Vaughan (*Hilbert's inequality*, 1974) have `3/2` in both
places. The constant proved is `5√2/π ≈ 2.2508`, the one that follows from `5√2` in
M2-HILBERT-WEIGHTED, about `1.50` times theirs. `3/2` is **not** proved. There is no
hypothesis `δ ≤ 1/2`: for two or more points it follows from `δ_r ≤ intDist ≤ 1/2`, and for one
point the form vanishes.

Mode: a **proof** in this repository. The Brun–Titchmarsh theorem in progressions
`π(x; q, a) ≤ 2x/(φ(q) log(x/q))` that this large sieve feeds is **not** proved.

## The argument

* *Periodization* (`HilbertCosecantWeighted.lean`, first half). The points `α_t + m`,
  `t ∈ Fin n`, `|m| ≤ M`, carry the spacings `δ_t` (`perLam_sep`; for `t ≠ t'` by
  `intDist ≥ δ_t`, for `t = t'` because `|m − m'| ≥ 1 ≥ δ_t`). The line bounds of
  `LocalSpacingMaximal.lean`, applied to them as a family indexed by a finite subset of
  `Fin n × ℤ`, and the expansion `π² csc² πx = ∑_m (x + m)⁻²` (`hasSum_inv_sq_int`, round 2)
  give `δ_s ∑_r δ_r csc² π(α_r − α_s) ≤ 6/π²` (`delta_mul_sum_delta_cscSq_le`; every finite part of
  the series is a sub-sum of a line configuration, `sum_hasSum_le_of_window`) and
  `∑_{s≠t} a_s a_t δ_s^{3/2} δ_t^{1/2} csc² π(α_s − α_t) ≤ (2√120/π²) ∑ a_t²`
  (`sum_sum_cscSq_le`). For the bilinear bound the window of radius `M = K + N` contains, for
  each of the `2N + 1` centres `j` with `|j| ≤ N`, all shifts `|k| ≤ K`, so
  `(2N + 1) X_K ≤ 2√120 (2M + 1) ∑ a²` (`sum_sum_window_le`); letting `N → ∞` gives
  `X_K ≤ 2√120 ∑ a²` for every `K`.
* *Eigenvector argument* (second half), as in `MontgomeryVaughanWeighted.lean` with
  `B r s = √δ_r √δ_s csc π(α_r − α_s)`: `sum_delta_csc_mul_csc` (the identity
  `csc a csc b = csc(b − a)(cot a − cot b)` of round 2 with weights) and `wcsc_eigen_identity`
  cancel the cotangent column sums; `|csc cot| ≤ csc²` and the two bounds above give
  `μ² ≤ (6 + 4√120)/π² < 50/π²` (`wcsc_eigenvalue_sq_le`); the spectral theorem for `iB` and
  Cauchy–Schwarz give `weightedCosecantInequality`; `weightedCosecantInequality_finset` reindexes.
* *Large sieve* (`LargeSieveWeighted.lean`), by the route of `large_sieve_mv`: expanding the
  square, the diagonal is `N ∑ ‖x_i‖²` and the off-diagonal part is `(H(v) − H(w))/(2i)`
  (`kernel_mul_two_I_sin`), each bounded by `(5√2/π) ∑ ‖x_i‖²/δ_i`; this is
  `large_sieve_weighted_dual`. The duality principle `sum_normSq_adjoint_le` with constant `1`,
  applied to `(N + (5√2/π)/δ_i)^{−1/2} conj e(n t_i)`, gives `large_sieve_weighted`.

## Hypothesis hygiene

No new `def … : Prop`; no theorem takes an unproved `Prop` as a hypothesis.
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M2-LARGE-SIEVE-WEIGHTED

* *Constants, by hand.* `(6 + 4√120)/π² ≈ 49.82/9.8696 ≈ 5.048 < 50/π² ≈ 5.066`;
  `√(50/π²) = 5√2/π ≈ 2.2508`; `3/2 = (3π/2)/π`, so the ratio to Montgomery–Vaughan is again
  `5√2/(3π/2) ≈ 1.5006`. The expansion checked at `x = 1/2`: `∑_m (1/2 + m)⁻² = π²`
  (round 2), so for two points `α = (0, 1/2)`, `δ = (1/2, 1/2)` the column bound reads
  `δ_s δ_r csc²(π/2) = 1/4 ≤ 6/π² ≈ 0.608`.
* *Non-triviality.* Cosecant: `n = 2`, `α = (0, 1/2)`, `δ = (1/2, 1/2)`, `u = (1, i)`: the form is
  `2i`, norm `2`, against `2.2508 · (2 + 2) ≈ 9.0`. Large sieve: one point, `N` coefficients
  `a_n = 1`: left side `(N + 2.2508/δ)⁻¹ N²`, right side `N`, consistent; with uniform
  `δ_i = δ` the theorem reads `∑_i |S(t_i)|² ≤ (N + 2.2508 δ⁻¹) ∑ |a_n|²`, weaker than
  `large_sieve_mv` (`N + δ⁻¹`), as expected.
* *Vacuity.* The hypotheses hold for `t_i = i/R`, `δ_i = 1/R`, and for Farey points `a/q` with
  `δ_{a/q} = 1/(qQ)` (the application Montgomery and Vaughan make).
* *Load-bearing.* Without the spacing hypothesis two equal points give an unbounded cosecant
  form (`α = (0, ε)`, norm `2/sin πε`); `0 < δ_i` is needed for `/δ_i`.
* *Claim mode.* A proof in this repository, with `5√2/π`, not `3/2`.
* *Statement pinning.* `scripts/revalidation.lean` writes out the four statements above and the
  periodized bound `sum_sum_cscSq_le` in full and supplies the repository's declarations as proof
  terms; axioms pinned in step 3 of `scripts/audit.sh`.

## Not proved

* Montgomery and Vaughan's constant `3/2`.
* The Brun–Titchmarsh theorem in progressions `π(x; q, a) ≤ 2x/(φ(q) log(x/q))`.
* The large sieve for Dirichlet polynomials at well-spaced real points (M2-MEANVALUE).

## Commands and gates

See `docs/goal/evidence/2026-10-18-m2-meanvalue-weighted.md`, § "Commands and gates".
