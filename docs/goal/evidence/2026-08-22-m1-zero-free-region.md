# M1-ZERO-FREE-REGION — the de la Vallée Poussin region, exponent one

Date: 2026-08-22
Modules: `RiemannHypothesis/DirichletSeriesBounds.lean`, `RiemannHypothesis/ZeroFreeClassical.lean`
(both imported by `RiemannHypothesis.lean`)

## What is proved

`RiemannHypothesis.zeroFreeRegion : ZeroFreeRegion`, i.e.

```
∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0
```

This is the classical exponent-one region.  The row was previously `DONE_WEAK`: only the
exponent-nine region `RiemannHypothesis.zeroFreeRegionNinth` (M1-ZERO-FREE-REGION-NINTH) had
been proved, by an elementary Cauchy-estimate transfer that loses several powers of `log`.

### The Dirichlet-series input (`DirichletSeriesBounds.lean`)

* `summable_rpow_neg`, `summable_log_mul_rpow_neg`, `summable_vonMangoldt_rpow_neg`,
  `summable_vonMangoldt_rpow_neg_cos` — the summability facts for `σ > 1`.
* `zetaSeries_le` / `le_zetaSeries` — `1/(σ-1) ≤ Σ n^{-σ} ≤ 1/(σ-1) + 1`, by comparison with
  `∫₁^∞ x^{-σ} dx` (`AntitoneOn.integral_le_sum` / `sum_le_integral`).
* `negReLogDerivZeta s := (-(ζ'(s)/ζ(s))).re`, with `negReLogDerivZeta_eq_tsum`
  (`= Σ Λ(n) n^{-σ} cos(t log n)` for `σ > 1`) and `negReLogDerivZeta_real_eq`
  (`= (Σ log n · n^{-σ}) / (Σ n^{-σ})` on the real axis).
* `logSeries_le` — `Σ log n · n^{-σ} ≤ (ζ(σ-a) - ζ(σ))/a` for `0 < a < σ-1`, from the elementary
  `log x ≤ (x^a - 1)/a`.
* `negReLogDerivZeta_real_le` — **the sharp real-axis bound**
  `-ζ'/ζ(σ) ≤ 1/(σ - 1 - a) + (σ - 1)/a` for every `0 < a < σ - 1`.  Taking `a = θ(σ-1)` with
  `θ` small makes the leading constant `1/(1-θ)`, i.e. as close to `1` as required; the
  crude bound `1/(σ-1) + O(1)` would not suffice, because the 3-4-1 argument needs a constant
  strictly below `4/3` after the `3 : 4` weighting.
* `three_four_one` — Mertens' inequality
  `0 ≤ 3·f(σ) + 4·f(σ+it) + f(σ+2it)` for `σ > 1`, from `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`
  applied term by term to the `Λ` Dirichlet series.

### The Hadamard input (`ZeroFreeClassical.lean`)

Via the vendored `Zeta23` library, which supplies the Hadamard expansion
`Re ξ'/ξ(s) = Σ_ρ m_ρ (σ - β_ρ)/|s - ρ|²` (`re_logDeriv_xi_eq_tsum`, with absolute convergence),
the identity `ζ'/ζ + L₂ = ξ'/ξ - L₋`, the Stirling bound `‖ψ(z) - log z‖ ≤ 4`, and
`|Re L₋| ≤ C/t²`.

* `re_L2_le` — the upper companion of `Zeta23`'s `re_L2_ge`:
  `Re L₂(s) ≤ ½ log|t| + C` for `1 ≤ σ ≤ 2`, `|t| ≥ 4`.  For the second digamma factor
  `ψ((1-s)/2)`, whose argument has non-positive real part, the functional equation is used to
  shift by one before applying Stirling.
* `negReLogDerivZeta_le` — `-ζ'/ζ(s) ≤ ½ log|t| + C` (all zero terms dropped; each is `≥ 0`).
* `negReLogDerivZeta_le_of_zero` — `-ζ'/ζ(s) ≤ ½ log|t| + C - 1/(σ - β)` when `ρ = β + it` is a
  nontrivial zero at the same height, keeping exactly that one term of the Hadamard sum
  (`normSq(s - ρ) = (σ - β)²` there, and the multiplicity is `≥ 1`).

### The endgame

`exists_re_le_one_sub_of_nontrivialZero` — there is `t₀` with `β ≤ 1 - (1/125)/log|γ|` for every
nontrivial zero `ρ = β + iγ` with `|γ| ≥ t₀`.  At `σ = 1 + 1/(10 L)`, `L = log|γ|`, with
`a = (σ-1)/10` in the real-axis bound, the three inequalities give

```
4/(σ - β) ≤ (215/6)·L + K   with K = 30 + 4C + C' + (log 2)/2 + 1,
```

and for `L ≥ K` this is `≤ (221/6)·L`, whence `σ - β ≥ 24/(221 L)` and
`β ≤ 1 + 1/(10L) - 24/(221L) = 1 - (19/2210)/L ≤ 1 - (1/125)/L`.

`zeroFreeRegion` then assembles the three ranges: `Re s ≥ 1` is Mathlib's
`riemannZeta_ne_zero_of_one_le_re`; `Re s ≤ 0` is excluded by taking `c ≤ (log 3)/2 < log 3`;
the zeros with `3 ≤ |γ| ≤ t₀` form a finite set (`Zeta23`'s `finite_absWindow`), so
`ε := min_ρ (1 - β_ρ) > 0` and `c ≤ ε·log 3` handles them.  The constant taken is
`c = min (min (1/125) (ε·log 3)) ((log 3)/2)`.

## Scope and honesty about the constant

* `c` is **not effective**: `t₀ = max 4 (exp K)` depends on the constants `C`, `C'` coming from
  the vendored Stirling / `L₋` estimates, which are existentially quantified there, and `ε`
  depends on the finitely many low-lying zeros.  What is explicit is the exponent (one) and the
  constant `1/125` that the analytic argument yields above the height `t₀`.
* No claim is made about the Vinogradov–Korobov region, nor about any zero-density estimate.
* The Riemann Hypothesis itself is not claimed anywhere.

## Gates

* `lake build` — succeeds (9078 jobs), no `sorry` in `RiemannHypothesis/`.
* `./scripts/audit.sh` — `OK`; the new claims are pinned in `scripts/revalidation.lean`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-ZERO-FREE-REGION

A second pass, made against the compiled modules rather than against this note.

* **Is the statement the intended one?**  `ZeroFreeRegion` is the pre-existing definition in
  `RiemannHypothesis/Partial.lean`, unchanged by this work; `scripts/revalidation.lean` pins both
  its unfolding and the term `RiemannHypothesis.zeroFreeRegion` inhabiting it, so a later
  weakening stops that file elaborating.
* **Is it vacuous?**  No.  The hypotheses `3 ≤ |Im s|` and `1 - c/log|Im s| < Re s` are satisfied
  by, for example, every `s` with `Re s = 1` and `Im s = 3`; and the conclusion is a genuine
  non-vanishing statement, strictly stronger than the exponent-nine
  `zeroFreeRegionNinth` for large `|Im s|` (`c/L` beats `2^{-45}/L⁹`).
* **Is the analytic chain sound, or does it lean on something circular?**  The three ingredients
  are independent of any zero-free information: the 3-4-1 inequality is a pointwise trigonometric
  identity summed over the `Λ` series in `σ > 1`; the real-axis bound is an integral comparison;
  the Hadamard bound comes from `Zeta23`'s explicit-formula development, which is proved from the
  argument principle and Stirling, not from a zero-free region.
* **Is the constant honestly reported?**  Yes — see "Scope" above.  The statement being closed is
  the existential `ZeroFreeRegion`, which does not ask for effectivity, and the exit criteria have
  been restated to record that `t₀` is not explicit.
* **Do the small heights really get handled?**  `3 ≤ |Im s| < t₀` is covered by the finiteness of
  the set of nontrivial zeros of bounded ordinate; the minimum `ε` of `1 - β` over that finite
  set is positive because every nontrivial zero has `β < 1`.  The empty case is handled
  separately (any `ε` works).
* **Proof hygiene.**  No `sorry`, `axiom`, `native_decide` or `implemented_by` in either new
  module; `#print axioms` on each exported theorem returns exactly `propext`, `Classical.choice`,
  `Quot.sound` (checked by `scripts/audit.sh`).
* **What is *not* claimed.**  Nothing effective, nothing about `Re s > 1 - c/(log|t|)^{2/3}`, and
  nothing about the Riemann Hypothesis.
