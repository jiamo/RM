# 2026-09-24 — M2-GRAM-INERTIA (B1–B4) and the first A1 layer

## What was found before writing anything

The Gram / inertia machinery is **not** absent from the repository: the vendored `Zeta23`
library (`vendor/zeta23/Zeta23/LinAlg/*`, `Zeta23/ZeroSide.lean`, `Zeta23/Assembly.lean`)
already proves, in namespace `RHLinalg` / `Zeta23.ZeroSide`:

| item | vendored declaration |
|---|---|
| positive index, variational description | `posIndex`, `posIndex_eq_max_finrank_posDefOn` |
| inertia under pull-back (one direction) | `posIndex_conj_le` |
| subadditivity | `posIndex_add_le` |
| von Neumann, Hermitian | `vonNeumann_trace_ineq` |
| rank–trace inequality | `rank_trace_ineq`, `rank_trace_ineq_two` |
| block structure `A = P + Q`, `n₊(Q) ≤ p` | `ZeroBlockData`, `posIndex_blockQ_le` |

What was missing was (i) the *equality* form of Sylvester's law (Mathlib has only the existence of
a signed diagonal form, `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`), (ii) any
connection of the block structure to this repository's `criticalReflect`, and (iii) a statement of
the certificate that takes the two prime-side estimates as inputs and returns the proportion. That
is what `RiemannHypothesis/GramInertia.lean` supplies.

## Statements (all in `RiemannHypothesis.GramInertia`)

* **B1** `posIndex_conj_eq`, `negIndex_conj_eq`, `rank_conj_eq`, `posIndex_add_negIndex`.
* **B2** `norm_trace_mul_le_of_posSemidef` : `‖tr(AB)‖ ≤ Σ aᵢ bᵢ` for `A, B ⪰ 0`.
* **B3** `ReflectionConfig`, `ReflectionConfig.gram`, `gram_isHermitian`, `posIndex_gram_le`
  (`n₊(A) ≤ #on-line + #{Re ρ > 1/2}`), `two_mul_posIndex_gram_le`, `card_offLine_eq_two_mul`,
  `card_eq`, `rank_gram_le`.
* **B4** `inertia_certificate`, `inertia_certificate_ratio`, `certificate_eventually_of_bounds`,
  `ReflectionConfig.gram_certificate`, `ReflectionConfig.gram_certificate_ratio`,
  `GramFamily.certificate_eventually`, `GramFamily.certificate_Hfun_eventually`,
  `GramFamily.two_thirds_eventually`.

The certificate in words: if `tr Â = N(1 + o(1))` and `‖Â‖_F² ≤ (1/λ + λ/3) N (1 + o(1))`, and the
diagonal (Poisson) bound holds at on-line points, then the number of *distinct* on-line points is
at least `(2 − 1/λ − λ/3 − ε) N` eventually, with `N` counting all points *with multiplicity*; at
`λ = 1` this is `2/3 − ε`. No hypothesis about the location of the points is made; the only
structural input is stability under `ρ ↦ 1 − ρ̄`.

## A1 (first layer)

`RiemannHypothesis/PaleyWienerEasy.lean`: for `g ∈ L¹[-τ, τ]`, `F(z) = ∫_{-τ}^{τ} g(t) e^{izt} dt`
is entire (`bandLimited_differentiable`), satisfies `|F(z)| ≤ ‖g‖₁ e^{τ|z|}`
(`norm_bandLimited_le`), hence has exponential type at most `τ`
(`bandLimited_hasExponentialTypeAtMost`), and `|F(x)| ≤ ‖g‖₁` on `ℝ`. The hard direction and
Beurling's `B` are not done.

## Adversarial revalidation

* What the proof uses: the conclusion is not a restatement of the hypotheses; the proof goes
  through `posIndex_blockQ_le` (the reflection structure) and the rank–trace inequality. The two
  prime-side estimates and the Poisson bound are explicit hypotheses; no instance of them for a
  concrete taper is constructed in this repository (that is the open boundary).
* Normalisation: the numerator is `#onLine` (distinct points on the line), the denominator
  `count = Σ mult` (with multiplicity) — the harder direction, as in `Zeta23`.
* `#print axioms` for `posIndex_conj_eq`, `negIndex_conj_eq`, `norm_trace_mul_le_of_posSemidef`,
  `inertia_certificate_ratio`, `ReflectionConfig.posIndex_gram_le`,
  `ReflectionConfig.gram_certificate_ratio`, `GramFamily.two_thirds_eventually`: exactly
  `propext`, `Classical.choice`, `Quot.sound`. No `sorry` in either new module.
