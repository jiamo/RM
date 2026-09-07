# The mean value theorem for well-spaced frequencies, Vaughan's identity, the corpus instance, and the Vinogradov system

Date: 2026-09-06
Modules: `RiemannHypothesis/MeanValueWellSpaced.lean`, `RiemannHypothesis/VaughanIdentity.lean`,
`RiemannHypothesis/CorpusInstance.lean`, `RiemannHypothesis/VinogradovMeanValue.lean`

## Why these four

They are the four points at which the recorded boundaries of the board are load-bearing rather
than decorative.

* `M2-MEANVALUE` records that the sharp Montgomery–Vaughan form of the mean value theorem is
  missing; what the applications actually consume is not the generalized Hilbert inequality but
  the bound `T + 1/δ` for an arbitrary family of `δ`-separated frequencies, and that is what is
  proved here.
* The sieve chain (`large sieve → squarefree → Brun–Titchmarsh → Brun`) ends outside the main
  line; the missing combinatorial input on the way to Bombieri–Vinogradov is Vaughan's identity,
  now available as an exact identity in the Dirichlet convolution ring.
* `M2-CORPUS-INSTANCE` asked for the abstract counting system of `CorpusCeiling` to be realized
  by the zeroes of `ζ`.  Until that is done, the non-derivability results of `CorpusCeiling` are
  statements about an abstraction; afterwards they are statements about a system that provably
  holds of `ζ`.
* `M3-VINOGRADOV` has no substrate at all.  The counting object of Vinogradov's mean value
  theorem, and the translation invariance that efficient congruencing runs on, are elementary
  and are fixed here so that the analytic work has something to attach to.

## What is proved

### `MeanValueWellSpaced.lean`

For real frequencies `λ_r`, `r ∈ S`, with `|λ_r − λ_s| ≥ δ` for `r ≠ s`, and arbitrary complex
coefficients `x_r`:

* `rowSum_le` — `∑_s exp(−(λ_r − λ_s)²/(4b)) ≤ 1 + 2√(πb)/δ`.  The combinatorial input is
  `card_fiber_le_two`: at most two frequencies lie at distance in `[kδ, (k+1)δ)` from `λ_r`, one
  on each side.
* `bilinear_le_of_rowSum_le` — Schur's test for a symmetric nonnegative kernel.
* `integral_normSq_expSum_le` — `∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ e(√π T + 2π/δ) ∑ ‖x_r‖²`, and
  `integral_normSq_expSum_le_mv`, `integral_Ioc_normSq_expSum_le_mv` — the same with the round
  constant `18 (T + 1/δ)`, over `[−T, T]` and over `[0, T]`.

The proof is the Gaussian majorant method: `1 ≤ e·exp(−t²/T²)` on `[−T, T]`, the Gaussian turns
the mean square into an absolutely convergent bilinear form with kernel
`exp(−T²(λ_r − λ_s)²/4)`, and the separation bounds its row sums.  The generalized Hilbert
inequality is *not* proved, and the constant on the main term is `e√π`, not the sharp `1`.

### `VaughanIdentity.lean`

`vaughan_identity` — in `ArithmeticFunction ℝ`,

    Λ = Λ_{≤U} + log ∗ μ_{≤V} − Λ_{≤U} ∗ ζ ∗ μ_{≤V} + Λ_{>U} ∗ ζ ∗ μ_{>V},

proved from `Λ ∗ ζ = log` and `ζ ∗ μ = 1` alone; `vonMangoldt_eq_of_lt` is its value at `n > U`,
where the first term drops out, `typeI_apply`, `typeII_apply`, `typeIII_apply` write the three
terms as divisor sums over the triples `b c m = n` with the stated constraints, and
`sum_vonMangoldt_eq` sums the identity against an arbitrary weight over `U < n ≤ N`.  No
estimate for either bilinear sum is proved, so nothing about primes in progressions follows.

### `CorpusInstance.lean`

`zetaCorpus : ZeroCorpus 0.33`, with `total = windowCount 0 T`,
`distinct = windowCountDistinct 0 T`, `onLine = windowCountOnLine 0 T`,
`off = windowCountOffLine 0 T` and `offAt δ T = (offAtSet δ T).ncard`, where `offAtSet` is the
set of off-line zeroes of the window at distance at least `δ` from the line — equal to
`zerosOffCriticalLine δ T` for `δ > 0` (`ncard_offAtSet_eq`), which is the set the density
theorems bound, and defined so that the field `offAt_le_off`, which is quantified over all `δ`,
is true also for `δ ≤ 0`.

The supporting facts proved on the way:

* `windowCountDistinct_add`, `windowCountOnLine_add`, `windowCountOffLine_add` — additivity of
  the three distinct counts over adjacent ordinate windows (the multiplicity count already had
  `windowCount_add`).  This is what turns the dyadic-window statement of
  `sixty_seven_percent_on_critical_line` into the difference of cumulative counts that the field
  `window_onLine` asks for.
* `ncard_even_of_criticalReflect` — a finite set of off-line points stable under `ρ ↦ 1 − ρ̄` has
  even cardinality, whence `exists_windowCountOffLine_eq_two_mul` and
  `exists_ncard_offAtSet_eq_two_mul` (the reflection preserves the distance to the line).
* `windowCount_le_log_mul_windowCountDistinct` — the cumulative multiplicity bound
  `N(T) ≤ (41 + K) log T · N_d(T)` for `T ≥ 25`, from `zeroMultiplicity_le_log_abs_im` above
  height `25` and `exists_zeroMultiplicity_bound_low` below it.
* `exists_offAtSet_eq_empty` — the classical zero-free region in counting form.  The right-hand
  side is `zeroFreeRegion`; the left-hand side is the reflection `criticalReflect`; the zeroes of
  ordinate below `3`, which the zero-free region does not see, are excluded by
  `riemannZeta_ne_zero_of_abs_im_le` (no zeroes below height `7/2`).
* `exists_ncard_offAtSet_eq_windowCountOffLine` — the off-line count of a window is attained at
  a positive distance: the window is finite, so the minimum of `|re ρ − 1/2|` over it is
  positive.

Consequences restated for `ζ`: `zeta_windowOff_le` (at most `33 %` of the zeroes of a dyadic
window are off the line — the abstract soundness bound, unfolded),
`zetaStripForm_iff_rhCounts_zetaCorpus` (the Riemann hypothesis is exactly `RHCounts zetaCorpus`)
and `rh_not_derivable_from_zeta_corpus`: the corpus that `ζ` provably satisfies has a model whose
off-line count is not identically zero, so no argument using only those facts can prove the
conjecture.  `zeta_density_not_sufficient` records the same for density bounds at a fixed `δ`.

### `VinogradovMeanValue.lean`

`vinBox`, `VinogradovEq`, `vinogradovCount` fix the system and its solution count `J_{s,k}(X)`;
`vinogradovEq_translate` and `vinogradovEq_dilate` are its translation and dilation invariances
(the first is the invariance efficient congruencing exploits), `pow_card_le_vinogradovCount` is
the diagonal lower bound `X^s ≤ J`, `vinogradovCount_le_pow` the trivial upper bound, and
`vinogradovCount_one_one` the non-vacuity check `J_{1,1}(X) = X`.
`VinogradovMeanValueBound` records the theorem itself as a `Prop`; it is **not** proved, and
nothing here bears on the zero-free region.

## Verification

* `lake build` — succeeds; the four modules are imported by `RiemannHypothesis.lean`.
* No `sorry` outside `Challenge.lean`.
* The axioms of every new declaration are exactly `[propext, Classical.choice, Quot.sound]`,
  checked by the `#print axioms` block of `scripts/audit.sh`.
* Statements pinned in `scripts/revalidation.lean`: the row-sum bound, both forms of the mean
  value theorem, Vaughan's identity written out in full, the five fields of `zetaCorpus` by
  `rfl`, the identification of `offAtSet` with `zerosOffCriticalLine`, the soundness bound for
  `ζ`, the equivalence with the Riemann hypothesis, the independence statement, and the three
  Vinogradov facts.
* `./scripts/audit.sh` — `OK`.

## Adversarial revalidation: M2-MEANVALUE-WELLSPACED

*Is the statement vacuous?*  No: `Separated S lam δ` is satisfiable with `S` arbitrary — take
`lam r` any `δ`-separated family, e.g. `lam = fun r => δ * r` on a finite set of integers — and
the conclusion bounds an integral of a genuinely nonzero function.  Taking `S` a singleton gives
`∫₋ᵀᵀ ‖x‖² = 2T‖x‖²`, so the constant `18` cannot be replaced by anything below `2`, and the
`1/δ` term is needed because the left side is at least `‖∑ x_r‖²` times a fixed length while the
right side must dominate it for `T → 0`.

*Is the separation hypothesis used?*  Yes, in exactly one place: `card_fiber_le_two`.  Without
it the row sums are unbounded (all frequencies equal gives row sum `|S|`), and the conclusion is
false for `x ≡ 1`, `λ ≡ 0`, `S` large: the left side is `2T|S|²` and the right side
`18(T + 1/δ)|S|`.

*Is the bound weaker than the one already in the repository?*  It is a different statement:
`integral_normSq_dirichletPoly_le_mv` is about the frequencies `log n` and has the error inside
the sum; this one is about arbitrary separated frequencies.  Neither implies the other.

## Adversarial revalidation: M2-VAUGHAN

*Is the identity trivial or circular?*  It is an identity, so its content is entirely in the
support of the terms: `Λ_{≤U}` vanishes above `U`, the type II term is supported on triples with
`b ≤ U`, `c ≤ V`, and the type III term on triples with `b > U`, `c > V`.  The proof uses only
`Λ ∗ ζ = log` and `ζ ∗ μ = 1`, both of which are Mathlib theorems, not hypotheses.

*Could the truncations be wrong?*  `truncLE_add_truncGT` checks that the two truncations
reconstruct the original function, and `truncLE_apply`, `truncGT_apply` are definitional.  If the
inequality in either truncation were flipped, `vonMangoldt_eq_of_lt` — which needs
`truncLE Λ U n = 0` for `n > U` — would fail.

*Does anything analytic follow?*  No.  The bilinear sums are not estimated; the row records the
identity only.

## Adversarial revalidation: M2-CORPUS-INSTANCE

*Does the instance actually check the correspondence?*  Yes: `zetaCorpus` is a term of type
`ZeroCorpus 0.33`, so Lean checks every field against the repository's theorems about `ζ`.  The
five counting functions are pinned by `rfl` in `scripts/revalidation.lean`, so the instance
cannot silently be built out of some other, more convenient, functions.

*Is `offAt` the right counting function?*  `ncard_offAtSet_eq` proves that for `δ > 0` it is
exactly `(zerosOffCriticalLine δ T).ncard`, the function the density theorems of this repository
bound.  The intersection with the off-line condition matters only for `δ ≤ 0`, where the
structure demands `offAt δ T ≤ off T` and the unintersected set would count the on-line zeroes
too.

*Does the independence statement claim more than it proves?*  No.  It says that the list of
facts collected in `ZeroCorpus 0.33` has a model with a positive off-line count, and that `ζ` is
a model of that list.  It does not say the Riemann hypothesis is unprovable, nor that it is
false; it says a proof must use a fact outside the list.

*Is the `0.33` real?*  It is the constant of `sixty_seven_percent_on_critical_line`, which the
field `window_onLine` consumes after converting the dyadic window statement into cumulative
differences with `windowCount_add` and `windowCountOnLine_add`.  Had the conversion been wrong,
the field would not typecheck against `1 − 0.33 = 0.67`.

## Adversarial revalidation: M3-VINOGRADOV-SYSTEM

*Is `vinogradovCount` the right object?*  It counts pairs of `s`-tuples from `[1, X]` whose power
sums agree up to degree `k`; `vinogradovCount_one_one` computes `J_{1,1}(X) = X` and the diagonal
bound gives `X^s ≤ J`, both of which would fail for an off-by-one box or an empty degree range.

*Is anything about the mean value theorem claimed?*  No.  `VinogradovMeanValueBound` is a `Prop`
and appears nowhere as a hypothesis or a conclusion; the row is `DONE_WEAK` and its
`open_boundary` says so.
