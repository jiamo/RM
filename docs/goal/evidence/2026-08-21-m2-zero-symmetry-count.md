# Evidence: conjugation symmetry of the zero set, and the parity of `N(T)` (2026-08-21)

Row: `M2-ZERO-SYMMETRY-COUNT` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroSymmetryCount.lean`, writing
`nontrivialZeroSet = {s | ζ s = 0, 0 < re s < 1}` and
`N(T) = (nontrivialZeros T).ncard = #{ρ ∈ nontrivialZeroSet | |im ρ| ≤ T}`:

* `im_ne_zero_of_mem_nontrivialZeroSet` : every nontrivial zero has nonzero imaginary part;
* `conj_mem_nontrivialZeroSet`, `one_sub_mem_nontrivialZeroSet` : the zero set is stable under
  `s ↦ conj s` and under `s ↦ 1 - s`;
* `conj_image_upperNontrivialZeroSet` : conjugation maps the upper half `{ρ | im ρ > 0}` of the
  zero set bijectively onto the lower half;
* `union_upper_lower_nontrivialZeroSet` : the zero set is the (disjoint) union of its two halves;
* `infinite_upperNontrivialZeroSet`, `infinite_lowerNontrivialZeroSet` : **each half-plane
  contains infinitely many nontrivial zeroes**;
* `ncard_nontrivialZeros_eq_two_mul` : `N(T) = 2 · #{ρ : ζ ρ = 0, 0 < re ρ < 1, 0 < im ρ ≤ T}`;
* `even_ncard_nontrivialZeros` : **`N(T)` is even** for every `T`.

## The argument

All the analytic input is already in the repository.

* *No real zeroes.* `riemannZeta_ofReal_ne_zero_of_lt_one` (`M0-SYMMETRY`) says `ζ(x) ≠ 0` for
  real `0 < x < 1`; a nontrivial zero with `im ρ = 0` equals `((re ρ : ℝ) : ℂ)`, which is such an
  `x`. Hence the zero set splits as the disjoint union of an upper and a lower half.
* *Stability.* `riemannZeta_conj_of_mem_strip` and `riemannZeta_one_sub_eq_zero_of_mem_strip`
  (both `M0-SYMMETRY`) give the two symmetries; the strip conditions are preserved because
  `(conj s).re = s.re` and `(1 - s).re = 1 - s.re`.
* *Bijection between the halves.* Conjugation is an involution, so `conj '' upper = lower` (each
  inclusion is one application of stability plus `(conj s).im = -s.im`).
* *Infinitude of each half.* If the upper half were finite, so would be its image the lower half,
  and hence their union — the whole zero set — contradicting `infinite_nontrivialZeroSet`
  (`M2-ZERO-INFINITE`). The lower half is then infinite as the injective image of the upper.
* *Parity.* At a fixed height the same splitting is disjoint and both parts are finite (subsets
  of `nontrivialZeros T`, finite by `M2-ZERO-COUNT`), so `Set.ncard_union_eq` applies; the two
  parts have equal cardinality by `Set.ncard_image_of_injective` along conjugation, whence
  `N(T) = 2 · #upper` and `N(T)` is even.

## Commands run

```
lake build RiemannHypothesis.ZeroSymmetryCount
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for each of the eight results above reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Multiplicities are ignored.** `nontrivialZeros T` is a set of points and `ncard` counts
  points, so the parity statement concerns *distinct* zeroes. Counted with multiplicity the same
  statement would require the equality of the orders of vanishing at `ρ` and `conj ρ`, which is
  not proved here.
* **No location.** Nothing is proved about the real parts of the zeroes, so nothing here bears on
  the Riemann hypothesis.
* **No rate.** The infinitude of each half-plane inherits the non-effectivity of
  `infinite_nontrivialZeroSet`; no height of any individual zero is exhibited.

## Adversarial revalidation: M2-ZERO-SYMMETRY-COUNT

Second, independent pass.

* **Claim mode.** All the results are `theorem`s of this repository and are pinned in full in
  `scripts/revalidation.lean` — including `rfl`-pins of the two new definitions
  `upperNontrivialZeroSet` and `lowerNontrivialZeroSet`, so the halves cannot be silently
  redefined into something trivial — with the repository declarations as proof terms;
  `scripts/audit.sh` prints their axioms.
* **Vacuity check.** None of the statements is vacuous: `infinite_upperNontrivialZeroSet` asserts
  the existence of infinitely many zeroes, so it is strictly stronger than `M2-ZERO-EXISTS`, and
  `ncard_nontrivialZeros_eq_two_mul` is an equality of natural numbers that would fail if
  `nontrivialZeros T` were infinite (`Set.ncard` would then return `0` on the left while the
  right-hand side counted the upper zeroes), so the finiteness input of `M2-ZERO-COUNT` is
  load-bearing.
* **Is the parity a `ncard = 0` degeneracy?** No. For small `T` both sides are genuinely `0`
  (a true statement — the lowest zero sits at height `≈ 14.13`), but for large `T` the left side
  is positive: `tendsto_ncard_nontrivialZeros_atTop` (`M2-ZERO-COUNT-LOWER`) forces `N(T) → ∞`,
  so the identity is asserting something at infinitely many heights where both sides are large.
* **Direction check.** `Set.ncard_union_eq` needs disjointness *and* finiteness of both parts;
  both are supplied from `finite_nontrivialZeros`, and disjointness is `0 < im` versus `im < 0`,
  which is where the absence of real zeroes is used. Dropping that input would make the union
  fail to exhaust the zero set, not merely weaken the count.
* **Is it circular?** No: `M0-SYMMETRY` is proved from the paired eta series and the functional
  equation, `M2-ZERO-INFINITE` from a growth contradiction for `ξ`, and `M2-ZERO-COUNT` from a
  Jensen-type counting lemma; none of the three uses this row.
* **Sanity check against the literature.** Classically the nontrivial zeroes come in conjugate
  pairs `ρ, conj ρ` (and in quadruples `ρ, conj ρ, 1-ρ, 1-conj ρ` off the critical line), the
  first pair being at height `≈ ±14.13`, and `N(T)` counted over `|im ρ| ≤ T` is indeed even.
  What is new here is only that this is machine-checked from the repository's own results.
