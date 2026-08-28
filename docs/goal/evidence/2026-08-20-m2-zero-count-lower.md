# Evidence: the counting function `N(T)` is unbounded (2026-08-20)

Row: `M2-ZERO-COUNT-LOWER` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroCountLower.lean`, writing
`N(T) = (nontrivialZeros T).ncard = #{ρ : ζ ρ = 0, 0 < re ρ < 1, |im ρ| ≤ T}`:

* `monotone_ncard_nontrivialZeros` : `T ↦ N(T)` is monotone;
* `exists_mem_nontrivialZeroSet_lt_abs_im` : **for every height `T` there is a zero of `ζ` in the
  open critical strip with `T < |im s|`** — the nontrivial zeroes are not confined to any
  horizontal strip;
* `exists_le_ncard_nontrivialZeros` : for every `n : ℕ` there is a height `T ≥ 0` with `n ≤ N(T)`;
* `tendsto_ncard_nontrivialZeros_atTop` : `N(T) → ∞` as `T → ∞`.

## The argument

Both inputs are already in the repository. `finite_nontrivialZeros` (`M2-ZERO-COUNT`) says that
`nontrivialZeros T` is finite for every `T`, and `infinite_nontrivialZeroSet`
(`M2-ZERO-INFINITE`) says that the whole zero set in the strip is infinite.

* *Unboundedness of the heights.* If every nontrivial zero satisfied `|im s| ≤ T` for one fixed
  `T`, then `nontrivialZeroSet ⊆ nontrivialZeros T` would be a subset of a finite set, hence
  finite — contradicting `infinite_nontrivialZeroSet`.
* *Every `n` is attained.* An infinite set contains a finite subset `t` of cardinality `n`
  (`Set.Infinite.exists_subset_card_eq`). The finitely many numbers `|im s|`, `s ∈ t`, have an
  upper bound `M`, so `t ⊆ nontrivialZeros (max 0 M)` and therefore
  `n = #t ≤ N(max 0 M)` by `Set.ncard_le_ncard` (the larger set being finite).
* *Divergence.* Monotonicity is immediate from `Set.ncard_le_ncard`; combined with the previous
  point applied to `⌈b⌉₊`, the criterion `tendsto_atTop_atTop` gives `N(T) → ∞`.

## Commands run

```
lake build RiemannHypothesis.ZeroCountLower
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `monotone_ncard_nontrivialZeros`,
`exists_mem_nontrivialZeroSet_lt_abs_im`, `exists_le_ncard_nontrivialZeros` and
`tendsto_ncard_nontrivialZeros_atTop` reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **No rate.** Nothing here approaches the classical `N(T) ~ (T/2π) log (T/2πe)`, nor even a
  lower bound of the form `N(T) ≫ T`: the divergence inherits the non-effectivity of
  `infinite_nontrivialZeroSet`, which is proved by contradiction. In particular no bound on the
  height of the `n`-th zero is obtained.
* **No location.** Nothing is proved about the real parts, so the row does not touch the Riemann
  hypothesis; and no individual zero is exhibited.
* Multiplicities are ignored: `nontrivialZeros T` is a set of points and `ncard` counts points.
* The complementary upper bound `N(T) ≤ C T log T` is `M2-ZERO-COUNT`, proved separately; the two
  together give `N(T) → ∞` with `N(T) = O(T log T)`, and nothing between.

## Adversarial revalidation: M2-ZERO-COUNT-LOWER

Second, independent pass.

* **Claim mode.** All four results are `theorem`s of this repository and are pinned in full in
  `scripts/revalidation.lean` with the repository declarations as proof terms; `scripts/audit.sh`
  prints their axioms.
* **Vacuity check.** None of the statements is vacuous. `exists_mem_nontrivialZeroSet_lt_abs_im`
  asserts the existence of a zero, so it would be false if the strip were empty of zeroes; it is
  therefore at least as strong as `M2-ZERO-EXISTS`. `tendsto_ncard_nontrivialZeros_atTop` is a
  statement about a function taking finite values — if `nontrivialZeros T` were infinite for some
  `T`, `Set.ncard` would return `0` there and the divergence could not hold, so the finiteness
  input of `M2-ZERO-COUNT` is genuinely load-bearing and is not being hidden by a junk value.
* **Direction check.** `Set.ncard_le_ncard` requires the *larger* set to be finite; both uses
  supply `finite_nontrivialZeros`, so no inequality is obtained from a `ncard = 0` degeneracy.
* **Is it circular?** No: the two inputs are proved independently of each other and of this row —
  local finiteness comes from the Jensen-type counting lemma plus the order-one growth of `ξ`,
  infinitude from the growth contradiction after dividing out finitely many roots.
* **Consistency with the upper bound.** `M2-ZERO-COUNT` gives `N(T) ≤ C T log T`, which is
  compatible with — and, for `T` large, far above — the divergence proved here. Had the two rows
  been in conflict (e.g. a bounded `N` together with `N → ∞`), the repository would be
  inconsistent; they are not.
* **Sanity check against the literature.** Classically the first nontrivial zero is at height
  `≈ 14.13` and `N(T) ~ (T/2π) log (T/2πe)`, so all four statements are true and considerably
  weaker than what is known numerically; what is new here is that they are machine-checked from
  the repository's own results.
