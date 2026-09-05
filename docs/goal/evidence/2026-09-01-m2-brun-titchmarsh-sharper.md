# M2-BRUN-TITCHMARSH — the squarefree harmonic sum, and the constants of Brun–Titchmarsh

## Task

Close the first item of the open boundary recorded for `M2-BRUN-TITCHMARSH`: the crude lower
bound `∑_{q ≤ Q squarefree} 1/q ≥ (log Q)/4 − 3/4`, which was responsible both for the constant
`70` in the Brun–Titchmarsh inequality of that row and for its threshold `log y ≥ 24`. Two bounds
are proved: `(4/7) log Q` for the squarefree harmonic sum itself, and the classical `log Q` for
the sifting sum, which is the one the application uses.

## Lean declarations

Added to `RiemannHypothesis/BrunTitchmarsh.lean` (namespace `RiemannHypothesis.BrunTitchmarsh`):

* `sum_inv_sq_Icc_one_le` — `∑_{d ≤ Q} 1/d² ≤ 7/4`, from the telescoping bound `sum_inv_sq_le`
  of `M2-LARGE-SIEVE-SQUAREFREE` for the tail from `d = 2`;
* `sum_inv_le_sum_inv_sq_mul_sum_inv_squarefree` — the factorization `n = d² q` with `q`
  squarefree gives
  `∑_{n ≤ Q} 1/n ≤ (∑_{d ≤ Q} 1/d²)(∑_{q ≤ Q squarefree} 1/q)`;
* `four_sevenths_log_le_sum_inv_squarefree`, `four_sevenths_log_le_siftSum` —
  `(4/7) log Q ≤ ∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`;
* `sum_geom_Icc_le` — `∑_{k=1}^{K} x^k ≤ x/(1 − x)` for `0 ≤ x < 1`;
* `sum_inv_primeFactors_eq_le` — the reciprocals of the `m ≤ Q` whose set of prime factors is
  exactly `P` sum to at most `∏_{p ∈ P} 1/(p − 1)`;
* `squarefree_prod_primeFactors`, `Icc_subset_biUnion_primeFactors` — the radical of `n` is
  squarefree, has the same prime factors as `n`, and is at most `n`;
* `log_le_siftSum` — the classical lower bound `log Q ≤ siftSum Q`, with the constant `1`;
* `card_primes_Ico_le_of_const` — the Brun–Titchmarsh estimate with the two numerical constants
  left as parameters `c` and `K`;
* `card_primes_Ico_le` — **Brun–Titchmarsh**, restated: for every `x` and every `y` with
  `log y ≥ 4`, `#{p prime : x ≤ p < x + y} ≤ 13 y / log y + √y + 1`;
* `card_primes_Ico_le_of_log_ge_24` — the same with the constant `9`, for `log y ≥ 24`;
* `card_primes_range_le` — the case `x = 0`, restated: `π(N) ≤ 13 N / log N + √N + 1` once
  `log N ≥ 4`.

The earlier route through the non-squarefree integers (`sum_inv_multiples_le`,
`sum_biUnion_le_sum_sum`, `sum_inv_not_squarefree_le`, `quarter_log_le_sum_inv_squarefree`,
`quarter_log_le_siftSum`) is kept: it is a true statement about the density of the squarefree
integers, and it is still pinned in `scripts/revalidation.lean`.

## The proof

**The squarefree harmonic sum.** Every `n ≥ 1` can be written as `n = d² q` with `q` squarefree
(mathlib's `Nat.sq_mul_squarefree`); a choice of such a factorization for each `n` is an
*injective* map `n ↦ (d, q)`, since `d² q` recovers `n`. Both `d` and `q` are at most `n`, so the
image of `[1, Q]` lies in `[1, Q] × {q ≤ Q squarefree}`, and since all terms are nonnegative

  `∑_{n ≤ Q} 1/n ≤ ∑_{(d, q)} 1/(d² q) = (∑_{d ≤ Q} 1/d²)(∑_{q ≤ Q squarefree} 1/q)`.

With `∑_{d ≤ Q} 1/d² ≤ 7/4` and mathlib's `log Q ≤ ∑_{n ≤ Q} 1/n`, this gives

  `∑_{q ≤ Q squarefree} 1/q ≥ (4/7) log Q`,

with no additive loss — against `(log Q)/4 − 3/4` before. The truth is `(6/π²) log Q + O(1)`, and
`6/π² = 0.6079…` against `4/7 = 0.5714…`, so the constant is now within `6 %` of the optimum;
what is lost is the additive `O(1)`, which is where the remaining slack in the threshold sits.

**The sifting sum itself.** The sifting sum is larger than the squarefree harmonic sum, and for it
the constant is `1`, not `4/7`. For squarefree `d`,

  `∏_{p ∣ d} 1/(p − 1) = ∏_{p ∣ d} (1/p + 1/p² + ⋯) = ∑_{m : rad m = d} 1/m`,

and every `n ≤ Q` occurs in exactly one of these sums, the one indexed by its radical. The Lean
proof is the finite form of that computation: `sum_inv_primeFactors_eq_le` is proved by induction
on the set `P` of prime factors, removing one prime `p` and writing `m = p^k m'` with `k ≥ 1` and
`m'` prime to `p` — an injective map `m ↦ (k, m')` into `[1, Q] × {m' ≤ Q : rad m' = P \ {p}}` —
with the geometric partial sum `∑_{k=1}^{Q} p^{-k} ≤ 1/(p − 1)` of `sum_geom_Icc_le` supplying the
factor at `p`. Since the radical of `n ≤ Q` is squarefree and at most `n`,
`Icc_subset_biUnion_primeFactors` covers `[1, Q]` by the fibres, and

  `log Q ≤ ∑_{n ≤ Q} 1/n ≤ siftSum Q`.

**The constants.** At `Q = ⌊√y⌋` one has `log Q ≥ (log y)/2 − log 2`, so

  `siftSum Q ≥ log Q ≥ (1/2) log y − log 2`.

The sieve gives `|A| · siftSum Q ≤ Q² + π y ≤ 4.15 y` for the set `A` of primes of `[x, x + y)`
above `√y`, so for any `c` with `c log y ≤ (1/2) log y − log 2` and any `K` with `Kc ≥ 4.15`,

  `|A| ≤ K y / log y`.

This is `card_primes_Ico_le_of_const`. Since `log 2 = 0.6931…` is a fixed additive loss, the
admissible `c` improves as `y` grows: `c = 0.326` is admissible for `log y ≥ 4`, giving `K = 13`,
and `c = 0.471` for `log y ≥ 24`, giving `K = 9`. The primes of `[x, x + y)` below `√y` number at
most `√y + 1`, which is the additive term.

## Gates

* `lake build RiemannHypothesis.BrunTitchmarsh` — succeeds, with no warning from the module.
* `./scripts/audit.sh` — the new statements are pinned in `scripts/revalidation.lean`; the
  previous pins for `card_primes_Ico_le` and `card_primes_range_le` are replaced by the sharper
  ones, and the `(4/7) log Q` and `log Q` bounds are added.
* No `sorry`; the axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; no unproved
  `Prop` of the repository is used, so no entry of `docs/goal/conditional-theorems.txt` changes.

## Open boundary after this row

The constant `13` (and `9` for `log y ≥ 24`) is still above the sharp `2` of Montgomery–Vaughan
and the `2 + o(1)` of the classical Brun–Titchmarsh theorem: what remains is the factor `π` of
this repository's large sieve, in place of the sharp `1`, and the rigid choice `Q = ⌊√y⌋`, which
loses an additive `log 2`. With the sharp large sieve and `Q = √y / log y` the same route gives
`2 + o(1)`; with the factor `π` kept and `Q` optimized it would give `2π + o(1)`. The threshold `log y ≥ 4`, that
is `y ≥ 55`, is an artefact of the same losses. Only the interval form is proved: the
arithmetic-progression form `π(x + y; q, a) − π(x; q, a) ≪ y / (φ(q) log(y/q))` needs the sieve at
moduli coprime to `q`, and no Bombieri–Vinogradov consequence follows. Nothing about `ζ` follows:
no zero-free region, no zero-density estimate, no mean value theorem, and no zero is located.
