# An explicit sequence of low discrepancy: the van der Corput sequence

Date: 2026-09-08
Module: `RiemannHypothesis/VanDerCorputSequence.lean`

## Why

Every discrepancy bound in the repository so far is an *upper* bound for a sequence whose
discrepancy is only known to decay slowly: the Erdős–Turán route of
`RiemannHypothesis/Discrepancy.lean` gives `D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9)` for badly
approximable `α`, and `RiemannHypothesis/WeylDiscrepancyQuadratic.lean` gives a comparable rate
for `α n²`.  Nothing exhibited a sequence with the *logarithmic* rate `O(log N / N)` that the
Koksma inequalities of `M1-KOKSMA-LIPSCHITZ-SHARP` and `M1-KOKSMA-VARIATION` are designed to be
used with.  This row supplies one, unconditionally and with explicit constants.

## What is proved

* `vdc` — the base-two radical inverse, defined by the recursion
  `vdc n = (n % 2 + vdc (n / 2)) / 2`.  Its first values are proved to be
  `0, 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8`, so the definition is the classical one.
* `vdc_nonneg`, `vdc_lt_one`, `fract_vdc` — the sequence lives in `[0, 1)`, so taking fractional
  parts, as the discrepancy of this repository does, changes nothing.
* `vdc_split` — the digit identity `vdc n = (revBits j n + vdc (n / 2^j)) / 2^j`, where
  `revBits j n` is the reversal of the lowest `j` binary digits of `n`.
* `vdc_mem_cell` — hence `vdc n ∈ [k/2^j, (k+1)/2^j)` with `k = revBits j n`.
* `revBits_inj_mod`, `image_revBits_block` — the cell index determines `n` modulo `2^j`, so on
  **any** `2^j` consecutive indices the cell index is a bijection onto `{0, …, 2^j − 1}`: each
  dyadic cell of length `2^(-j)` receives exactly one point.
* `abs_blockCount_sub_le_one` — the counting error of an initial segment `[0, x)`, `0 ≤ x ≤ 1`,
  over such a block is at most `1`.
* `abs_count_sub_le_size` — for every offset `a`, every `N` and every `x ∈ [0, 1]`,

      |#{n ∈ [a, a+N) : vdc n < x} − N x| ≤ Nat.size N = log₂ N + 1 .

* `discrepancy_vdc_le` — `D_N(vdc) ≤ 2 (log₂ N + 1)/N` for every `N ≥ 1`.
* `abs_countIn_vdc_div_sub_le` — the counting form: every `[a, b) ⊆ [0, 1]` receives its share
  of the first `N` points to within `2 (log₂ N + 1)/N`.
* `abs_countIn_zero_sub_le_size` — the star form of the same bound, with the constant `1`.
* `one_div_two_mul_le_discrepancy` — in the other direction, and for *every* sequence,
  `D_N ≥ 1/(2N)`: among the `2N` cells of length `1/(2N)` the first `N` points must miss one.
* `discrepancy_vdc_bounds` — hence `1/(2N) ≤ D_N(vdc) ≤ 2 (log₂ N + 1)/N`, so the rate is
  optimal up to the logarithm.
* `tendsto_size_div_atTop`, `tendsto_discrepancy_vdc` — the bound tends to zero, so the sequence
  is equidistributed modulo one.
* `koksma_vdc_lipschitz`, `koksma_vdc_variation`, `tendsto_average_vdc_variation` — the
  quadrature consequences: for `L`-Lipschitz `f`,

      |(1/N) ∑_{n<N} f(vdc n) − ∫₀¹ f| ≤ L · 2 (log₂ N + 1)/N ,

  the corresponding bound with `2 V(f)` for `f` of bounded variation, and the limit statement.

## Proof

Everything rests on one combinatorial fact.  Splitting the binary expansion of `n` at position
`j` splits the expansion of `vdc n` at position `j` as well (`vdc_split`), and the first `j`
digits of `vdc n` are the lowest `j` digits of `n`, reversed.  Since `vdc (n / 2^j) ∈ [0, 1)`,
the point `vdc n` lies in the dyadic cell indexed by `revBits j n`, and `revBits j` determines
`n` modulo `2^j` — this is proved by induction on `j`, comparing the top digit and dividing.  A
window of `2^j` consecutive integers is a complete residue system modulo `2^j`, so `revBits j`
is injective on it, and by counting it is a bijection onto `{0, …, 2^j − 1}`.  Hence each cell
holds exactly one of the `2^j` points, and for any `x` the number of points below `x` is between
`⌊2^j x⌋` and `⌈2^j x⌉`, an error at most `1`.

An arbitrary block of `N` consecutive indices is then cut along the binary digits of `N`: with
`j = Nat.size N − 1` the first `2^j` indices form one dyadic block and the remaining
`N − 2^j < 2^j` are handled by strong induction, whose bound `Nat.size (N − 2^j) ≤ j` gives the
telescoping `1 + Nat.size (N − 2^j) ≤ Nat.size N`.  Finally `[a, b)` is the difference of the
initial segments `[0, b)` and `[0, a)`, which doubles the constant, and dividing by `N` and
taking the supremum over intervals gives `discrepancy_vdc_le`.

For the limit, `Nat.size N ≥ 1` and `2^(Nat.size N − 1) ≤ N` combine with the elementary
`k² ≤ 4 · 2^k` to give `(Nat.size N)² ≤ 8 N`, i.e. `Nat.size N / N ≤ 8 / Nat.size N`, and
`Nat.size N → ∞`.

The lower bound is a pigeonhole: the `2N` cells `[k/(2N), (k+1)/(2N))` are disjoint, the map
`n ↦ ⌊2N ⟨xₙ⟩⌋` sends each of the `N` indices into one of them, so some cell receives none, and
its deviation is exactly `1/(2N)`.

## Scope

The constant `2` is not optimal, and the lower bound proved is only the trivial `1/(2N)`:
Schmidt's theorem, that `N D_N` is unbounded for every sequence, is not formalized, so the
*optimality* of the logarithmic rate is asserted nowhere in Lean.  Only the base-two sequence is treated — no general base, no Halton
or Hammersley point sets, no multidimensional discrepancy.  Nothing here concerns `ζ`.

## Adversarial revalidation: M1-VDC-SEQUENCE

* **Is the sequence the intended one, or an accident of the recursion?**  The first eight values
  are proved in the module (`vdc_zero` … `vdc_seven`): `0, 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8`.
  These are the van der Corput sequence, and they already show the characteristic behaviour: the
  first `2^j` terms hit each dyadic cell of length `2^(-j)` exactly once.
* **Is the bound vacuous for small `N`?**  It is weak but not vacuous, and it is never wrong: at
  `N = 1` it reads `D_1 ≤ 2`, which is implied by `discrepancy_le_one`; the bound becomes
  equal to the trivial bound at `N = 8`, where it reads `D_8 ≤ 1`, and informative from `N = 16`
  on, where it reads `D_16 ≤ 5/8`.  No claim of the module is stronger for small `N` than the trivial `D_N ≤ 1`.
* **Is the upper bound consistent with a lower bound proved here?**  Yes, and the two are
  proved independently: `one_div_two_mul_le_discrepancy` gives `D_N ≥ 1/(2N)` for every
  sequence, and `2 (log₂ N + 1)/N ≥ 1/(2N)` for every `N ≥ 1`, so the pair is consistent — an
  upper bound below `1/(2N)` would have been a contradiction, and the module would not compile.
* **Is the theorem consistent with the known lower bounds?**  Yes.  The classical lower bound
  for the van der Corput sequence — known in the literature, not formalized here — is of order
  `log N / N`, the same order as the upper bound proved here, so the statement is not
  accidentally stronger than the truth; and the constant
  sequence `0`, for which the repository proves `D_N ≥ 1/2` (`half_le_discrepancy_const_zero`),
  is *not* of this form — the bound distinguishes the two.
* **Does anything conditional enter?**  No.  The module imports only
  `RiemannHypothesis.KoksmaSharp` (hence `KoksmaVariation` and `Discrepancy`), uses no `Prop` of
  this repository that is not proved, and `#print axioms` on each exported theorem gives exactly
  `propext`, `Classical.choice`, `Quot.sound`.
* **Is the discrepancy the repository's own?**  Yes: `discrepancy` of
  `RiemannHypothesis/Discrepancy.lean`, the supremum over all `[a, b) ⊆ [0, 1]` of
  `|#{n < N : ⟨xₙ⟩ ∈ [a, b)}/N − (b − a)|`; the statements are pinned against it in
  `scripts/revalidation.lean`, and the quadrature corollaries are pinned against the Koksma
  inequalities of the repository.
