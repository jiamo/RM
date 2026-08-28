# M1-WEYL-DIFFERENCING — van der Corput's A process

Date: 2026-08-26
File: `RiemannHypothesis/WeylDifferencing.lean`

## Claim

For `z : ℤ → ℂ` vanishing outside `[0, N)`, write `S = ∑_{0 ≤ n < N} z n` and

    corr z N k = ∑_{0 ≤ n < N} z (n + k) · conj (z n).

* **the van der Corput inequality** (`mul_normSq_sum_le`) — for every `H ≥ 1`,

      H ‖S‖² ≤ (N + H − 1) · ∑_{|k| < H} ‖corr z N k‖ ;

* **the weighted (Fejér) form** (`mul_normSq_sum_le_weighted`) — the sharper classical
  statement, with the weights the double sum really carries,

      H² ‖S‖² ≤ (N + H − 1) · ∑_{|k| < H} (H − |k|) ‖corr z N k‖ ;

* **the arithmetic form** (`norm_sq_sum_e2pi_le`) — with `e(θ) = exp(2πiθ)` and an arbitrary
  phase `f : ℤ → ℝ`,

      H ‖∑_{0 ≤ n < N} e(f n)‖²
        ≤ (N + H − 1) · (N + 2 ∑_{0 < k < H} ‖∑_{0 ≤ n < N−k} e(f(n+k) − f(n))‖).

The last is the shape in which the A process is used: the original sum is replaced by the
*differenced* sums, whose phases `f(· + k) − f(·)` move `k` times as fast.

## Proof

Three elementary steps; there is no arithmetic in the first two statements at all.

1. *Averaging over shifted windows* (`sum_blockSum`).  With the block sum
   `B n = ∑_{h < H} z (n + h)` and the window `I = [1 − H, N)`, every shift of `I` by
   `h < H` contains `[0, N)`, so `∑_{n ∈ I} B n = H · S`.
2. *Cauchy–Schwarz* (`sq_sum_le_card_mul_sum_sq`): `(∑_{n ∈ I} ‖B n‖)² ≤ #I · ∑_{n ∈ I} ‖B n‖²`,
   and `#I = N + H − 1`.
3. *Expanding the square* (`sum_normSq_blockSum`).  `∑_{n ∈ I} ‖B n‖² = ∑_{h₁,h₂ < H} corr z N
   (h₁ − h₂)`: for fixed `h₁, h₂` the substitution `m = n + h₂` turns the inner sum into a
   correlation, the window again being large enough to see the whole support.  Counting the
   shifts finishes: at most `H` pairs give a given `k` (`sum_product_norm_corr_le`), and exactly
   `H − |k|` do (`card_filter_sub_eq`, `sum_product_norm_corr_eq`), which is the difference
   between the two forms.

For the arithmetic corollary the sequence is `z n = e(f n)` on `[0, N)` and `0` elsewhere.  Then
`corr z N 0 = N` (every term is `|e|² = 1`), `corr z N k = ∑_{0 ≤ n < N−k} e(f(n+k) − f(n))` for
`k > 0`, and `corr z N (−k) = conj (corr z N k)` (`corr_neg`), so the two-sided sum folds to the
diagonal plus twice the positive shifts (`sum_Ioo_norm_corr_eq`).

## Why this row exists

`M1-VAN-DER-CORPUT` and `M1-KUSMIN-LANDAU` prove the first-derivative tests, for integrals and
for sums.  Both are silent when the phase moves *slowly*: Kusmin–Landau needs `f'` to stay away
from the integers.  The A process is the manoeuvre that removes that restriction — it trades a
sum for its differences, whose phases move faster — and it is one of the two processes (with `B`,
Poisson summation) out of which the exponent pairs of the theory of `ζ` are built.  Both open
boundaries named it explicitly as missing.

## Scope, and what is *not* claimed

* Only the A process is proved.  The B process (Poisson summation) is not, nor is the third
  derivative test; those are what the exponent pair `(1/6, 2/3)` and hence the Weyl bound
  `ζ(1/2 + it) ≪ t^{1/6+ε}` require.
* The process is not iterated here, and it is not combined with Kusmin–Landau: no choice of `H`
  is made, and no bound for a specific phase is derived.
* No consequence for `ζ` is drawn in the module: no subconvexity bound, no approximate functional
  equation, no density estimate.  The row is infrastructure.
* The length factor is `N + H − 1`, the exact cardinality of the window, rather than the usual
  `N + H`; the constants are otherwise the classical ones.

## Adversarial revalidation: M1-WEYL-DIFFERENCING

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.WeylDifferencing` succeeds, the file contains no `sorry`, and it triggers no
  linter warning.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the three main
  statements (checked in `scripts/audit.sh`).
* The statements are pinned in `scripts/revalidation.lean`, so a change of statement breaks the
  audit.
* The statements are not vacuous.  The support hypothesis is satisfiable by construction (the
  arithmetic corollary constructs such a `z` from an arbitrary phase and quantifies over *all*
  `f : ℤ → ℝ` and all `N`), and the inequality is nontrivial: for a sum of `N` unimodular terms
  the trivial bound is `‖S‖² ≤ N²`, while the A process gives `‖S‖² ≤ (N + H − 1)N/H` plus the
  differenced terms — already `‖S‖² ≪ N²/H` when the differenced sums exhibit cancellation.
* The inequality is not an equality in disguise: taking `z n = 1` on `[0, N)` gives
  `S = N`, `corr z N k = N − |k|`, and the two sides of `mul_normSq_sum_le` are `H N²` and
  `(N + H − 1)(2 ∑_{0<k<H}(N − k) + N)`, so the estimate is genuinely lossy and its content is
  the *direction* of the inequality.
* The statements are unconditional: no unproved `Prop` of this repository occurs as a hypothesis,
  so `docs/goal/conditional-theorems.txt` gains no new entry.
