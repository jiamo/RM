# M2-LARGE-SIEVE-SQUAREFREE — Montgomery's sieve over squarefree moduli

## Task

Close the open boundary of `M2-LARGE-SIEVE-SIFTED`: extend the sieve consequence of the large
sieve from *prime* moduli to all *squarefree* moduli `q ≤ Q`, with the multiplicative sifting
density `∏_{p ∣ q} (p − w p)/(w p)`.

## Lean declarations

New module `RiemannHypothesis/LargeSieveSquarefree.lean`
(namespace `RiemannHypothesis.LargeSieveSquarefree`), imported by `RiemannHypothesis.lean`:

* `expSum A x = ∑_{n ∈ A} e(n x)`, `redSq A q = ∑_{b < q, (b,q)=1} ‖expSum A (b/q)‖²`,
  `fiberSum A p x r = ∑_{n ∈ A, n ≡ r (p)} e(n x)`, `squarefreeUpTo Q = {q : 1 ≤ q ≤ Q, q squarefree}`;
* `sum_normSq_dft` — Parseval's identity for the discrete Fourier transform of an arbitrary
  complex-valued function on `ℤ/q`: `∑_{c<q} ‖∑_{r<q} g r e(rc/q)‖² = q ∑_{r<q} ‖g r‖²`;
* `expSum_add_div_eq`, `sum_fiberSum`, `fiberSum_eq_zero` — the fibre decomposition of `A` mod `p`;
* `sq_norm_expSum_mul_le_sum_prime` — the prime step at an arbitrary real shift `x`:
  `‖S(x)‖² (p − w)/w ≤ ∑_{0<c<p} ‖S(c/p + x)‖²` when `A` meets at most `w` classes mod `p`;
* `redSq_prime_mul_le` — multiplicativity: `((p − w)/w) · F(m) ≤ F(p m)` for `p` prime, `p ∤ m`;
* `redSq_one` — `F(1) = |A|²`;
* `sq_card_mul_prod_le_redSq` — for squarefree `q`, `|A|² ∏_{p ∣ q} (p − w p)/(w p) ≤ F(q)`;
* `card_le_sifted_squarefree` — **Montgomery's sieve**:
  `|A| ∑_{q ≤ Q squarefree} ∏_{p ∣ q} (p − w p)/(w p) ≤ Q² + π N`;
* `card_le_sifted_squarefree_half` — `|A| · #{q ≤ Q squarefree} ≤ Q² + π N` for a set meeting at
  most half the classes modulo every prime `p ≤ Q`;
* `card_filter_sq_dvd_le`, `card_not_squarefree_le`, `sum_inv_sq_le`, `card_squarefreeUpTo_ge` —
  at least a quarter of the moduli up to `Q` are squarefree;
* `card_mul_le_of_sifted_half`, `card_le_of_sifted_half_sqrt` — `|A| Q/4 ≤ Q² + π N`, and, at
  `Q = ⌊√N⌋`, `|A| ≤ 34 √N`.

## The proof

`F(q) = ∑_{(b,q)=1} ‖S(b/q)‖²` is bounded above, summed over all `q ≤ Q`, by
`(Q² + π N)|A|` — that is `large_sieve_farey_pairs` of `M2-LARGE-SIEVE-FAREY` applied to the
indicator of `A`. Everything else is a lower bound for `F(q)`.

For the lower bound, write a squarefree `q` as `p m` with `p = q.minFac` and `p ∤ m`. The numbers
`b = (c m + d p) mod p m` with `0 < c < p` and `d` reduced mod `m` are distinct reduced residues
mod `p m` (`hmaps`, `hinj` inside `redSq_prime_mul_le`, by the Chinese remainder theorem in the
explicit form `b ≡ c m (p)`, `b ≡ d p (m)`), and `b/(p m) ≡ c/p + d/m (mod 1)`. Grouping `A` by
its residue mod `p` writes `S(c/p + d/m)` as the discrete Fourier transform at `c` of the fibre
sums `g r`, which are supported on the `w p` classes that `A` meets mod `p`; Parseval
(`sum_normSq_dft`) and Cauchy–Schwarz over those classes give
`∑_{0<c<p} ‖S(c/p + d/m)‖² ≥ ((p − w p)/(w p)) ‖S(d/m)‖²`. Summing over `d` gives
`redSq_prime_mul_le`, and strong induction on `q` (with `q.primeFactors = insert p m.primeFactors`)
gives `sq_card_mul_prod_le_redSq`. Restricting the Farey sum to the squarefree `q ≤ Q` and
cancelling one factor `|A|` gives `card_le_sifted_squarefree`; taking
`w p = max 1 #(A mod p)`, which satisfies `2 w p ≤ p`, makes every factor `(p − w p)/(w p) ≥ 1`,
so the sifting sum is at least the number of squarefree `q ≤ Q`, which is
`card_le_sifted_squarefree_half`.

The count of squarefree moduli is elementary: a non-squarefree `q ∈ [1, Q]` is a multiple of `d²`
for some `d ∈ [2, Q]` (take `d` a prime with `d² ∣ q`), the multiples of `d²` in `[1, Q]` number at
most `Q/d²` (`card_filter_sq_dvd_le`, by the injection `q ↦ q/d²` into `[1, Q/d²]`), and
`∑_{2 ≤ d ≤ Q} 1/d² ≤ 3/4 − 1/Q` by the telescoping bound `1/d² ≤ 1/(d(d−1)) = 1/(d−1) − 1/d`
applied from `d = 3` on (`sum_inv_sq_le`, by induction). Hence at most `(3/4)Q` of the moduli are
not squarefree and `card_squarefreeUpTo_ge` gives `#{q ≤ Q squarefree} ≥ Q/4`. With
`Q = ⌊√N⌋ ≥ √N/2` and `Q² ≤ N`, the sieve gives `|A| (√N/8) ≤ (1 + π) N`, that is
`|A| ≤ 8(1 + π)√N ≤ 34 √N` (`card_le_of_sifted_half_sqrt`).

## Commands and observed output

```text
$ lake build RiemannHypothesis.LargeSieveSquarefree
Build completed successfully (8725 jobs).

$ lake build
Build completed successfully.

$ ./scripts/audit.sh
OK
```

`#print axioms` for `sum_normSq_dft`, `sq_norm_expSum_mul_le_sum_prime`, `redSq_prime_mul_le`,
`sq_card_mul_prod_le_redSq`, `card_le_sifted_squarefree`, `card_le_sifted_squarefree_half`,
`card_squarefreeUpTo_ge` and `card_le_of_sifted_half_sqrt`
reports exactly `[propext, Classical.choice, Quot.sound]` (checked by `scripts/audit.sh`).

## What is supported

Montgomery's form of the large sieve for sifted sets, with the multiplicative sifting density over
squarefree moduli, is proved in Lean, unconditionally, with no `sorry` and with no unproved `Prop`
of this repository among its hypotheses.

## What is not proved

* The constant is `Q² + π N`, not the sharp `Q² + N − 1`; the factor `π` is inherited from the
  Sobolev step of `M2-LARGE-SIEVE-GALLAGHER`.
* Only squarefree moduli are treated. The sifting density at a prime power is not proved: the
  large sieve is applied at reduced fractions and the inductive step uses `p ∤ m`.
* No Selberg-type optimization of the sifting weights, no character form of the large sieve, and
  no Bombieri–Vinogradov consequence.
* The constant `34` in the `√N` bound is generous: it comes from the factor `π` in the large
  sieve, from the crude count `#{q ≤ Q squarefree} ≥ Q/4` (the truth is `6Q/π² + O(√Q)`), and from
  `⌊√N⌋ ≥ √N/2`. No sharp constant is claimed.
* Nothing about `ζ` follows: no mean value theorem is improved, no zero-density estimate is
  obtained and no zero is located.

## Adversarial revalidation: M2-LARGE-SIEVE-SQUAREFREE

Second, independent pass over the claims of the row.

1. **Claim mode.** All six results are `theorem`s proved in this repository, not `def ... : Prop`
   statements and not mathlib results. The only external input is mathlib plus this repository's
   own `large_sieve_farey_pairs` (`M2-LARGE-SIEVE-FAREY`), itself a proved theorem. The exact
   statements are pinned in `scripts/revalidation.lean` under the heading
   `M2-LARGE-SIEVE-SQUAREFREE`, with the repository declaration supplied as the proof term, so a
   rename or a weakening breaks `./scripts/audit.sh`.
2. **The `√N` corollary, checked by hand.** `|A| · Q/4 ≤ Q² + π N` with `Q = ⌊√N⌋`: here
   `Q² ≤ N` and `π ≤ 3.15`, so the right side is at most `4.15 N`, and `Q ≥ √N − 1 ≥ √N/2`
   because `√N ≥ 2` for `N ≥ 4`; hence `|A| · √N/8 ≤ 4.15 N` and `|A| ≤ 33.2 √N ≤ 34 √N`. The
   count `#{q ≤ Q squarefree} ≥ Q/4` is checked against the truth `6Q/π² ≈ 0.608 Q`: the claim is
   weaker, as it must be. At `Q = 2` the claim reads `#{1, 2} = 2 ≥ 0.5`, and at `Q = 1` it reads
   `1 ≥ 0.25`; both hold with room, and the telescoping bound is checked at `n = 2`:
   `1/4 ≤ 3/4 − 1/2`, an equality.
3. **Constants, checked by hand.** The right-hand side `Q² + π N` is exactly the constant of
   `large_sieve_farey_pairs`, multiplied by `∑_{n<N} ‖a n‖² = |A|` for the indicator of `A`, after
   cancelling one factor `|A|`; no constant is invented in this module. In the prime step, Parseval
   gives `∑_{c<p} ‖S(c/p+x)‖² = p T` with `T = ∑_{r<p} ‖g r‖²`, Cauchy–Schwarz gives
   `‖S(x)‖² ≤ w T`, so `∑_{0<c<p} ‖S(c/p+x)‖² = p T − ‖S(x)‖² ≥ (p/w − 1)‖S(x)‖²`, which is the
   stated `((p − w)/w)‖S(x)‖²` — the same arithmetic as in the prime-modulus row, now with a
   complex-valued `g`. Sanity check of the shape of the conclusion: for `w p = (p+1)/2` and
   `q = 1` the product is empty, the density is `1` and the inequality reduces to
   `|A|² ≤ F(1) = |A|²`, an equality (`redSq_one`).
4. **Hypotheses: load-bearing, not vacuous.** `hq : Squarefree q` is used twice — to get `p ∤ m`
   in the induction step (a repeated prime factor would make the fractions `c/p + d/m` collide)
   and to make `q.primeFactors` the exact factorization. `hwle : w p ≤ p` is what makes the factor
   `(p − w p)/(w p)` nonnegative, so that the induction may multiply the inductive hypothesis by
   it; dropping it makes the statement false, since a negative factor reverses the inequality.
   `hwpos : 0 < w p` prevents division by zero. `hQ : 2 ≤ Q` is inherited from the Farey row.
   The hypotheses are satisfiable and the conclusions are not vacuous: `card_le_sifted_squarefree_half`
   has no free weight at all, and its hypothesis holds, for instance, for the set of squares below
   `N` at odd primes.
5. **Attribution.** The statement proved here is the sieve form of the large sieve associated with
   Montgomery (1968); the multiplicativity of the sifting density is the standard Chinese-remainder
   argument. It is proved here, not cited: no step is imported from the literature.
6. **Boundary.** The row is `DONE_WEAK`, and the open boundary above states what is missing
   (sharp constant, prime powers, character form, no consequence for `ζ`). No reduction to an open
   conjecture is involved.
