# M2-LARGE-SIEVE-SIFTED — the large sieve for sifted sets

Date: 2026-08-30
File: `RiemannHypothesis/LargeSieveSifted.lean`

## Claim

Let `A ⊆ [0, N)` be a finite set of integers, `e(x) = exp(2πix)`, and

    indSum A q b = ∑_{n ∈ A} e(n b / q),      fiberCard A q r = #{n ∈ A : n ≡ r mod q}.

* `sum_e2pi_mul_div` — **orthogonality of the additive characters modulo `q`**: for `q ≥ 1` and
  `m : ℤ`,

      ∑_{b < q} e(m b / q) = q if q ∣ m, and 0 otherwise.

* `sum_normSq_indSum` — **Parseval's identity**:

      ∑_{b < q} ‖indSum A q b‖² = q ∑_{r < q} (fiberCard A q r)².

* `sq_card_le_mul_sum_sq_fiber` — Cauchy–Schwarz over the classes actually met: if `A` meets at
  most `w` classes modulo `q`, then `|A|² ≤ w ∑_r (fiberCard A q r)²`.

* `sq_card_mul_le_sum_prime` — **the lower bound at a prime modulus**: for a prime `p` and
  `w ≥ 1` as above,

      ∑_{0 < b < p} ‖indSum A p b‖² ≥ |A|² (p − w)/w.

* `card_le_sifted` — **Montgomery's inequality**: if `A ⊆ [0, N)` meets at most `w p` classes
  modulo every prime `p ≤ Q`, and `Q ≥ 2`, then

      |A| ∑_{p ≤ Q} (p − w p)/(w p) ≤ Q² + π N.

* `card_le_sifted_half` — the case `2 w p ≤ p`: a set meeting at most half the classes modulo
  every prime `p ≤ Q` satisfies `|A| · #{p ≤ Q} ≤ Q² + π N`.

* `card_image_mod_le_of_isSquare` — the squares meet at most `(p + 1)/2` classes modulo an odd
  prime `p`.

* `card_le_of_isSquare`, `card_squares_lt_le` — hence, for a set of squares in `[0, N)`, and in
  particular for the set of *all* squares below `N`,

      |A| · #{odd primes p ≤ Q} ≤ 3 (Q² + π N).

## Proof

Apply `large_sieve_farey_pairs` of `M2-LARGE-SIEVE-FAREY` with `a` the indicator of `A`.  Since
`A ⊆ [0, N)`, the right-hand side `(Q² + π N) ∑_{n < N} ‖a n‖²` is `(Q² + π N)|A|`, and the
exponential sum at `b/q` is `indSum A q b`.

`sum_e2pi_mul_div` is the geometric sum `∑_{b < q} z^b` with `z = e(m/q)`: `z^q = e(m) = 1`, so the
sum is `q` if `z = 1` and `(z^q − 1)/(z − 1) = 0` otherwise, and `e2pi_div_eq_one_iff` identifies
`z = 1` with `q ∣ m` through `Complex.exp_eq_one_iff`.

For Parseval, `‖indSum A q b‖² = indSum A q b · conj(indSum A q b)` expands as a double sum over
`A × A` of `e((n − n') b / q)`; summing over `b < q` and using orthogonality leaves `q` times the
number of pairs congruent modulo `q`, which is `q ∑_r (fiberCard A q r)²` after grouping the pairs
by the common class.  The term `b = 0` of the identity is `|A|²`.

`sq_card_le_mul_sum_sq_fiber` is `sq_sum_le_card_mul_sum_sq` applied over the image of `A` modulo
`q`: the fibre counts vanish off that image, so `|A| = ∑_{r ∈ image} fiberCard` and
`|A|² ≤ #image · ∑_r (fiberCard)² ≤ w ∑_r (fiberCard)²`.

At a prime modulus the reduced residues are `{1, …, p − 1}` (`filter_coprime_prime`), so
subtracting the term `b = 0` from Parseval gives
`∑_{0 < b < p} ‖indSum A p b‖² = p Σ − |A|²` with `Σ = ∑_r (fiberCard)² ≥ |A|²/w`, which is at
least `|A|²(p − w)/w`.

Summing this over the primes `p ≤ Q` — a subfamily of the moduli of the Farey large sieve, all
terms being nonnegative — gives `|A|² L ≤ (Q² + π N)|A|`, and cancelling one factor `|A|` (the
case `A = ∅` being trivial) gives `card_le_sifted`.

For `card_le_sifted_half` take `w p = max 1 (#classes met)`, for which `2 w p ≤ p` and hence
`(p − w p)/w p ≥ 1`, so `L ≥ #{p ≤ Q}`.

For the squares, if `n = s²` then `n ≡ x² (mod p)` with `x = s mod p`, and `x` may be replaced by
`p − x`, because `x² − (p − x)² = p(2x − p)` is divisible by `p`; one of `x`, `p − x` is smaller
than `(p + 1)/2` when `p` is odd, so the classes met are contained in the image of
`{0, …, (p − 1)/2}` under squaring, of size at most `(p + 1)/2`.  Feeding
`w p = (p + 1)/2` for odd `p` (and the trivial `w 2 = 2`) into `card_le_sifted`, each odd prime
contributes `(p − 1)/(p + 1) ≥ 1/3`.

## Why this row exists

The open boundary of `M2-LARGE-SIEVE-FAREY` records that the Farey form is "the large sieve for
exponential sums at rational points only", with no sieve consequence drawn.  This row draws the
first one: an upper bound for a set defined by residue conditions, which is the shape in which the
large sieve is actually used in analytic number theory.  It also puts the Parseval and
orthogonality lemmas for additive characters into the repository, which the character form of the
large sieve will need.

## Scope, and what is *not* claimed

* Only **prime** moduli are used.  The full arithmetic large sieve sums over the squarefree
  `q ≤ Q`, where the sifting density is multiplicative by the Chinese remainder theorem; that step
  is not formalized here.  Without it the sifting function is a sum over primes, which is weaker,
  and no bound of Selberg, Brun–Titchmarsh or Bombieri–Vinogradov strength follows.
* The constant `Q² + π N` carries the factor `π` inherited from `M2-LARGE-SIEVE-GALLAGHER`; it is
  not the sharp `Q² + N − 1` of Selberg and Montgomery–Vaughan.
* The character form of the large sieve is still not proved, as `M2-LARGE-SIEVE-FAREY` records.
* For the squares the bound obtained is **weaker than the trivial `√N`**; the example is there to
  exhibit a natural set satisfying the hypothesis, not to improve on counting squares.
* Nothing about `ζ` follows: no mean value theorem is improved, no zero-density estimate is
  obtained and no zero is located.

## Adversarial revalidation: M2-LARGE-SIEVE-SIFTED

* The module is imported by `RiemannHypothesis.lean`, `lake build` succeeds, the file contains no
  `sorry`, and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the nine
  statements listed above; the checks are in `scripts/audit.sh`.
* The main statements are pinned in `scripts/revalidation.lean`, with `indSum`, `fiberCard` and
  `primesUpTo` named by their fully qualified constants and every hypothesis written out.
* Nothing is vacuous.  `card_squares_lt_le` has no hypothesis on the set at all — it is a
  statement about the squares below `N` — so the sieve is applied to a set that exists, and
  `card_image_mod_le_of_isSquare` shows the Diophantine hypothesis of the sieve is satisfiable.
  The inequality of `card_le_sifted` is not vacuous either: for `w p ≤ p/2` the sifting function
  is at least the number of primes up to `Q`, which grows, so the bound is a genuine restriction
  on `|A|`.
* The hypotheses are load-bearing.  `Q ≥ 2` is what `large_sieve_farey_pairs` requires; `w p > 0`
  is used to divide by `w p`; `A ⊆ [0, N)` is what identifies the right-hand side with `|A|`.  The
  residue hypothesis cannot be dropped: for `A = [0, N)` itself every class is met and the sifting
  function is `0`.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.
