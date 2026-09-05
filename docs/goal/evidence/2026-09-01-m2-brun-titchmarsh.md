# M2-BRUN-TITCHMARSH — the primes in a short interval, from the squarefree large sieve

## Task

Draw the first genuine sieve consequence of Montgomery's inequality of
`M2-LARGE-SIEVE-SQUAREFREE`: an upper bound of the right order of magnitude, uniform in the
starting point, for the number of primes in an interval `[x, x + y)`.

## Lean declarations

New module `RiemannHypothesis/BrunTitchmarsh.lean`
(namespace `RiemannHypothesis.BrunTitchmarsh`), imported by `RiemannHypothesis.lean`:

* `siftSum Q = ∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p − 1)` — the sifting sum of the large sieve at
  the weights `w p = p − 1`;
* `inv_le_prod_inv_sub_one`, `sum_inv_squarefree_le_siftSum` —
  `∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`;
* `harmonic_cast`, `log_le_sum_inv`, `sum_inv_le_log_add_one` —
  `log Q ≤ ∑_{n ≤ Q} 1/n ≤ log Q + 1`, from mathlib's `harmonic`;
* `sum_inv_multiples_le` — `∑_{n ≤ Q, d² ∣ n} 1/n ≤ (log Q + 1)/d²`;
* `sum_biUnion_le_sum_sum` — subadditivity of a sum of nonnegative terms over a `biUnion`;
* `sum_inv_not_squarefree_le` — `∑_{n ≤ Q, n not squarefree} 1/n ≤ (3/4)(log Q + 1)`;
* `quarter_log_le_sum_inv_squarefree`, `quarter_log_le_siftSum` —
  `(log Q)/4 − 3/4 ≤ ∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`;
* `card_mul_siftSum_le` — the sieve for a set `A ⊆ [0, N)` avoiding one residue class modulo
  every prime `p ≤ Q`: `|A| · siftSum Q ≤ Q² + π N`;
* `card_primes_Ico_eq`, `shifted_primes_avoid`, `half_log_sub_log_two_le_log_sqrt` — the three
  ingredients of the application;
* `card_primes_Ico_le` — **Brun–Titchmarsh with a non-optimal constant**: for every `x` and every
  `y` with `log y ≥ 24`,
  `#{p prime : x ≤ p < x + y} ≤ 70 y / log y + √y + 1`;
* `card_primes_range_le` — its case `x = 0`, a Chebyshev-type upper bound
  `π(N) ≤ 70 N / log N + √N + 1`; in particular the primes have density zero.

## The proof

**The sifting sum.** A squarefree `q` is the product of its prime factors, so
`1/q = ∏_{p ∣ q} 1/p ≤ ∏_{p ∣ q} 1/(p − 1)`; summing over the squarefree `q ≤ Q` gives
`∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`.

**The squarefree harmonic sum.** The full harmonic sum satisfies `log Q ≤ ∑_{n ≤ Q} 1/n` (mathlib's
`log_add_one_le_harmonic`, together with the monotonicity of `log`). The non-squarefree `n ≤ Q` are
covered by the multiples of `d²` for `d ∈ [2, Q]`; the multiples of `d²` in `[1, Q]` are exactly the
`d² m` with `m ≤ Q/d²`, so their reciprocals sum to `(1/d²) ∑_{m ≤ Q/d²} 1/m ≤ (log Q + 1)/d²`
(mathlib's `harmonic_le_one_add_log`). Summing the union bound over `d` and inserting the
telescoping estimate `∑_{2 ≤ d ≤ Q} 1/d² ≤ 3/4 − 1/Q` of `M2-LARGE-SIEVE-SQUAREFREE` gives
`∑_{n ≤ Q, n not squarefree} 1/n ≤ (3/4)(log Q + 1)`, hence
`∑_{q ≤ Q squarefree} 1/q ≥ log Q − (3/4)(log Q + 1) = (log Q)/4 − 3/4`.

**The sieve at `w p = p − 1`.** If `A` avoids one residue class `c` modulo the prime `p`, then
`A mod p` is contained in `(range p).erase c`, so `#(A mod p) ≤ p − 1`. Montgomery's inequality
`card_le_sifted_squarefree` at these weights has density
`(p − (p − 1))/(p − 1) = 1/(p − 1)` at each prime factor, so it reads
`|A| · siftSum Q ≤ Q² + π N`.

**The application.** Shifting by `x` identifies the primes of `[x, x + y)` with the `m < y` for
which `x + m` is prime. Split those `m` according to whether `x + m > Q` or not, with
`Q = ⌊√y⌋`. The second class has `m ≤ x + m ≤ Q`, so it contributes at most `Q + 1 ≤ √y + 1`. For
the first class `A`, and a prime `p ≤ Q`, put `c = (p − x mod p) mod p`: if `m ≡ c (mod p)` then
`p ∣ x + m`, and since `x + m` is a prime exceeding `Q ≥ p ≥ 2` this is impossible; so `A` avoids
one class modulo every prime `p ≤ Q` and `|A| · siftSum Q ≤ Q² + π y`.

Finally `y < (Q + 1)² ≤ 4Q²`, so `log Q ≥ (log y)/2 − log 2 > (log y)/2 − 0.6932`; hence
`siftSum Q ≥ (log Q)/4 − 3/4 > (log y)/8 − 0.9233 ≥ 0.08 log y` once `log y ≥ 24`. Since
`Q² ≤ y` and `π ≤ 3.15`, the right-hand side is at most `4.15 y`, so
`|A| ≤ 4.15 y / (0.08 log y) < 52 y / log y ≤ 70 y / log y`.

## Commands and observed output

```text
$ lake build RiemannHypothesis.BrunTitchmarsh
Build completed successfully (8726 jobs).

$ lake build
Build completed successfully.

$ ./scripts/audit.sh
OK
```

`#print axioms` for `sum_inv_squarefree_le_siftSum`, `sum_inv_not_squarefree_le`,
`quarter_log_le_siftSum`, `card_mul_siftSum_le`, `card_primes_Ico_le` and `card_primes_range_le`
reports exactly `[propext, Classical.choice, Quot.sound]` (checked by `scripts/audit.sh`).

## What is supported

A Brun–Titchmarsh inequality — an upper bound of the correct order `y / log y`, uniform in the
starting point `x`, for the number of primes in `[x, x + y)` — is proved in Lean, unconditionally,
with no `sorry` and with no unproved `Prop` of this repository among its hypotheses. It is deduced
from this repository's own large sieve, not imported.

## What is not proved

* The constant `70` is far from the sharp `2` of Montgomery–Vaughan, and from the `2 + o(1)` of the
  classical Brun–Titchmarsh theorem. It collects the factor `π` of this repository's large sieve,
  the crude bound `∑_{q ≤ Q squarefree} 1/q ≥ (log Q)/4 − 3/4` (the truth is
  `(6/π²) log Q + O(1)`), and the choice `Q = ⌊√y⌋`.
* The threshold `log y ≥ 24` is an artefact of the same crude bounds; nothing is claimed for
  `y < e²⁴`.
* Only the interval form is proved. The arithmetic-progression form
  `π(x + y; q, a) − π(x; q, a) ≪ y / (φ(q) log(y/q))` is not: it needs the sieve at moduli coprime
  to `q`.
* No Bombieri–Vinogradov consequence, and no Selberg-type optimization of the sifting weights.
* Nothing about `ζ` follows: no zero-free region, no zero-density estimate, no mean value theorem,
  and no zero is located.

## Adversarial revalidation: M2-BRUN-TITCHMARSH

Second, independent pass over the claims of the row.

1. **Claim mode.** Every result named in the exit criteria is a `theorem` proved in this
   repository — not a `def ... : Prop`, not a hypothesis, not a mathlib result. The external
   inputs are mathlib (the harmonic-number bounds `log_add_one_le_harmonic` and
   `harmonic_le_one_add_log`, `Real.log_two_lt_d9`, `Real.pi_lt_d2`,
   `Nat.prod_primeFactors_of_squarefree`) and this repository's own
   `card_le_sifted_squarefree` and `sum_inv_sq_le` of `M2-LARGE-SIEVE-SQUAREFREE`, themselves
   proved theorems. The exact statements are pinned in `scripts/revalidation.lean` under the
   heading `M2-BRUN-TITCHMARSH`, with the repository declaration supplied as the proof term, so a
   rename or a weakening breaks `./scripts/audit.sh`.
2. **The final constant, checked by hand.** With `L = log y ≥ 24` and `Q = ⌊√y⌋`:
   `y < (Q+1)² ≤ 4Q²` (using `Q ≥ 2`), so `2 log Q > L − log 4 > L − 1.3863` and
   `log Q > L/2 − 0.6932`. Then `siftSum Q ≥ (log Q)/4 − 3/4 > L/8 − 0.1733 − 0.75 = L/8 − 0.9233`,
   and `L ≥ 24` gives `0.9233 ≤ 0.0385 L`, so `siftSum Q ≥ 0.0865 L ≥ 0.08 L`. The sieve gives
   `|A| · 0.08 L ≤ Q² + π y ≤ y + 3.15 y = 4.15 y`, so `|A| ≤ 51.875 y/L`, comfortably below the
   claimed `70 y/L`; the remaining primes are at most `Q + 1 ≤ √y + 1`. Every inequality has slack,
   and the claimed constant is deliberately not the best this argument gives.
3. **Not vacuous.** The hypothesis `24 ≤ log y` is satisfiable (any `y ≥ e²⁴`), and for such `y`
   the conclusion is a genuine restriction: `70 y/log y + √y + 1` is far below the trivial bound
   `y`. The sieve input `card_mul_siftSum_le` is likewise non-vacuous — its hypothesis is exhibited
   in use, in `card_primes_Ico_le`, by an explicit residue class. The statement is uniform in `x`:
   `x` is universally quantified and no bound on `x` in terms of `y` is imposed, which is the whole
   point of a Brun–Titchmarsh inequality (`π(x + y) − π(x) ≤ π(y)` is *false* in general, and is
   not what is proved here).
4. **Hypotheses: load-bearing.** In `card_mul_siftSum_le`, `hQ : 2 ≤ Q` is inherited from the Farey
   row; `havoid` is what bounds `#(A mod p)` by `p − 1`, and without it the factor
   `(p − w p)/(w p)` is not `1/(p − 1)`. In `card_primes_Ico_le`, `24 ≤ log y` is used twice: to get
   `y ≥ 4`, hence `Q ≥ 2`, and to absorb the additive constant `0.9233` into `L/8`. In
   `shifted_primes_avoid` the hypothesis `Q < x + m` is essential — for a prime `x + m ≤ Q` the
   class is *not* avoided, since `p = x + m` divides `x + m`; this is exactly why the primes below
   `Q` are counted separately, and it is why the `√y` term appears in the conclusion.
5. **Direction of the estimate.** The result is an *upper* bound only. It gives no lower bound for
   the number of primes in an interval, and in particular says nothing about the existence of
   primes in `[x, x + y)`; a lower bound of the same order is not accessible to a sieve.
6. **Attribution.** The deduction of a Brun–Titchmarsh inequality from the large sieve is
   Montgomery's; the sharp form is Montgomery–Vaughan (1973). What is proved here is the
   deduction with an explicit but non-optimal constant. It is proved, not cited: no step is
   imported from the literature.
7. **Boundary.** The row is `DONE_WEAK`, and the open boundary above states what is missing (sharp
   constant, threshold on `y`, progression form, no consequence for `ζ`). No reduction to an open
   conjecture is involved.
