# M2-BRUN-TITCHMARSH — Brun–Titchmarsh in arithmetic progressions

## Task

Close the item of the open boundary of `M2-BRUN-TITCHMARSH` that reads *"Only the interval form
is proved: the arithmetic-progression form … is not, since it needs the sieve at moduli coprime
to `q`."* The sieve at moduli coprime to `q` is built, a lower bound for its sifting sum is
proved, and the progression form of Brun–Titchmarsh is deduced with an explicit constant.

## Lean declarations

New file `RiemannHypothesis/BrunTitchmarshProgressions.lean` (namespace
`RiemannHypothesis.BrunTitchmarsh`), imported by `RiemannHypothesis.lean`:

* `siftSumCoprime q Q` — the sifting sum of the large sieve at the weights `w p = p − 1` for
  `p ∤ q` and `w p = p` for `p ∣ q`, that is `∑_{d ≤ Q squarefree, (d,q) = 1} ∏_{p ∣ d} 1/(p − 1)`;
* `coprime_harmonic_le_siftSumCoprime` — `∑_{n ≤ Q, (n,q) = 1} 1/n ≤ siftSumCoprime q Q`;
* `Icc_one_eq_Ico_one_succ`, `block_coprime_card` — a block of `q` consecutive integers contains
  exactly `φ(q)` integers coprime to `q`;
* `totient_mul_harmonic_le_coprime_harmonic` — the block bound
  `(φ(q)/q) ∑_{j ≤ J} 1/j ≤ ∑_{n ≤ J q, (n,q) = 1} 1/n`, whence
  `totient_log_div_le_siftSumCoprime`, `(φ(q)/q) log ⌊Q/q⌋ ≤ siftSumCoprime q Q`;
* `qPart`, `qPart_pos`, `qPart_dvd`, `primeFactors_qPart_subset`, `coprime_div_qPart` — the
  `q`-part of an integer and the splitting `n = m · k` with `(m, q) = 1` and every prime factor
  of `k` dividing `q`;
* `sum_inv_le_coprime_mul_smooth`, `sum_inv_smooth_le`, `prod_primeFactors_self_div_sub_one` —
  the resulting factorization of the harmonic sum and the Euler factor
  `∏_{p ∣ q} p/(p − 1) = q/φ(q)`;
* `totient_log_le_coprime_harmonic` — `(φ(q)/q) log Q ≤ ∑_{n ≤ Q, (n,q) = 1} 1/n`;
* `totient_log_le_siftSumCoprime` — `(φ(q)/q) log Q ≤ siftSumCoprime q Q`;
* `card_mul_siftSumCoprime_le` — the sieve: a set `A ⊆ [0, N)` that avoids one residue class
  modulo every prime `p ≤ Q` not dividing `q` satisfies
  `|A| · siftSumCoprime q Q ≤ Q² + π N`;
* `modOffset`, `modOffset_lt`, `add_modOffset_mod`, `exists_param` — the reparametrization of a
  progression: every `n ≥ x` with `n ≡ a (mod q)` is `x + r + q t` for the least shift `r < q`
  with `x + r ≡ a (mod q)`;
* `progression_avoid` — for a prime `p ≤ Q` with `p ∤ q`, the parameters `t` for which
  `b + q t` is a prime exceeding `Q` avoid one residue class modulo `p`;
* `card_primes_Ico_mod_le` — **Brun–Titchmarsh in progressions**.

Each is pinned as an `example … := <declaration>` in `scripts/revalidation.lean`.

## The statement

With `Y = ⌊y/q⌋ + 1` and `Q = ⌊√Y⌋`, for every `q ≥ 1`, every residue `a < q`, and all `x`, `y`
with `Q ≥ 2`,

```
#{ n prime : x ≤ n < x + y, n ≡ a (mod q) } ≤ 4.15 q Y / (φ(q) log Q) + √Y + 1.
```

## The proof

**The sieve.** `card_le_sifted_squarefree` of `M2-LARGE-SIEVE-SQUAREFREE` is instantiated at the
weights `w p = p` for `p ∣ q` and `w p = p − 1` otherwise. For a squarefree `d ≤ Q` not coprime
to `q` there is a prime `p ∣ gcd(d, q)`, and the corresponding factor `(p − w p)/w p` vanishes,
so the whole product vanishes; the squarefree `d` coprime to `q` contribute exactly
`∏_{p ∣ d} 1/(p − 1)`. The sifting sum of Montgomery's inequality is therefore
`siftSumCoprime q Q`.

**The sifting sum from below.** The radical of an `n ≤ Q` coprime to `q` is squarefree, coprime
to `q`, at most `n`, and has the same prime factors as `n`; grouping the `n ≤ Q` into these
radical fibres and applying `sum_inv_primeFactors_eq_le` of the interval row gives
`∑_{n ≤ Q, (n,q) = 1} 1/n ≤ siftSumCoprime q Q`. The left-hand side is bounded below with the
classical constant: every `n ≥ 1` factors uniquely as `n = m · k` where `k = qPart q n` is the
`q`-part of `n` (the product of `p^{v_p(n)}` over the primes `p ∣ q`) and `m = n/k` is coprime
to `q`; both factors are at most `n`, and `n ↦ (m, k)` is injective, so

```
∑_{n ≤ Q} 1/n ≤ (∑_{m ≤ Q, (m,q)=1} 1/m) · (∑_{k ≤ Q, rad k ∣ q} 1/k).
```

The second factor is bounded by grouping the `k` according to their set `S` of prime factors,
which ranges over the subsets of the primes dividing `q`; `sum_inv_primeFactors_eq_le` bounds
each group by `∏_{p ∈ S} 1/(p − 1)`, and summing over the power set gives
`∏_{p ∣ q} (1 + 1/(p − 1)) = ∏_{p ∣ q} p/(p − 1)`, which is `q/φ(q)` by mathlib's
`Nat.totient_mul_prod_primeFactors`. Since `log Q ≤ ∑_{n ≤ Q} 1/n`, this yields
`(φ(q)/q) log Q ≤ ∑_{n ≤ Q, (n,q) = 1} 1/n ≤ siftSumCoprime q Q`. (The cruder block bound,
which each block of `q` consecutive integers contributing exactly `φ(q)` coprime residues gives
as `(φ(q)/q) log ⌊Q/q⌋ ≤ siftSumCoprime q Q`, is retained as
`totient_log_div_le_siftSumCoprime`.)

**The application.** Let `r < q` be the least shift with `x + r ≡ a (mod q)` and `b = x + r`.
Every prime `n ∈ [x, x + y)` with `n ≡ a (mod q)` is `n = b + q t` for a unique parameter
`t < Y = ⌊y/q⌋ + 1` (`exists_param`, via `Nat.modEq_iff_dvd'`), and `t ↦ b + q t` is injective,
so the primes of the progression inject into the parameter set
`T = { t < Y : b + q t prime }`. Split `T` at the sieve level: the parameters with `b + q t ≤ Q`
number at most `Q + 1`, and the rest form a set `A` which, for every prime `p ≤ Q` with `p ∤ q`,
avoids the residue class `t ≡ −b q^{-1} (mod p)` — a `t` in that class would make `p ∣ b + q t`,
impossible for a prime `b + q t > Q ≥ p` (`progression_avoid`, computed in `ZMod p`). The sieve
gives `|A| · siftSumCoprime q Q ≤ Q² + π Y ≤ 4.15 Y` because `Q = ⌊√Y⌋` and `π < 3.15`, and the
lower bound for the sifting sum turns this into
`|A| ≤ 4.15 q Y / (φ(q) log Q)`. Adding back the `Q + 1 ≤ √Y + 1` small parameters gives the
statement.

## Verification

* `lake build RiemannHypothesis.BrunTitchmarshProgressions` — succeeds, with no warning from the
  module.
* No `sorry`; `#print axioms RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_mod_le` gives
  exactly `propext, Classical.choice, Quot.sound`.
* `bash scripts/audit.sh` — ends with `OK`.

## What is *not* proved

The constant `4.15` inherits the factor `π` of this repository's large sieve, exactly as in the
interval form, and the rigid sieve level `Q = ⌊√Y⌋` halves the logarithm: with `Y ≈ y/q` the
bound reads `8.3 y / (φ(q) log(y/q))` up to lower-order terms, against the sharp
`2 y / (φ(q) log(y/q))` of Montgomery–Vaughan. The hypothesis `⌊√Y⌋ ≥ 2` is the analogue of the
threshold `log y ≥ 4` of the interval form. No Bombieri–Vinogradov
consequence is drawn, no Selberg-type optimization of the weights is carried out, and nothing
about `ζ` follows: no zero-free region, no zero-density estimate, no mean value theorem, and no
zero is located.
