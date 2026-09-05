# M2-BRUN-TITCHMARSH — the constant `2π + o(1)`, by optimizing the sieve level

Date: 2026-09-03
File: `RiemannHypothesis/BrunTitchmarshSharp.lean` (new)

## What was open

The open boundary of M2-BRUN-TITCHMARSH named the loss precisely:

> what remains is the factor `π` of this repository's large sieve, in place of the sharp `1`, and
> the rigid choice `Q = ⌊√y⌋`, which loses an additive `log 2`. With the sharp large sieve and
> `Q = √y / log y` the same route gives `2 + o(1)`; with the factor `π` kept and `Q` optimized it
> would give `2π + o(1)`.

The second of those two losses is removed here.  The first is not: it is the constant of the
repository's large sieve, and needs Selberg's majorant or the Montgomery–Vaughan Hilbert
inequality, neither of which is formalized.

## Claim (Lean-checked, no `sorry`)

* `card_primes_Ico_le_of_level` — the sieve at an **arbitrary** level `Q ≥ 2`: uniformly in the
  starting point `x`,

      #{p prime : x ≤ p < x + y} ≤ (Q² + π y)/log Q + Q + 1 .

  (The previous file only had the specialization `Q = ⌊√y⌋`, inlined into its proof.)

* `card_primes_Ico_le_two_pi` — for every `ε > 0` there is a `Y` such that for every `y ≥ Y` and
  every `x`,

      #{p prime : x ≤ p < x + y} ≤ (2π + ε) y / log y .

`2π = 6.283…` replaces the `13` of `card_primes_Ico_le` and the `9` of
`card_primes_Ico_le_of_log_ge_24`, and the additive `√y + 1` disappears into the `ε`.
`card_primes_Ico_le_two_pi_aux` is the same statement for `ε ≤ 1` with the threshold explicit:
`log y ≥ (1000/ε)² + 10⁶` suffices.

* `card_primes_range_le_two_pi` — the case `x = 0`: `π(N) ≤ (2π + ε) N / log N` for all large `N`.

* `card_primes_Ico_mod_le_of_level` (in `RiemannHypothesis/BrunTitchmarshProgressions.lean`, which
  now proves its Brun–Titchmarsh inequality at a free level and recovers the old statement
  `card_primes_Ico_mod_le` as the level `Q = ⌊√Y⌋`) — with `Y = ⌊y/q⌋ + 1`,

      #{p prime : x ≤ p < x + y, p ≡ a mod q} ≤ (Q² + π Y) q / (φ(q) log Q) + Q + 1 .

* `card_primes_Ico_mod_le_two_pi` — the progression form with the constant `2π + ε`: for every
  `ε > 0` there is a `Y₀` with

      #{p prime : x ≤ p < x + y, p ≡ a mod q} ≤ (2π + ε) (q/φ(q)) Y / log Y

  whenever `Y = ⌊y/q⌋ + 1 ≥ Y₀`, uniformly in `x`, in the modulus `q` and in the residue `a`.
  This replaces the constant `4.15` against `log √Y`, that is `8.3` against `log Y`.

## Proof

Run the sieve at `Q = ⌊√y / log y⌋` instead of `⌊√y⌋`.  Write `t = log y`, `s = √y`, `u = √t`.

* `Q ≤ s/t`, so `Q² ≤ y/t²`, which is negligible against the `π y` of the large sieve — this is
  what the rigid level `⌊√y⌋` could not achieve, since there `Q² = y`.
* `Q ≥ s/t − 1 ≥ s/(2t)`, so `log Q ≥ t/2 − log t − log 2` by `log_le_siftSum`; the loss
  `log t + log 2` is `O(√t)` by the elementary `log t ≤ 2√t` (`log_le_two_mul_sqrt`), hence
  negligible against `t/2`.
* The primes below the level contribute `Q + 1 ≤ s/t + 1`, negligible against `y/t` because
  `s = √y`; the quantitative form uses `s ≥ t²/16` (`sq_log_le_sixteen_mul_sqrt`, from
  `√y = exp(t/2) = (exp(t/4))² ≥ (1 + t/4)²`).

Adding up, the bound is `(π y)/(t/2) (1 + o(1)) = 2π y/t (1 + o(1))`.  The numeric chain is
isolated in `level_bound_le_two_pi`, which carries an extra factor `c ≥ 1`: `c = 1` gives the
interval form and `c = q/φ(q)` the arithmetic-progression form.

## Commands and observed output

```bash
lake build RiemannHypothesis.BrunTitchmarshSharp   # Build completed successfully
lake build                                          # Build completed successfully
./scripts/audit.sh                                  # OK
```

`./scripts/audit.sh` prints

```
'RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le_of_level' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le_two_pi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

and both statements are pinned in `scripts/revalidation.lean`.

## What is *not* proved

* The constant is `2π`, not the sharp `2 + o(1)` of the classical Brun–Titchmarsh theorem: the
  factor `π` is the one this repository's large sieve carries in place of `1`, and removing it
  needs Selberg's majorant or the Montgomery–Vaughan Hilbert inequality.
* The threshold is not effective in any useful sense: `log y ≥ (1000/ε)² + 10⁶` is what the crude
  numerical chain gives, and it is far from what the argument really needs.
* Only the interval form is treated here; the arithmetic-progression form of
  `RiemannHypothesis/BrunTitchmarshProgressions.lean` still carries its own rigid level
  `Q = ⌊√Y⌋` and its constant `4.15`.  No Bombieri–Vinogradov consequence is drawn, and nothing
  about `ζ` follows: no zero-free region, no zero-density estimate, no mean value theorem.
