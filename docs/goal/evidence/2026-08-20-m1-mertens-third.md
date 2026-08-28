# Evidence: Mertens' third theorem, bounded form (2026-08-20)

Row: `M1-MERTENS-THIRD` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/MertensThird.lean`:

* `primeProd x = ∏_{p ≤ x} (1 − 1/p)⁻¹` (a definition).
* `neg_log_one_sub_bounds` : `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`.
* `log_primeProd_eq` : `log ∏_{p ≤ x} (1 − 1/p)⁻¹ = ∑_{p ≤ x} −log(1 − 1/p)`.
* `primeProd_pos` : the product is positive.
* `log_primeProd_sub_primeRecipSum_bounds` :
  `0 ≤ log ∏_{p ≤ x} (1 − 1/p)⁻¹ − ∑_{p ≤ x} 1/p ≤ 2`.
* `mertens_third` : `|log ∏_{p ≤ x} (1 − 1/p)⁻¹ − log log x| ≤ 54` for `x ≥ 4`.
* `mertens_third_bounds` : `e^{−54} log x ≤ ∏_{p ≤ x} (1 − 1/p)⁻¹ ≤ e^{54} log x` for `x ≥ 4`.

## The argument

`log ∏_{p ≤ x} (1 − 1/p)⁻¹ = ∑_{p ≤ x} −log(1 − 1/p)` (each factor is positive because
`1/p ≤ 1/2`). For `0 < t ≤ 1/2`, `log(1 − t) ≤ −t` gives the lower bound `t ≤ −log(1 − t)`,
and `log z ≤ z − 1` at `z = (1 − t)⁻¹` gives `−log(1 − t) ≤ t/(1 − t) ≤ t + 2t²`, the last
step being `t²(1 − 2t) ≥ 0`. Summing with `t = 1/p` over the primes `p ≤ x`, and bounding
`∑_{p ≤ x} 2/p² ≤ 2 ∑_{n=2}^{⌊x⌋} 1/n² ≤ 2` (`sum_inv_sq_le`), gives

```
0 ≤ log ∏_{p ≤ x} (1 − 1/p)⁻¹ − ∑_{p ≤ x} 1/p ≤ 2.
```

Combining with `mertens_second` (`|∑_{p ≤ x} 1/p − log log x| ≤ 52` for `x ≥ 4`) gives `54`,
and exponentiating gives the product form.

## Commands run

```
lake build RiemannHypothesis.MertensThird
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `mertens_third` and `mertens_third_bounds` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* The sharp form of Mertens' third theorem, `∏_{p ≤ x} (1 − 1/p)⁻¹ ∼ e^γ log x`, is not
  proved. Only that the ratio lies between two positive absolute constants — and the
  constants proved here, `e^{±54}`, are enormous compared with the truth `e^γ ≈ 1.781`.
* The convergence of `∑_{p ≤ x} 1/p − log log x` (the Meissel–Mertens constant) is not
  proved, so no `∼` statement is available from this row.

## Adversarial revalidation: M1-MERTENS-THIRD

Second, independent pass.

* **Claim mode.** All items are `theorem`s or `lemma`s proved here; `primeProd` is a `def`
  unfolding to `∏ p ∈ {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime}, (1 − 1/p)⁻¹`, pinned by `rfl` in
  `scripts/revalidation.lean`. The only non-elementary input is this repository's
  `mertens_second`.
* **Non-vacuity.** `x ≥ 4` is load-bearing (it is inherited from `mertens_second`, and is
  what makes `log x > 0` so that the product form has content). Both conclusions are
  two-sided bounds on a non-trivial quantity: `mertens_third_bounds` in particular asserts
  the product grows at least like a positive constant times `log x`, which already implies
  that `∑_p 1/p` diverges.
* **Numerical sanity.** At `x = 100`: `∏_{p ≤ 100} (1 − 1/p)^{-1} ≈ 3.04` and
  `log 100 ≈ 4.605`, ratio `≈ 0.66`; the true limit of the ratio is `e^γ ≈ 1.781`, reached
  slowly. Both are trivially inside `[e^{−54}, e^{54}]`, as expected: the constant is the
  crude sum of the constants of the earlier rows and is not claimed to be sharp.
* **The elementary inequality, checked.** At `t = 1/2`, `−log(1/2) = 0.693` and
  `t + 2t² = 1`, so the upper bound holds with room; at `t = 1/3`, `−log(2/3) = 0.405`
  against `1/3 + 2/9 = 0.556`. The lower bound `t ≤ −log(1 − t)` is `log(1 − t) ≤ −t`,
  an instance of `log z ≤ z − 1`. The hypothesis `t ≤ 1/2` is genuinely used: the last step
  `t/(1 − t) ≤ t + 2t²` fails for `t` close to `1`.
* **Statement pinning.** `scripts/revalidation.lean` writes out `primeProd`,
  `neg_log_one_sub_bounds`, `mertens_third` and `mertens_third_bounds` in full and supplies
  the repository's declarations as the proof terms; `scripts/audit.sh` prints their axioms.
