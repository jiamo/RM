# Evidence: Mertens' second theorem (2026-08-20)

Row: `M1-MERTENS-SECOND` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/MertensSecond.lean`:

* `primeRecipSum x = ∑_{p ≤ x} 1/p` (a definition).
* `sum_by_parts_Ioc` : the discrete Abel summation identity
  `∑_{n ≤ N+1} b(n) f(n) = (∑_{m ≤ N+1} b(m)) f(N+1) + ∑_{n ≤ N} (∑_{m ≤ n} b(m)) (f(n) − f(n+1))`.
* `sum_inv_sq_le` : `∑_{n=2}^{M} 1/n² ≤ 1`.
* `mertens_second_nat` : `|∑_{p ≤ N} 1/p − log log N| ≤ 50` for every natural `N ≥ 2`.
* `mertens_second` : `|∑_{p ≤ x} 1/p − log log x| ≤ 52` for every real `x ≥ 4`.

Mathlib knows that `∑_p 1/p` diverges (`Nat.Primes.not_summable_one_div`) but has no rate;
none of Mertens' three theorems is in Mathlib.

## The argument

Write `A(n) = ∑_{p ≤ n} log p / p` and `f(n) = 1/log n`, so that `∑_{p ≤ N} 1/p = ∑_{n ≤ N} b(n) f(n)`
with `b(n) = log n / n` on primes and `0` elsewhere. Summation by parts (`sum_by_parts_Ioc`) gives

```
∑_{p ≤ N} 1/p = A(N) f(N) + ∑_{n = 2}^{N-1} A(n) (f(n) − f(n+1)),
```

the `n = 1` term vanishing because `A(1) = 0`.

1. **Boundary term.** `mertens_first_prime` (this repository, row `M1-MERTENS-FIRST`) gives
   `|A(y) − log y| ≤ C₀ := log 4 + 12 + log 2 ≈ 14.08` for `y ≥ 1`. Hence
   `|A(N) f(N) − 1| = |A(N) − log N| / log N ≤ C₀ / log 2 ≤ 20.4` for `N ≥ 2`.
2. **Main term.** With `a = log n`, `b = log (n+1)`,
   `log n (f(n) − f(n+1)) = (b − a)/b`. The inequality `log t ≤ t − 1` applied to `t = a/b`
   gives `(b − a)/b ≤ log b − log a`, and applied to `t = b/a` it gives
   `log b − log a ≤ (b − a)/a`. The gap is
   `(b−a)/a − (b−a)/b = (b−a)²/(ab) ≤ 1/((log 2)² n²)`, using `b − a = log(1 + 1/n) ≤ 1/n`
   and `ab ≥ (log 2)²`. Telescoping over `2 ≤ n ≤ M` and using `∑_{n ≥ 2} 1/n² ≤ 1`,
   `∑_{n=2}^{M} log n (f(n) − f(n+1))` lies within `1/(log 2)² ≤ 2.09` of
   `log log (M+1) − log log 2`.
3. **Error term.** Replacing `A(n)` by `log n` in the Abel sum costs at most
   `C₀ ∑_{n=2}^{M} (f(n) − f(n+1)) = C₀ (f(2) − f(M+1)) ≤ C₀ / log 2 ≤ 20.4`, since `f` is
   antitone from `2` on.

Adding the three contributions and `|log log 2| ≤ 0.45` gives the constant `50` (the sum of
the individual bounds is `≈ 44.2`, so there is slack). For a real argument `x ≥ 4`, with
`N = ⌊x⌋ ≥ 4` one has `∑_{p ≤ x} 1/p = ∑_{p ≤ N} 1/p` and `N ≤ x ≤ 2N`, so
`0 ≤ log log x − log log N ≤ (log x − log N)/log N ≤ log 2 / log 4 ≤ 1`, giving `52`.

The constants are explicit but far from optimal: the true statement is
`∑_{p ≤ x} 1/p = log log x + M + O(1/log x)` with `M ≈ 0.2615`. Only boundedness of the error
is proved here.

## Commands run

```
lake build RiemannHypothesis.MertensSecond
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `mertens_second_nat`, `mertens_second` and `sum_by_parts_Ioc` reports
exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* The existence of the Meissel–Mertens constant `M`, i.e. the convergence of
  `∑_{p ≤ x} 1/p − log log x`, is not proved; only that this difference is bounded.
* Mertens' *third* theorem (the product `∏_{p ≤ x} (1 − 1/p)^{-1} ∼ e^γ log x`) is not proved.
* Nothing here approaches the prime number theorem.

## Adversarial revalidation: M1-MERTENS-SECOND

Second, independent pass.

* **Claim mode.** Everything is a `theorem` proved in this repository. `primeRecipSum` is a
  `def` unfolding to `∑ p ∈ {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime}, 1/p`, pinned by `rfl` in
  `scripts/revalidation.lean`; the theorems are about it, not about a placeholder `Prop`.
  The only imported input beyond Mathlib basics is this repository's `mertens_first_prime`.
* **Non-vacuity.** `N ≥ 2` is load-bearing: it makes `log N > 0`, so that `f(N) = 1/log N` is
  meaningful and the boundary term is controlled; at `N = 1` the Lean convention `log 1 = 0`
  would make `f(1)` a division by zero. `x ≥ 4` in the real form is used both for
  `⌊x⌋ ≥ 4` and for `log ⌊x⌋ ≥ log 4 ≥ log 2`, which is what bounds the passage from `⌊x⌋`
  to `x`. The conclusion is a two-sided bound on a non-trivial quantity.
* **Numerical sanity.** At `N = 100`, `∑_{p ≤ 100} 1/p ≈ 1.803` and `log log 100 ≈ 1.527`, a
  difference of `≈ 0.28`; at `N = 10`, `∑_{p ≤ 10} 1/p = 1/2+1/3+1/5+1/7 ≈ 1.176` against
  `log log 10 ≈ 0.834`, a difference of `≈ 0.34`; at `N = 2` the difference is
  `0.5 − log log 2 ≈ 0.87`. All are far inside `50`, as expected: the bound is the sum of
  three crude `O(1)` estimates and is not claimed to be sharp.
* **Where the size of the constant comes from.** Almost all of it is `2 C₀/log 2 ≈ 40.6`,
  i.e. twice the constant of Mertens' first theorem in prime form, which in turn is loose
  because `ψ(x) ≤ (log 4 + 4) x` and the prime-power correction `8` are loose. Sharpening
  the first theorem would sharpen this row automatically; no attempt is made here.
* **Independence of the pieces.** `sum_inv_sq_le`, the telescoping identities
  (`sum_fwt_telescope`, `sum_loglog_telescope`) and the two one-term inequalities
  (`main_term_le`, `main_term_ge`) are proved separately, so the final `linarith` step
  combines facts each of which is independently checkable.
* **Statement pinning.** `scripts/revalidation.lean` writes out `primeRecipSum`,
  `sum_by_parts_Ioc`, `sum_inv_sq_le`, `mertens_second_nat` and `mertens_second` in full and
  supplies the repository's declarations as the proof terms; `scripts/audit.sh` prints their
  axioms.
