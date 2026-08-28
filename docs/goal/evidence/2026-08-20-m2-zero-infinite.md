# Evidence: the critical strip contains infinitely many zeroes of `ζ` (2026-08-20)

Row: `M2-ZERO-INFINITE` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroInfinite.lean`:

* `rootProd m z = ∏_{ρ ∈ m} (z − ρ)` (a definition, the product over a multiset of roots), with
  `norm_rootProd_le` (`‖rootProd m z‖ ≤ (‖z‖+M)^{card m}` when all roots satisfy `‖ρ‖ ≤ M`) and
  `one_le_norm_rootProd` (`1 ≤ ‖rootProd m z‖` when `‖z‖ ≥ M+1`);
* `differentiable_dslope` : the difference quotient of an entire function is entire;
* `analyticOrderAt_ne_top` : an entire function that is nonzero somewhere vanishes to finite
  order at every point;
* `exists_rootMultiset_factorization` : **an entire `f`, not identically zero, whose zeroes all
  lie in a finite set `S`, is `rootProd m · g` with `m` a multiset of elements of `S` and `g`
  entire and nowhere zero**;
* `xiFn_eq_zero_iff_mem_nontrivialZeroSet` : the zeroes of `ξ` are exactly the nontrivial zeroes
  of `ζ`;
* `infinite_nontrivialZeroSet` : **the set of zeroes of `ζ` in the open critical strip is
  infinite**;
* `infinite_setOf_xiFn_eq_zero` : `ξ` has infinitely many zeroes.

This strengthens `M2-ZERO-EXISTS`, which produced a single zero.

## The argument

Suppose the strip contained only finitely many zeroes, say the finite set `S`. The zeroes of `ξ`
are exactly those (`xiFn_eq_zero_iff_mem_nontrivialZeroSet`, from `riemannXi_eq_zero_iff` and
`xiFn_eq_zero_of_zeta`), and `ξ(2) ≠ 0`, so `exists_rootMultiset_factorization` applies:
`ξ = rootProd m · g` with every root in `S` and `g` entire without zeroes.

*The factorization* is an induction on `∑_{ρ ∈ S} analyticOrderNatAt ξ ρ`, a finite number since
`ξ ≢ 0`. If `f` has a zero `a`, then `f z = (z − a)·(dslope f a) z` identically
(`sub_smul_dslope`), the quotient `dslope f a` is again entire (`differentiableOn_dslope` on
`Set.univ`), its zeroes are still contained in `S`, and — multiplying orders through
`analyticOrderAt_mul`, the linear factor having order `1` at `a` and `0` elsewhere — its total
order is one less. So the induction terminates, and collecting the extracted roots into a
multiset gives the statement.

*The contradiction.* Write `g = exp G` with `G` entire (`exists_exp_of_ne_zero`). Let
`M = ∑_{ρ ∈ S} ‖ρ‖`, so every root has `‖ρ‖ ≤ M`. For `‖z‖ ≥ M+1` one has
`‖rootProd m z‖ ≥ 1`, hence `‖g z‖ ≤ ‖ξ z‖` and, by the order-one bound `norm_xiFn_le` of
`M1-XI-GROWTH`, `re G z ≤ C(1+‖z‖)log(2+‖z‖)`. On the compact disc `‖z‖ ≤ M+1` the continuous
function `re G` attains a maximum `D`. Thus `re G z ≤ C(1+‖z‖)log(2+‖z‖) + D` everywhere, and
`linear_of_re_le` gives `G z = a + b z`.

Along the real axis, at `z = 2(n+1)`, the polynomial factor is harmless:
`‖rootProd m z‖ ≤ (2(n+1)+M)^d ≤ (2+M)^d e^{d(n+1)}` with `d = card m` (using `t ≤ e^t`), while
`‖g z‖ ≤ e^{‖a‖} e^{2‖b‖(n+1)}`. So `‖ξ(2(n+1))‖ ≤ B·Lⁿ` with `L = e^{d+2‖b‖}` — which
`xiFn_growth_contradiction` (from `M2-ZERO-EXISTS`: `‖ξ(2(n+1))‖ ≥ π^{-(n+1)} n!`) refutes.

## Commands run

```
lake build RiemannHypothesis.ZeroInfinite
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `exists_rootMultiset_factorization`,
`xiFn_eq_zero_iff_mem_nontrivialZeroSet`, `infinite_nontrivialZeroSet` and
`infinite_setOf_xiFn_eq_zero` reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Nothing is located and nothing is counted.** The proof is again a contradiction: it gives no
  zero explicitly, no bound on the height of the `n`-th zero, and no lower bound for `N(T)` (the
  matching upper bound `N(T) ≤ C T log T` is `M2-ZERO-COUNT`). The classical
  `N(T) ~ (T/2π)log(T/2πe)` is out of reach here.
* Multiplicities are still ignored in the statement: `nontrivialZeroSet` is a set of points.
  (Multiplicities do appear inside the proof, in the multiset of roots.)
* Nothing bears on the real parts of the zeroes, so the row does not touch the Riemann
  hypothesis.
* The Hadamard product for `ξ` is not constructed; only the finite-zero factorization is.

## Adversarial revalidation: M2-ZERO-INFINITE

Second, independent pass.

* **Claim mode.** All the results are `theorem`s of this repository, pinned in full in
  `scripts/revalidation.lean` with the repository declarations as proof terms. `Set.Infinite` is
  Mathlib's, i.e. `¬ Set.Finite`, so `infinite_nontrivialZeroSet` genuinely says that no finite
  set exhausts the zeroes.
* **Vacuity check.** The statement is not vacuous and cannot be satisfied by an empty set: an
  infinite set is in particular nonempty, so this result also re-proves `M2-ZERO-EXISTS`
  (which it in fact uses only through the growth lemma `xiFn_growth_contradiction`, not through
  the existence statement).
* **Is it circular?** No: `xiFn_growth_contradiction` is the unconditional lower bound
  `π^{-(n+1)} n! ≤ ‖ξ(2(n+1))‖` combined with `n!/Lⁿ → ∞`; it does not presuppose that `ξ` has
  any zero. `M2-ZERO-EXISTS` and `M2-ZERO-INFINITE` are the two applications of the same lemma,
  with the trivial factorization `ξ = 1·g` and the finite-root factorization respectively.
* **Direction check.** As in `M2-ZERO-EXISTS`, the contradiction is between an upper bound
  derived from the (false) finiteness assumption and an unconditional lower bound at the *same*
  points. The extra polynomial factor is bounded *above* by `(2+M)^d e^{d(n+1)}`, which only
  enlarges the upper bound, so the contradiction is not an artefact of a mis-signed estimate.
* **Where finiteness is used.** Twice, and both uses are essential: to obtain a *finite* multiset
  of roots (so that the product factor is of finite degree and hence of exponential type along
  the real axis), and to obtain a *bounded* set of roots (so that `‖rootProd m z‖ ≥ 1` outside a
  disc). With infinitely many zeroes both fail, as they must.
* **Sanity check of the factorization.** For `f z = (z−1)²(z−2)` and `S = {1, 2}` the statement
  returns the multiset `{1, 1, 2}` and `g = 1`; the induction has length `3 = 2 + 1`, the total
  order of vanishing. The multiset, not a finset, is what makes the induction correct at a
  multiple zero.
* **Sanity check of the conclusion.** Classically there are infinitely many nontrivial zeroes
  (indeed `N(T) ~ (T/2π)log(T/2πe)`), so the statement is true; what is new here is that it is
  proved in this repository, from the repository's own growth bounds.
* **Statement pinning.** `scripts/revalidation.lean` writes out `rootProd`,
  `exists_rootMultiset_factorization`, `xiFn_eq_zero_iff_mem_nontrivialZeroSet`,
  `infinite_nontrivialZeroSet` and `infinite_setOf_xiFn_eq_zero` in full; `scripts/audit.sh`
  prints their axioms.
