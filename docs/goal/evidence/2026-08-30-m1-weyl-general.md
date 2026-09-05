# M1-WEYL-GENERAL — Weyl's inequality in arbitrary degree

Date: 2026-08-30
File: `RiemannHypothesis/WeylGeneral.lean`

## Claim

Write `e(x) = exp(2πix)`, let `‖·‖` be the distance to the nearest integer (`intDist`), and let
`dioMaj β N m = min(N, 1/(2‖β m‖))` be the majorant of `M1-WEYL-CUBIC`, whose value is taken to be
`N` when `β m` is an integer, so that no convention for `1/0` is needed.

* `weylMulti β N H r m` — the **`r`-fold shifted majorant sum** `W_r`, defined by recursion on `r`:

      W₀(m) = dioMaj β N m,        W_{r+1}(m) = ∑_{0 ≤ k < H} W_r(m k).

  The zero shifts are *included*, so `W_r(0) = H^r N` (`weylMulti_zero_arg`), and
  `weylMulti_mul` records `W_r(β c, N, H, m) = W_r(β, N, H, c m)`: scaling the frequency is the
  same as scaling the argument.

* `IsPolyPhase d α f` — "`f n = ∑_{j ≤ d} c j n^j` for coefficients `c` with `c d = α`".

* `IsPolyPhase.diff` — **differencing lowers the degree**: if `f` is a polynomial phase of degree
  at most `d + 1` with `n^{d+1}`-coefficient `α`, then `n ↦ f(n + k) − f n` is a polynomial phase
  of degree at most `d` with leading coefficient `(d + 1) k α`.

* `norm_polyPhaseSum_pow_le` — **Weyl's inequality in degree `d + 1`**.  For every polynomial phase
  `f` of degree at most `d + 1` with `n^{d+1}`-coefficient `α`, every `N`, and every `H ≥ 1`,

      ‖∑_{0 ≤ n < N} e(f n)‖^{2^d} · H^d (N + H)
        ≤ 8^{2^d} (N + H)^{2^d} · W_d((d+1)! α, N, H, 1).

  There is no additive error term: the diagonal of each differencing step is absorbed by the
  `k = 0` term of the majorant sum.

* `dioSum β N M = ∑_{0 < t ≤ M} dioMaj β N t`, and `weylMulti_le_dioSum` — **the fold onto one
  variable**: for `m > 0`,

      W_{r+1}(m) ≤ (r + 1) H^r N + H^r · dioSum(β, N, m H^{r+1}).

* `dioSum_le_of_approx` — the counting lemma `sum_Ioc_le` of `M1-WEYL-MIN-SUM`, restated for
  `dioSum`: if `a`, `q` are coprime and `|β − a/q| ≤ 1/q²`, then
  `dioSum β N M ≤ (M/q + 1)(4N + q(1 + log q))`.

* `weylMulti_le_of_approx` — the two combined:

      W_{r+1}(1) ≤ (r + 1) H^r N + H^r ((H^{r+1}/q + 1)(4N + q(1 + log q))).

* `norm_monomialSum_pow_le_of_approx` — Weyl's inequality with the majorant sum evaluated, for the
  monomial phase `α n^{r+2}` and a coprime approximation `|(r+2)! α − a/q| ≤ 1/q²`.

* `norm_monomialSum_pow_mul_le_of_approx` — **the power saving, in a clean form**: under the same
  hypotheses, whenever `0 < H`, `H^{r+1} ≤ q` and `q ≤ N`,

      ‖∑_{0 ≤ n < N} e(α n^{r+2})‖^{2^{r+1}} · H ≤ 16^{2^{r+1}} N^{2^{r+1}} (r + 11 + 2 log N).

  For `H` of size about `N^{1/(r+1)}` — which the hypothesis `H^{r+1} ≤ q` permits when the
  denominator is of size about `N` — this is a saving of `N^{−1/((r+1) 2^{r+1})}` over the trivial
  bound `N`, up to the logarithm.  In the degree `d = r + 2` this is the exponent
  `1 − 1/((d−1) 2^{d−1})`.

## Proof

`M1-WEYL-QUADRATIC` applies van der Corput's A process once and `M1-WEYL-CUBIC` twice.  The
induction carries out the general step.

The A process, `norm_sq_sum_e2pi_le` of `M1-WEYL-DIFFERENCING`, gives

    H ‖S‖² ≤ (N + H − 1)(N + 2 ∑_{0 < k < H} ‖S_k‖),    S_k = ∑_n e(f(n+k) − f n),

and by `IsPolyPhase.diff` each `S_k` is the sum of a polynomial phase of degree one lower, with
leading coefficient `(d+1) k α`.  Applying the inductive hypothesis to each `S_k`, raising the
inequality to the power `2^{d-1}` and using Hölder in the form
`(∑_k ‖S_k‖)^{K} ≤ H^{K−1} ∑_k ‖S_k‖^{K}` turns the sum over the shifts into a sum of majorant
sums; `weylMulti_mul` then folds the shift `k` into the outermost variable of `W`, so that
`∑_{0 < k < H} W_{d-1}(k)` is one term of `W_d(1)` (`sum_Ioo_weylMulti_le`), and the diagonal
term `N` is absorbed by the `k = 0` term, which is exactly `H^{d-1} N`
(`weylMulti_ge_diagonal`).  The constants satisfy `C_{d+1} = 2^{K−1} + 2^{2K−1} C_d`, which
`8^{K}` dominates.  The purely algebraic step is isolated as `weyl_assembly`.

For the second half, `weylMulti_le_dioSum` is an induction on `r` using
`Finset.sum_range_succ'`: the shift `k = 0` contributes `H^r N`, and for `k ≥ 1` the inductive
hypothesis applies with the argument `m k`, whose one-dimensional majorant sums are all dominated
by the single sum up to `m H^{r+1}` by monotonicity.  Feeding the counting lemma of
`M1-WEYL-MIN-SUM` and simplifying with `H^{r+1} ≤ q ≤ N` gives the clean form.

## Why this row exists

The open boundaries of `M1-WEYL-QUADRATIC`, `M1-WEYL-MIN-SUM` and `M1-WEYL-CUBIC` all name the
same missing item: "the general degree-`d` Weyl inequality, by induction on `d`, is still not
formalized".  This row supplies it, together with the evaluation of the resulting majorant sum, so
that the degree is no longer a limitation of the method as formalized here — only the quality of
the exponent is.

## Scope, and what is *not* claimed

* The exponent is `1 − 1/((d−1) 2^{d−1})`, **weaker than the classical Weyl exponent
  `1 − 1/2^{d−1}`**.  The loss is the crude folding of the `(d−1)`-tuples of shifts onto their
  product in `weylMulti_le_dioSum`, where the classical argument uses the average divisor bound
  `∑_{m ≤ M} τ(m) ≪ M log M`, which is not formalized here.  For `d = 3` the two agree with the
  `7/8` of `M1-WEYL-CUBIC`.
* The constants are not optimized and the logarithm is not removed.
* The choice `H ≈ N^{1/(d−1)}` is left to the caller: the statement is uniform in `H` subject to
  `H^{d−1} ≤ q ≤ N`.  The unconditional badly approximable form and the explicit coefficients,
  done for `d = 2` in `M1-WEYL-BADLY-APPROXIMABLE` and for `d = 3` in `M1-WEYL-CUBIC`, are not
  carried out in general degree.
* Vinogradov's mean value theorem, which is what degrees beyond the reach of Weyl's method need,
  is not formalized.
* As it must be, the bound is conditional on a rational approximation to `d! α` with a large
  denominator; for `α` close to a rational with a small denominator there is no cancellation.
* Nothing about `ζ` follows.  Polynomial phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-GENERAL

* The module is imported by `RiemannHypothesis.lean`, `lake build RiemannHypothesis.WeylGeneral`
  succeeds, the file contains no `sorry`, and the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_polyPhaseSum_pow_le`, `IsPolyPhase.diff`, `weylMulti_le_dioSum`, `weylMulti_le_of_approx`,
  `norm_monomialSum_pow_le_of_approx` and `norm_monomialSum_pow_mul_le_of_approx`; the checks are
  in `scripts/audit.sh`.
* The main statements are pinned in `scripts/revalidation.lean` with `weylMulti`, `IsPolyPhase`
  and `dioSum` named by their fully qualified constants and every hypothesis written out.
* Nothing is vacuous.  The hypotheses of `norm_monomialSum_pow_mul_le_of_approx` are satisfiable:
  `H = 1` and any `q` with `1 ≤ q ≤ N` and a coprime approximation to `(r+2)! α` satisfy
  `H^{r+1} = 1 ≤ q ≤ N`, and Dirichlet's theorem (`exists_coprime_approx` of
  `M1-WEYL-BADLY-APPROXIMABLE`) produces such approximations.  The conclusion is a genuine saving:
  for `H` of size `N^{1/(r+1)}` the right-hand side is `o(N^{2^{r+1}} · H)`, so the bound beats
  the trivial `‖S‖ ≤ N`.  `norm_polyPhaseSum_pow_le` itself is unconditional and states an
  inequality between two explicit finite quantities.
* The hypotheses are load-bearing.  `0 < H` is needed for the differencing (with `H = 0` the left
  side of the A process is vacuous and the induction has nothing to fold); `m > 0` in
  `weylMulti_le_dioSum` is what makes `i ↦ m(i+1)` injective into `(0, m H^{r+1}]`; coprimality of
  `a` and `q` is what makes the grid argument behind the counting lemma work; `q ≤ N` merges the
  logarithms; `H^{r+1} ≤ q` is what bounds the number of complete residue blocks.  The Diophantine
  hypothesis cannot be dropped: for `α = 0` the sum equals `N` exactly.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.  In particular the rows of `M2` and beyond are
  untouched, and the Riemann Hypothesis itself remains open in this repository.
