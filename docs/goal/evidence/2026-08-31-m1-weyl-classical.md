# M1-WEYL-CLASSICAL — Weyl's inequality in its classical three-term form

Date: 2026-08-31
File: `RiemannHypothesis/WeylClassical.lean`

## Claim

`M1-WEYL-DIVISOR` reached Weyl's exponent `1 − 1/2^(d−1) + ε`, but only for denominators in the
range `N ≤ q ≤ N^(d−1)`, and named its own open boundary: "the classical statement covers
`q ≤ N^d` and carries the three terms `1/q + 1/N + q/N^d`, which is not proved here".  This row
proves that statement.  Nothing new is needed on the analytic side — the ingredients are Weyl
differencing with `H = N` shifts (`WeylGeneral.norm_polyPhaseSum_pow_le`), the fold of the shift
tuples onto their product with the divisor weight
(`WeylDivisor.weylMulti_le_of_approx_divisor`), and the counting lemma of `M1-WEYL-MIN-SUM`.  What
changes is that none of the four terms produced by the counting lemma is discarded: the range
restriction on `q` was exactly what allowed three of them to be collapsed into one.

* `weylBracket q N d = 1/q + 1/N + q/N^d` — the three-term bracket of the classical statement.
* `norm_polyPhaseSum_pow_le_three_term` — **the inequality with explicit constants**, for every
  `q > 0` and every polynomial phase `f` of degree at most `r + 2` with `n^(r+2)`-coefficient `α`:
  from a coprime approximation `|(r+2)! α − a/q| ≤ 1/q²` and the divisor bound `τ(n) ≤ C n^ε`,

      ‖∑_{0 ≤ n < N} e(f n)‖^(2^(r+1))
        ≤ 16^(2^(r+1)) N^(2^(r+1)) · (C (N^(r+1))^ε)^r · (r + 21 + 4 log q)
          · (1/q + 1/N + q/N^(r+2)).

  The counting lemma gives `(N^(r+1)/q + 1)(4N + q(1 + log q))` for the folded majorant sum; divided
  by `N^(r+2)` its four terms are `4/q`, `(1 + log q)/N`, `4/N^(r+1)` and `q(1 + log q)/N^(r+2)`,
  and `N^(r+1) ≥ N` puts the third inside the second.  The diagonal term `(r+1) N^(r+1)` of the
  differencing, divided by `N^(r+2)`, is `(r+1)/N`, which is the middle term again.
* `exists_norm_polyPhaseSum_pow_le_three_term` — the divisor loss and the logarithm absorbed into
  `N^ε` for `q ≤ N^(r+2)`: for every `ε > 0` there is a `C ≥ 1` with

      ‖∑_{0 ≤ n < N} e(f n)‖^(2^(r+1)) ≤ C N^(2^(r+1)) N^ε (1/q + 1/N + q/N^(r+2)),

  by taking the divisor exponent `ε₀ = ε/(2((r+1)r + 1))`, bounding `log q ≤ (r+2) log N` and using
  `Real.log x ≤ x^δ/δ` with `δ = ε/2`.
* `exists_norm_polyPhaseSum_le_three_term` — the same after taking `2^(r+1)`-th roots, in the shape
  found in the literature:

      ‖∑_{0 ≤ n < N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d−1)),  d = r + 2.

* `norm_monomialSum_pow_le_three_term`, `exists_norm_monomialSum_pow_le_three_term` and
  `exists_norm_monomialSum_le_three_term` — the three specialized to the monomial phase `α n^d`,
  by `WeylGeneral.isPolyPhase_monomial`.

For `q` of size `N^(d/2)` the bracket is of size `N^(−d/2)`, which is the classical minor-arc gain;
for `N ≤ q ≤ N^(d−1)` the bracket is `O(1/N)` and the statement of `M1-WEYL-DIVISOR` is recovered.

## Gates

* `lake build` succeeds; `lake build RiemannHypothesis.WeylClassical` succeeds and the module is
  imported by `RiemannHypothesis.lean`.
* No `sorry` in the file.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  the six theorems of the module; the checks are recorded in `scripts/audit.sh`.
* `docs/goal/conditional-theorems.txt` regenerated; the only theorem of this row that occurs in the
  manifest is `norm_polyPhaseSum_pow_le_three_term`, in the `DEFINITIONAL` section, because it takes
  the hypothesis `WeylGeneral.IsPolyPhase (r + 2) α f` on its own argument `f` — the same
  classification as `WeylGeneral.norm_polyPhaseSum_pow_le`.  No theorem of the row is conditional on
  an open assumption.

## Open boundary

* The `ε` is not removed: the constant is `16^(2^(r+1)) C₀(ε)^r (r + 21 + 8(r+2)/ε)` with `C₀(ε)`
  the divisor-bound constant, and the sharper `(log N)^A` form of the divisor loss is not
  formalized.  The constants are not optimized.
* The saving is vacuous at the two ends of the range: for `q = 1` the bracket is `≥ 1` and for `q`
  of size `N^d` it is again of size `1`.  That is the truth of the matter and not an artefact —
  for `α` close to a rational with a small denominator there is no cancellation.
* Vinogradov's mean value theorem, which is what degrees beyond the reach of Weyl's method need, is
  not formalized.
* Nothing about `ζ` follows: polynomial phases are not zeta phases, and no subconvexity bound,
  approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-CLASSICAL

* The module is imported by `RiemannHypothesis.lean`; `lake build` succeeds and the file contains
  no `sorry`.
* The statements are pinned in `scripts/revalidation.lean` (section `M1-WEYL-CLASSICAL`), with the
  bracket written out as `1/q + 1/N + q/N^(r+2)` rather than through the abbreviation, and the
  repository's declarations supplied as the proof terms.
* Nothing is vacuous.  The hypotheses are satisfiable: `DivisorBound.exists_card_divisors_le`
  produces `C` and `hbound` for any `ε > 0`, and Dirichlet's theorem (`exists_coprime_approx` of
  `M1-WEYL-BADLY-APPROXIMABLE`) produces coprime approximations with any prescribed accuracy, so
  every denominator range considered is inhabited.  The conclusion is a genuine saving whenever
  `q → ∞` and `q/N^d → 0`.
* The hypotheses are load-bearing.  `0 < N` gives `N^(r+2) > 0`, the factor cancelled at the end,
  and `N^(r+1) ≥ N`, which is what puts the fourth term of the counting lemma inside the second;
  `0 < q` and coprimality of `a` and `q` are what make the counting lemma work; `q ≤ N^(r+2)` is
  used only in the `ε`-forms, to bound `log q` by `(r+2) log N`; `1 ≤ C` and `0 < ε` make the
  divisor factor at least one, which is used to absorb the diagonal term.  The Diophantine
  hypothesis cannot be dropped: for `α = 0` the sum equals `N` exactly, and then `q = 1`, for which
  the bracket is `≥ 1` and the inequality is trivially true rather than a saving.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.  The Riemann hypothesis itself remains open in this
  repository.
