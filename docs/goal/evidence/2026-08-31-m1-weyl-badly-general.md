# M1-WEYL-BADLY-GENERAL — Weyl's exponent for a badly approximable coefficient, in every degree

Date: 2026-08-31
File: `RiemannHypothesis/WeylBadlyGeneral.lean`

## Claim

Weyl's inequality is conditional on a rational approximation to `d! α` with a denominator in a
prescribed range, and it must be: for `α` rational there is no cancellation.  The repository
removes the hypothesis for *badly approximable* coefficients in degree `2`
(`M1-WEYL-BADLY-APPROXIMABLE`) and in degree `3` (`M1-WEYL-CUBIC`); the open boundary of
`M1-WEYL-GENERAL` recorded that this was not carried out in general degree.  This row carries it
out, using the three-term inequality of `M1-WEYL-CLASSICAL`.

Dirichlet's approximation theorem with parameter `N` (`exists_coprime_approx` of
`M1-WEYL-BADLY-APPROXIMABLE`) gives a coprime `a/q` with `q ≤ N` and `|d! α − a/q| ≤ 1/(q(N+1))`,
and `le_den_of_badlyApproximable` turns the badly-approximable hypothesis into `q ≥ c(N+1)`.  Both
ends of the three-term bracket are then controlled at once:

    1/q + 1/N + q/N^d ≤ (1/c)/N + 1/N + 1/N^(d-1) ≤ (1/c + 2)/N,

which is a saving of a whole power of `N` over the trivial bracket.

* `exists_norm_polyPhaseSum_pow_mul_le_of_badlyApproximable` — for every `ε > 0` and `c > 0` there
  is a `C ≥ 1` such that, for every polynomial phase `f` of degree at most `d` with
  `n^d`-coefficient `α`,

      ‖∑_{0 ≤ n < N} e(f n)‖^(2^(r+1)) · N ≤ C N^(2^(r+1)) N^ε   for every N ≥ 1,

  whenever `|(r+2)! α − a/q| ≥ c/q²` for every fraction `a/q`.
* `exists_norm_polyPhaseSum_le_of_badlyApproximable` — the same after taking `2^(r+1)`-th roots:
  `‖∑_{n<N} e(f n)‖ ≤ C N^(1 − 1/2^(d−1) + ε)`, `d = r + 2`, with **no hypothesis on `N`** and no
  Diophantine hypothesis beyond the fixed one on the leading coefficient `α`.
* `exists_norm_monomialSum_pow_mul_le_of_badlyApproximable` and
  `exists_norm_monomialSum_le_of_badlyApproximable` — the two specialized to the monomial phase.
* `exists_norm_monomialSum_sqrt_two_le` — the explicit coefficient `α = √2/d!`, for which
  `d! α = √2` is badly approximable with constant `1/4` (`badlyApproximable_sqrt_two`).

For `d = 2` the exponent is `1/2 + ε`, matching the square-root cancellation of
`M1-WEYL-BADLY-APPROXIMABLE` up to the `ε` in place of its logarithm.

## Gates

* `lake build` succeeds; `lake build RiemannHypothesis.WeylBadlyGeneral` succeeds and the module is
  imported by `RiemannHypothesis.lean`.
* No `sorry` in the file.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the five theorems;
  the checks are recorded in `scripts/audit.sh`.
* `docs/goal/conditional-theorems.txt` regenerated; no theorem of this row occurs in the manifest.

## Open boundary

* The `ε` is inherited from the divisor loss of `M1-WEYL-CLASSICAL` and is not removed; the
  logarithmic form `N^(1−1/2^(d−1)) (log N)^A` is not proved.  The constant depends on `c`, `ε` and
  the degree and is not optimized.
* Badly approximable numbers are a set of measure zero.  For a general irrational `α` only the
  qualitative equidistribution of `α n^d` is available in this repository
  (`RiemannHypothesis.WeylPolynomialGeneral`), with no rate; a rate for almost every `α` would need
  the metric theory of Diophantine approximation, which is not formalized here.
* Nothing about `ζ` follows: polynomial phases are not zeta phases, and no subconvexity bound,
  approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-BADLY-GENERAL

* The module is imported by `RiemannHypothesis.lean`; `lake build` succeeds and the file contains
  no `sorry`.
* The statements are pinned in `scripts/revalidation.lean` (section `M1-WEYL-BADLY-GENERAL`), with
  the repository's declarations supplied as the proof terms.
* Nothing is vacuous.  The hypothesis class is inhabited: `badlyApproximable_sqrt_two` supplies
  `√2` with `c = 1/4`, and `badlyApproximable_of_quadratic` supplies every irrational quadratic
  number, so `exists_norm_monomialSum_sqrt_two_le` is an unconditional statement about an explicit
  sequence.  The conclusion beats the trivial bound `‖∑_{n<N}‖ ≤ N` for every `ε < 1/2^(d−1)`.
* The hypotheses are load-bearing.  The badly-approximable hypothesis is what forces the
  Dirichlet denominator to satisfy `q ≥ c(N+1)`, which bounds the first term of the bracket; the
  choice of Dirichlet parameter `N` is what bounds the third; `0 < N` is needed for both.  Without
  the Diophantine hypothesis the statement is false: for `α = 0` the sum equals `N`.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.  The Riemann hypothesis itself remains open in this
  repository.
