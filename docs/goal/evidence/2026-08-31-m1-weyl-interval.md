# M1-WEYL-INTERVAL — Weyl's inequality over an arbitrary interval

Date: 2026-08-31
File: `RiemannHypothesis/WeylInterval.lean`

## Claim

Every Weyl bound of this repository is stated for the sum over `Finset.Ico 0 N`, an interval
starting at the origin.  The applications of Weyl's method — cutting a long sum into short blocks,
or summing over a dyadic range — need the same bound for `Finset.Ico M (M + N)`, uniformly in the
starting point `M`.  This row supplies that, with the same constants and the same exponents.

The mechanism is that translation does not move the leading coefficient of a polynomial phase:
expanding `f (n + M)` by the binomial theorem changes the lower coefficients only.

* `WeylGeneral.IsPolyPhase.comp_add` — if `f` is a polynomial phase of degree at most `d` with
  `n^d`-coefficient `α`, then so is `n ↦ f (n + M)`, with the same `α`.  The new coefficients are
  `c'ᵢ = ∑_{i ≤ j ≤ d} c_j C(j,i) M^(j−i)`, and `c'_d = c_d = α`.
* `sum_e2pi_Ico_shift` — `∑_{M ≤ n < M + N} e(f n) = ∑_{0 ≤ n < N} e(f (n + M))`, by the
  translation bijection of `Finset.Ico`.
* `norm_polyPhaseSum_Ico_pow_le_three_term` — the three-term inequality of `M1-WEYL-CLASSICAL`
  with explicit constants, for the sum over `[M, M + N)` and every denominator `q > 0`.
* `exists_norm_polyPhaseSum_Ico_pow_le_three_term` and
  `exists_norm_polyPhaseSum_Ico_le_three_term` — the divisor loss and the logarithm absorbed into
  `N^ε`, and the classical form

      ‖∑_{M ≤ n < M + N} e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d−1)),   d = r + 2,

  with `C` independent of `M`.
* `exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable` — Weyl's exponent of
  `M1-WEYL-BADLY-GENERAL` over an arbitrary interval:
  `‖∑_{M ≤ n < M + N} e(f n)‖ ≤ C N^(1 − 1/2^(d−1) + ε)` for every `N ≥ 1` and every `M`.
* `exists_norm_monomialSum_Ico_le_three_term`,
  `exists_norm_monomialSum_Ico_le_of_badlyApproximable`,
  `exists_norm_monomialSum_Ico_sqrt_two_le` — the monomial phase `α n^d` over an arbitrary
  interval, the last at the explicit coefficient `α = √2/d!`.

## Gates

* `lake build` succeeds; `lake build RiemannHypothesis.WeylInterval` succeeds and the module is
  imported by `RiemannHypothesis.lean`.
* No `sorry` in the file.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the nine
  declarations of the row; the checks are recorded in `scripts/audit.sh`.
* `docs/goal/conditional-theorems.txt` regenerated; the two entries of this row,
  `IsPolyPhase.comp_add` and `norm_polyPhaseSum_Ico_pow_le_three_term`, occur in the
  `DEFINITIONAL` section, since `IsPolyPhase` is a hypothesis on the theorem's own argument `f`
  and not an open assumption of the repository.

## Open boundary

* The bounds are exactly those of `M1-WEYL-CLASSICAL` and `M1-WEYL-BADLY-GENERAL` transported by
  translation, so their whole open boundary is inherited: the `ε` is not removed, the constants are
  not optimized, the bracket is trivial at the two ends of the denominator range, and no Vinogradov
  mean value theorem is formalized.
* Uniformity is in the starting point only.  Nothing here is uniform in the polynomial phase beyond
  its leading coefficient, and no bound for a sum over an interval whose length varies with `M`, or
  over a set other than an interval, is proved.
* The Diophantine hypothesis is on `d! α`, which translation leaves untouched — this row adds no
  new Diophantine input whatsoever.
* Nothing about `ζ` follows: polynomial phases are not zeta phases, and no subconvexity bound,
  approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-INTERVAL

* The module is imported by `RiemannHypothesis.lean`; `lake build` succeeds and the file contains
  no `sorry`.
* The statements are pinned in `scripts/revalidation.lean` (section `M1-WEYL-INTERVAL`), with the
  repository's declarations supplied as the proof terms.
* Nothing is vacuous.  The hypothesis class is inhabited in both directions: `isPolyPhase_monomial`
  supplies polynomial phases in every degree, and `badlyApproximable_sqrt_two` supplies the
  explicit coefficient `√2` with `c = 1/4`, so `exists_norm_monomialSum_Ico_sqrt_two_le` is an
  unconditional statement about an explicit sequence, over every interval.  Its conclusion beats
  the trivial bound `N` for every `ε < 1/2^(d−1)`.
* The hypotheses are load-bearing.  `0 < N` is needed for the bracket to be finite, the coprime
  approximation is what makes the three-term bracket meaningful, and the badly-approximable
  hypothesis is what forces the Dirichlet denominator to be large.  Translation invariance is
  genuine and not an artefact of the statement: `sum_e2pi_Ico_shift` is an identity, and the
  starting point `M` enters neither the constant nor the exponent.
* Nothing is claimed to be stronger than what is transported: the interval bound is *equivalent*
  to the bound at the origin for the translated phase, and the content of the row is precisely
  `IsPolyPhase.comp_add`, that translation preserves the degree and the leading coefficient.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.  The Riemann hypothesis itself remains open in this
  repository.
