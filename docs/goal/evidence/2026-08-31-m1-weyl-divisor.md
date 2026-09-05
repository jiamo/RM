# M1-WEYL-DIVISOR — the divisor bound, and Weyl's classical exponent

Date: 2026-08-31
Files: `RiemannHypothesis/DivisorBound.lean`, `RiemannHypothesis/WeylDivisor.lean`

## Claim

`M1-WEYL-GENERAL` reached the exponent `1 − 1/((d−1) 2^(d−1))` and named its own open boundary:
the `(d−1)`-fold majorant sum was folded onto the product of the shifts *crudely*, giving every
one of the `H^(d−2)` remaining tuples a whole one-dimensional sum, where the classical argument
pays only the number of factorizations of the product — the divisor function.  This row supplies
that ingredient and reaches Weyl's exponent `1 − 1/2^(d−1) + ε`.

### The divisor bound (`RiemannHypothesis/DivisorBound.lean`)

* `exists_pow_bound` — for every `ε > 0` there is a `K ≥ 1` with `a + 1 ≤ K (2^ε)^a` for every
  `a : ℕ` (the Bernoulli step: `2^ε > 1`, so the geometric side eventually dominates the linear
  one, and the finitely many exceptions are absorbed into `K`).
* `exists_card_divisors_le` — **the divisor bound** `τ(n) ≤ C_ε n^ε` for every `n ≥ 1`, proved by
  multiplicativity: the prime powers `p^a` with `p ≥ 2^(1/ε)` contribute `(a+1)/p^(aε) ≤ 1`, and
  the finitely many small primes contribute at most `K^B` with `B = ⌈2^(1/ε)⌉`.  Mathlib does not
  contain this statement.
* `sum_mul_divisor_le` — folding one variable into the product multiplies the weight by one factor
  of `τ`:  `∑_{k ≤ A} ∑_{u ≤ M} τ(u)^p F(ku) ≤ ∑_{v ≤ AM} τ(v)^(p+1) F(v)` for every `F ≥ 0`.
* `card_divisors_pow_le` — `τ(v)^r ≤ (C V^ε)^r` for `1 ≤ v ≤ V`.

### The folded majorant sum (`RiemannHypothesis/WeylDivisor.lean`)

* `weylMulti_le_divisorSum` — **the `(r+1)`-fold majorant sum of `M1-WEYL-GENERAL`, folded onto the
  product of the shifts with the divisor weight**:

      W_{r+1}(β, N, H, m) ≤ (r + 1) H^r N
        + ∑_{1 ≤ u ≤ H^(r+1)} τ(u)^r · dioMaj(β, N, m u).

  The first term collects the tuples with a zero entry; every other tuple is counted at its
  product `u ≤ H^(r+1)`, and a product is reached by at most `τ(u)^r` tuples.
* `sum_Icc_dioMaj_mul_le` — the majorant sum along the multiples of `m > 0` is at most the
  one-dimensional sum `dioSum(β, N, mV)`, because `u ↦ m u` is injective into `(0, mV]`.
* `sum_divisorWeight_le` — the divisor weight discharged: on `[1, V]` the weight `τ(u)^s` is at
  most `(C V^ε)^s`, so the weighted sum is at most that constant times `dioSum`.
* `weylMulti_le_of_approx_divisor` — the two combined with the counting lemma of
  `M1-WEYL-MIN-SUM`: from a coprime approximation `|β − a/q| ≤ 1/q²`,

      W_{s+1}(β, N, H, 1) ≤ (s + 1) H^s N
        + (C (H^(s+1))^ε)^s · (H^(s+1)/q + 1)(4N + q(1 + log q)).

  The loss over the one-dimensional sum is the divisor factor `(C (H^(s+1))^ε)^s`, not the factor
  `H^s` of `weylMulti_le_of_approx`.
* `norm_monomialSum_pow_mul_le_of_approx_divisor` — **Weyl's inequality with the classical
  exponent.**  With `H = N` shifts and `N ≤ q ≤ N^(r+1)`,

      ‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · N
        ≤ 16^(2^(r+1)) N^(2^(r+1)) · (C (N^(r+1))^ε)^r · (r + 11 + 2(r+1) log N).

* `exists_norm_monomialSum_pow_mul_le` — **Weyl's exponent.**  For every `ε > 0` there is a
  `C ≥ 1` with

      ‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) · N ≤ C N^(2^(r+1)) N^ε

  whenever `|(r+2)! α − a/q| ≤ 1/q²` with `q` coprime to `a` and `N ≤ q ≤ N^(r+1)`; that is,
  `‖∑_{n<N} e(α n^d)‖ ≤ C' N^(1 − 1/2^(d−1) + ε)` for `d = r + 2`.  The divisor loss is absorbed by
  taking the divisor exponent `ε₀ = ε/(2((r+1)r + 1))`, and the logarithm by
  `Real.log x ≤ x^δ/δ` with `δ = ε/2`.

## Gates

* `lake build` — succeeds; `lake build RiemannHypothesis.DivisorBound` and
  `lake build RiemannHypothesis.WeylDivisor` succeed, both modules are imported by
  `RiemannHypothesis.lean`.
* No `sorry` in either file.
* `bash scripts/audit.sh`; `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
  for `exists_card_divisors_le`, `sum_mul_divisor_le`, `card_divisors_pow_le`,
  `weylMulti_le_divisorSum`, `sum_divisorWeight_le`, `weylMulti_le_of_approx_divisor`,
  `norm_monomialSum_pow_mul_le_of_approx_divisor` and `exists_norm_monomialSum_pow_mul_le`, and
  the checks are recorded in `scripts/audit.sh`.
* `docs/goal/conditional-theorems.txt` regenerated.  `WeylGeneral.IsPolyPhase` — the property
  "`f` is a polynomial phase of degree at most `d` with leading coefficient `α`" of the phase
  function supplied by the caller — is now classified as `DEFINITIONAL` in
  `scripts/conditional_theorems.lean`, where it had been reported as `UNCLASSIFIED`; no theorem of
  this row occurs in the manifest, since none of their hypotheses mentions an unproved `Prop`.

## Open boundary

* The denominator range is `N ≤ q ≤ N^(r+1)`, which is what taking `H = N` shifts allows.  The
  classical statement covers `q ≤ N^d` and carries the three terms `1/q + 1/N + q/N^d`; that
  refinement is not proved here.
* The `ε` is not removed: the bound carries `N^ε` with an ineffective-looking constant
  `C = 16^(2^(r+1)) C₀(ε)^r (r + 11 + 4(r+1)/ε)`, where `C₀(ε)` is the divisor-bound constant.  The
  sharper `(log N)^A` form of the divisor loss is not formalized.
* The constants are not optimized.
* Vinogradov's mean value theorem — what degrees beyond the reach of Weyl's method need — is not
  formalized.
* As it must be, the bound is conditional on a rational approximation to `d! α` with a denominator
  in the stated range; for `α` close to a rational with a small denominator there is no
  cancellation.
* Nothing about `ζ` follows.  Polynomial phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-DIVISOR

* Both modules are imported by `RiemannHypothesis.lean`; `lake build` succeeds and neither file
  contains a `sorry`.
* The statements are pinned in `scripts/revalidation.lean` (section `M1-WEYL-DIVISOR`), with every
  hypothesis written out and the repository's declarations supplied as the proof terms.
* Nothing is vacuous.  The hypotheses of `norm_monomialSum_pow_mul_le_of_approx_divisor` are
  satisfiable: `exists_card_divisors_le` produces `C` and the bound `hbound` for any `ε > 0`, and
  Dirichlet's theorem (`exists_coprime_approx` of `M1-WEYL-BADLY-APPROXIMABLE`) produces coprime
  approximations; a denominator `q` with `N ≤ q ≤ N^(r+1)` exists whenever `r ≥ 1`.  The conclusion
  is a genuine saving: the right-hand side is `N^(2^(r+1)) N^ε`, so dividing by `N` gives
  `‖S‖ ≤ C'' N^(1 − 1/2^(r+1) + ε')`, which beats the trivial `‖S‖ ≤ N`.
* The hypotheses are load-bearing.  `0 < N` is needed for the differencing and for `N^(r+1) > 0`,
  which is the factor cancelled at the end; `N ≤ q` is what merges the logarithms and bounds
  `4N + q(1 + log q)` by `q(5 + log q)`; `q ≤ N^(r+1)` bounds `N^(r+1)/q + 1` by `2 N^(r+1)/q` and
  `log q` by `(r+1) log N`; coprimality of `a` and `q` is what makes the counting lemma work; `m > 0`
  in `sum_Icc_dioMaj_mul_le` is what makes `u ↦ m u` injective; `1 ≤ C` and `0 < ε` are what make
  the divisor factor at least one, which is used to absorb the diagonal term `(r+1) N^(r+1)`.  The
  Diophantine hypothesis cannot be dropped: for `α = 0` the sum equals `N` exactly.
* No unproved `Prop` of this repository occurs among the hypotheses, and no result of this row is
  used to strengthen any other row's claim.  The Riemann Hypothesis itself remains open in this
  repository.
