# M1-WEYL-POLYNOMIAL-GENERAL — Weyl's exact criterion for a polynomial sequence

Date: 2026-08-28
File: `RiemannHypothesis/WeylPolynomialGeneral.lean`

## Claim

For every real polynomial `p`,

* `equidistributedMod1_polyEval_iff` — the values `p(n)`, `n ∈ ℕ`, are equidistributed modulo one
  **if and only if** some coefficient `p.coeff j` with `j ≥ 1` is irrational.

The two directions are recorded separately:

* `equidistributedMod1_polyEval_of_exists_irrational` — one irrational coefficient of positive
  index suffices; no hypothesis on the *leading* coefficient, and no degree hypothesis;
* `not_equidistributedMod1_polyEval_of_forall_rat` — if every coefficient of positive index is
  rational then the sequence is not equidistributed.

The two structural lemmas the proof needs are of independent use:

* `equidistributedMod1_of_sub_int` — equidistribution modulo one only depends on the sequence
  modulo one: if `x n − y n ∈ ℤ` for every `n` and `y` is equidistributed, so is `x`;
* `equidistributedMod1_of_residue_classes` — if `v ≥ 1` and each arithmetic subsequence
  `k ↦ x (v k + r)`, `r < v`, is equidistributed, then `x` is equidistributed.

## Proof

The converse is a computation.  If every `a_j`, `j ≥ 1`, is rational, `exists_common_denom`
produces `L ≥ 1` with `L a_j ∈ ℤ` for all `j ≥ 1` (the product of the denominators over the
support), so `L p(n) − L p(0) = ∑_{j ≥ 1} L a_j n^j ∈ ℤ` and every term of the Weyl sum at
frequency `L` equals `e(L p(0))`.  That sum has modulus `N`, so `‖∑_{n<N} e(L p(n))‖ / N = 1`
does not tend to `0`, and `M1-WEYL-CRITERION` forbids equidistribution.

The forward direction is a strong induction on `deg p`.  If the leading coefficient is irrational
the statement is `M1-WEYL-POLYNOMIAL`.  Otherwise `a_D = q` is rational; put `v = q.den` and split
`ℕ` into the residue classes modulo `v`.  Along `n = v m + r` the leading term is constant modulo
one, because `v ∣ (v m + r)^D − r^D` and `q v = q.num` is an integer, so `p(v m + r)` differs by an
integer from the value at `m` of

    h_r = C (a_D r^D) + (taylor r (eraseLead p)).comp (C v · X),

a polynomial of degree at most `D − 1`.  Let `j₀` be the largest index carrying an irrational
coefficient (`Nat.findGreatest`); it is at least `1` and, since `a_D` is rational, at most `D − 1`.
All coefficients above `j₀` are rational, and `irrational_taylor_coeff` then shows that the
`j₀`-th coefficient of `taylor r (eraseLead p)` is `p.coeff j₀` plus a rational number, hence
irrational; multiplying by the nonzero rational `v^{j₀}` keeps it irrational, and
`comp_C_mul_X_coeff` identifies it with `h_r.coeff j₀`.  The induction hypothesis applies to `h_r`,
`equidistributedMod1_of_sub_int` transports it to the progression, and
`equidistributedMod1_of_residue_classes` glues the `v` progressions into the full sequence.

Rationality is handled through the subfield `ratSubfield = (Rat.castHom ℝ).fieldRange`, whose
complement is exactly the irrationals (`mem_ratSubfield_iff`), so closure under sums, products,
powers and finite sums is inherited from the subfield structure.

The gluing lemma is proved through Weyl sums: `sum_range_eq_sum_residues` splits `∑_{n<N}` into
`∑_{r<v} ∑_{k<c_r(N)}` with `c_r(N) = #{k : v k + r < N}` (`blockCount`, with the exact criterion
`lt_blockCount_iff`), each block sum divided by `N` is at most the same sum divided by `c_r(N)`
since `c_r(N) ≤ N`, and `c_r(N) → ∞`, so each of the `v` terms tends to zero.

## Why this row exists

`M1-WEYL-POLYNOMIAL` recorded in its scope that "nothing is claimed when every coefficient is
rational", and its hypothesis was the classical one that the *leading* coefficient be irrational —
which says nothing about, say, `n ↦ √2 n + n²/2`.  This row removes the restriction and replaces
the sufficient condition by an exact criterion, so the equidistribution of a polynomial sequence
modulo one is now decided by its coefficients alone.

## Scope, and what is *not* claimed

* No rate of convergence: the input estimates are ineffective in the diophantine nature of the
  irrational coefficient, so nothing of the shape `∑_{n<N} e(p(n)) = O(N^{1−c})` is proved.
* The criterion is about a fixed polynomial with real coefficients; nothing uniform in `p` and
  nothing about polynomials in several variables is claimed.
* Nothing about `ζ` follows: polynomial phases are not the phase of `ζ`, and no subconvexity
  bound, approximate functional equation or density estimate is claimed.

## Adversarial revalidation: M1-WEYL-POLYNOMIAL-GENERAL

* The module is imported by `RiemannHypothesis.lean`,
  `lake build RiemannHypothesis.WeylPolynomialGeneral` succeeds, the file contains no `sorry`, and
  the build emits no warning for it.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the five main
  statements; the checks are in `scripts/audit.sh`.
* All five are pinned in `scripts/revalidation.lean` with `EquidistributedMod1` and `Irrational`
  written out in full, so neither side of the criterion can be weakened.
* The criterion is not vacuous in either direction, and both directions are needed: for
  `p = C √2 * X + C (1/2) * X^2` the *leading* coefficient is rational, so `M1-WEYL-POLYNOMIAL`
  does not apply, while the new criterion gives equidistribution from `Irrational √2`; for `p = X`
  every coefficient is rational and the fractional parts are all `0`, which the second direction
  proves is not equidistribution.
* The index restriction `j ≥ 1` is load-bearing on both sides: `p = C √2` is a constant
  polynomial, its coefficient of index `0` is irrational, and its values are constant, hence not
  equidistributed.
* No unproved `Prop` of this repository occurs among the hypotheses.
