# The congruencing step of Vinogradov's mean value theorem

Date: 2026-09-07
Module: `RiemannHypothesis/VinogradovCongruencing.lean`

## Why

`M3-VINOGRADOV-SYSTEM` fixed the counting object `J_{s,k}(X)` and proved its invariances, and
recorded as its open boundary that no part of an actual route to the mean value theorem was
formalized.  The first step of Wooley's efficient congruencing is a purely combinatorial lemma:
split the solutions along the residue classes of a modulus and descend to the same system in a
shorter box.  That step is what this row proves.

## What is proved

* `sum_affine_pow_eq` — the binomial expansion `∑ (r + q u_i)^j = ∑_{m ≤ j} C(j,m) r^{j−m} q^m ∑
  u_i^m`, in `ℕ`, with no subtraction.
* `vinogradovEq_of_affine` — **the descent.**  If `(r + q·u, r + q·v)` solves the Vinogradov
  system of degree `k` and `q ≥ 1`, then `(u, v)` solves it.
* `residuePair`, `profileCount`, `vinogradovCount_eq_sum_fiber` — **the decomposition.**
  `J_{s,k}(X)` is the sum, over the pairs of residue profiles modulo `q`, of the number of
  solutions with those residues.
* `congruentCount`, `congruentCount_le` — **the congruencing lemma.**  The solutions whose `2s`
  variables all lie in one class modulo `q` number at most `J_{s,k}(X/q + 1)`.
* `diagonalClassCount_le` — summed over the `q` classes: at most `q · J_{s,k}(X/q + 1)`.
* `diagonalClassCount_le_pow` — the iterated form, at the modulus `p^m`.
* `diagonalClassCount`, `diagonalClassCount_le_sum`, `diagonalClassCount_le'` — the same bound
  for the whole diagonal profile (the solutions whose variables merely *share* a residue).

## Proof

The descent is an induction on the degree.  For `j ≤ k`, the equation `∑ (r + q u_i)^j = ∑ (r +
q v_i)^j` expands, by `sum_affine_pow_eq`, into a `ℕ`-linear combination of the equalities
`∑ u_i^m = ∑ v_i^m` for `m ≤ j`.  The terms with `m < j` are equal by the inductive hypothesis
(the case `m = 0` is `s = s`), so they cancel — in `ℕ`, by `Nat.add_left_cancel`, with no
subtraction anywhere — and what is left is `q^j ∑ u_i^j = q^j ∑ v_i^j`, whence the claim since
`q^j > 0`.  This is exactly the point at which the translation invariance of the Vinogradov
system is used: an arbitrary system of equations does not survive the substitution.

The congruencing lemma is then the map `x_i ↦ x_i / q + 1`.  For a solution all of whose
variables are congruent to `r` modulo `q`, `x_i = r + q (x_i / q)`, so the descent applies and
the reduced tuples solve the same system in `[0, X/q]`; `vinogradovEq_translate` moves that box
to `[1, X/q + 1]`.  The map is injective on the class because the residue is fixed, so
`Finset.card_le_card_of_injOn` gives the bound.

## Scope

One congruencing step, not the induction.  Efficient congruencing runs the step with two
distinct blocks of variables and a tuned pair of parameters, tracks a whole family of
conditioned counts rather than the diagonal profile alone, and closes with a convexity argument
over that family.  The complementary half — that a `k`-tuple of *distinct* residues modulo a
prime `p > k` is determined up to permutation by its power sums, which is what bounds the
non-diagonal profiles — is not formalized here.  Vinogradov's mean value theorem therefore
remains unproved, `VinogradovMeanValueBound` is still only a statement, and no zero-free region
follows.

## Adversarial review

* *Is the descent vacuous?*  No: `vinogradovEq_of_affine` has content already for `q = 1`, where
  it is the converse of the translation invariance, and its hypothesis `0 < q` is used (for
  `q = 0` the conclusion is false, since all the shifted tuples are constant).
* *Is `congruentCount_le` trivially true because the left side is zero?*  No: taking `q = 1`
  makes `congruentCount k s X 1 0 = J_{s,k}(X)`, and the bound reads `J_{s,k}(X) ≤ J_{s,k}(X+1)`,
  which is the truth and is not vacuous.  The content of the lemma is the *shortening* of the
  box by the factor `q`.
* *Does the decomposition claim more than it proves?*  `vinogradovCount_eq_sum_fiber` is an
  identity, proved by `Finset.card_eq_sum_card_fiberwise`; it is the partition of the solution
  set, not an estimate.  `diagonalClassCount_le_sum` is an inequality, not an equality, because
  for `s = 0` the diagonal profile is a single point while the classes number `q`.
* *Axioms.*  `#print axioms` on the four pinned statements gives exactly `propext`,
  `Classical.choice`, `Quot.sound`.
