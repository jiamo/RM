# Conditioning: a tuple of residues is determined by its power sums

Date: 2026-09-07
Module: `RiemannHypothesis/VinogradovConditioning.lean`

## Why

`M3-VINOGRADOV-CONGRUENCING` proves the descent half of one efficient congruencing step: what
happens to the solutions whose `2s` variables all lie in *one* residue class modulo `q`.  Its
open boundary names the complementary half — the *conditioning* estimate, which controls the
solutions whose residues are spread out.  The algebraic core of that half is a classical fact
about symmetric functions, and it is what this row proves: modulo a prime `p > k`, a `k`-tuple
of residues is determined, up to the order of its entries, by its power sums of degrees
`1, …, k`.  Equivalently: a solution of the Vinogradov *congruence* system of degree `k` is a
rearrangement of any other solution with the same residue set, which is the statement behind the
`k!` in the conditioning bound.

## What is proved

* `entries`, `card_entries` — the multiset of entries of a tuple `x : Fin k → F`, of cardinality
  `k`.
* `natCast_mul_esymm_eq_sum` — **Newton's identities, evaluated at a tuple.**  For every `n`,
  `n · e_n(x) = (−1)^{n+1} ∑_{i + j = n, i < n} (−1)^i e_i(x) p_j(x)`, where `e_i` are the
  elementary symmetric functions of the multiset of entries and `p_j` the power sums.
* `esymm_eq_of_powerSum_eq` — **equal power sums force equal elementary symmetric functions.**
  Over a field in which `1, …, k` are invertible, if `∑ x_i^j = ∑ y_i^j` for `1 ≤ j ≤ k`, then
  `e_n(x) = e_n(y)` for every `n ≤ k`.
* `multiset_map_eq_of_powerSum_eq` — **hence the tuples are rearrangements.**  Under the same
  hypotheses, `x` and `y` have the same multiset of entries.
* `multiset_map_eq_of_powerSum_eq_zmod` — the arithmetic form, over `ZMod p` with `k < p`.
* `exists_perm_of_entries_eq` — two tuples with the same multiset of entries differ by a
  permutation of the indices.
* `card_congruenceSolutions_le_factorial` — **the conditioning bound.**  Modulo a prime `p > k`,
  at most `k !` tuples `x : Fin k → ZMod p` share a prescribed vector of power sums
  `∑ x_i^j = c j`, `1 ≤ j ≤ k`.

## Proof

`natCast_mul_esymm_eq_sum` is mathlib's `MvPolynomial.mul_esymm_eq_sum` pushed through the
evaluation homomorphism `MvPolynomial.aeval x`: `aeval` sends the elementary symmetric
polynomial to the `esymm` of the multiset of entries and the `psum` to the power sum, so the
polynomial identity becomes the numerical one.

`esymm_eq_of_powerSum_eq` is strong induction on `n`.  The case `n = 0` is `1 = 1`.  For `n > 0`
every term of the Newton sum has `i < n ≤ k`, so `e_i(x) = e_i(y)` by the inductive hypothesis,
and `1 ≤ j = n − i ≤ k`, so `p_j(x) = p_j(y)` by assumption; the two sums therefore agree, and
`n · e_n(x) = n · e_n(y)` cancels because `n` is invertible.  This is the only place the
characteristic hypothesis is used, and it is genuinely needed.

`multiset_map_eq_of_powerSum_eq` compares the monic polynomials `P = ∏ (X − x_i)` and
`Q = ∏ (X − y_i)`.  Both have degree `k` (`natDegree_multiset_prod_of_monic`).  Vieta
(`Multiset.prod_X_sub_C_coeff`) writes the coefficient of `X^j` of each as `±e_{k−j}`, and
`k − j ≤ k`, so the previous step gives `P = Q` coefficientwise; coefficients above the degree
vanish on both sides.  Finally `roots_multiset_prod_X_sub_C` recovers the multiset of entries
from the polynomial, so `entries x = P.roots = Q.roots = entries y`.

`multiset_map_eq_of_powerSum_eq_zmod` only has to check the characteristic hypothesis: for
`0 < m ≤ k < p`, `(m : ZMod p) = 0` would force `p ∣ m`, hence `p ≤ m`.

`exists_perm_of_entries_eq` is an induction on `k`.  For `k + 1`, the value `x 0` occurs in the
multiset of entries of `y`, say at the index `j`; composing `y` with the transposition `(0 j)`
puts it first, and since the multisets of entries agree and their heads now agree,
`Multiset.cons_inj_right` gives that the two tails have the same entries.  The permutation
produced by the inductive hypothesis on the tails is extended to `Fin (k + 1)` by
`Equiv.Perm.decomposeFin`, whose two evaluation lemmas are exactly the two cases of `Fin.cases`.

`card_congruenceSolutions_le_factorial` combines the two.  If no tuple has the prescribed power
sums the bound is trivial; otherwise fix one such `y`.  Every other solution `x` has
`entries x = entries y` by the previous theorem, hence `x = y ∘ e` for a permutation `e`, so the
solution set is contained in the image of `Equiv.Perm (Fin k)` under `e ↦ y ∘ e`, whose
cardinality is at most `Fintype.card (Equiv.Perm (Fin k)) = k !`.

## Scope

The conditioning bound is proved for one prescribed vector of power sums.  What is not proved is
its interleaving with the descent of `M3-VINOGRADOV-CONGRUENCING`.  The induction of efficient congruencing — two blocks of
variables, a tuned pair of parameters, a family of conditioned counts and a convexity argument
over it — remains unformalized, `VinogradovMeanValueBound` is still only a statement, and no
zero-free region follows.

## Adversarial review

* *Is the hypothesis on the characteristic really needed, or is the statement true anyway?*  It
  is needed.  Over `ZMod 2` with `k = 2`, the tuples `(0, 1)` and `(1, 0)` are rearrangements,
  but `(0, 0)` and `(1, 1)` have power sums `p_1 = 0, p_2 = 0` and `p_1 = 0, p_2 = 0`
  respectively — equal — while their multisets of entries differ.  The proof breaks exactly at
  `2 · e_2`, and the hypothesis `hchar` excludes this.
* *Is the conclusion vacuous for `k = 0`?*  For `k = 0` both multisets are empty and the
  statement is trivially true, but the theorem is stated for every `k` and has content for every
  `k ≥ 2`; the `k = 1` case is `x_0 = y_0`, which is the hypothesis at `j = 1`.
* *Does the ZMod form quietly assume the residues are distinct?*  No.  It applies to arbitrary
  tuples, including repeated residues, and concludes equality of multisets — the stronger
  statement.  Distinctness is what the counting step will use it for, not what it needs.
* *Is `natCast_mul_esymm_eq_sum` a restatement of a mathlib lemma with no content?*  It is
  mathlib's Newton identity transported along `aeval`; the transport is the content, since the
  induction needs the identity for the multiset of entries of a concrete tuple, not for the
  symmetric polynomials.
* *Is the `k !` bound vacuous because the solution set is empty?*  No.  The constant tuple
  `x i = a` has power sums `k a^j`, so for that vector of prescribed power sums the set is
  non-empty, and for `k = 1` it is a single point, matching `1! = 1`.  The bound is also sharp:
  for `k` distinct residues, all `k !` orderings are solutions with the same power sums.
* *Axioms.*  `#print axioms` on `esymm_eq_of_powerSum_eq`, `multiset_map_eq_of_powerSum_eq` and
  `multiset_map_eq_of_powerSum_eq_zmod`, `exists_perm_of_entries_eq` and
  `card_congruenceSolutions_le_factorial` gives exactly `propext`, `Classical.choice`,
  `Quot.sound`.
