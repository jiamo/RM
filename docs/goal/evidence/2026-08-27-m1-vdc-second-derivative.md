# M1-VDC-SECOND-DERIVATIVE — the second-derivative test for exponential *sums*

Date: 2026-08-27
File: `RiemannHypothesis/VanDerCorputSums.lean`

## Claim

Write `e(θ) = exp(2πiθ)` (`e2pi`), and let `g = f'` on `[a, a + L]`.

* **free separation** (`norm_sum_e2pi_le_of_grow`) — if `r > 0`, `λ > 0`, `f` has derivative `g`
  on `[a, a+L]` and `g` increases at speed at least `r`, i.e.
  `r (y − x) ≤ g y − g x` for `x ≤ y` in the interval, then

      ‖∑_{j < L} e(f(a+j))‖ ≤ 2 (V + 2) ((1 + 2/λ) + (2λ/r + 1)),   V = g(a+L) − g(a);

* **balanced choice** (`norm_sum_e2pi_le_of_grow_sqrt`) — taking `λ = √r / 2`, legitimate for
  `0 < r ≤ 1`,

      ‖∑_{j < L} e(f(a+j))‖ ≤ 2 (V + 2) (2 + 5/√r);

* **the second-derivative test** (`norm_sum_e2pi_le_of_deriv_two`) — if in addition `g` has a
  derivative `g'` with `0 < r ≤ g' ≤ R` on `[a, a+L]` and `r ≤ 1`, then

      ‖∑_{j < L} e(f(a+j))‖ ≤ 2 (R L + 2) (2 + 5/√r).

  For `R` comparable to `r` this is the classical `≪ L √r + 1/√r`, the exponent pair `(1/2, 1/2)`;

* **decreasing derivative** (`norm_sum_e2pi_le_of_deriv_two_neg`) — the same conclusion when
  `−R ≤ g' ≤ −r < 0`, since replacing `f` by `−f` conjugates every term and leaves the norm of
  the sum unchanged (`e2pi_neg`);

* **worked instance** (`norm_sum_e2pi_logPhase_le`) — for the phase of `ζ`,
  `f(x) = −(t/2π) log x`, summed over the dyadic block `[N, 2N)`, with `0 < t ≤ 8πN²`,

      ‖∑_{j < N} e(f(N+j))‖ ≤ 2 (t/(2πN) + 2) (2 + 5/√(t/(8πN²))).

## Proof

The range is split according to the position of `g` relative to the integers.  The classification
map (`cls`) sends the index `j` to the pair `(⌊g(a+j) + λ⌋, [g(a+j) ≥ ⌊g(a+j)+λ⌋ + λ])`: for
`λ ≤ 1/2` the windows `[k − λ, k + λ)` (*bad*, `g` close to the integer `k`) and
`[k + λ, k + 1 − λ)` (*good*, `g` far from every integer) tile the line, and
`Finset.sum_fiberwise_of_maps_to` splits the sum along the fibres.

* Since `g` is monotone — it grows at speed at least `r > 0` — each fibre is a *contiguous block*
  of indices (`cls_eq_of_between`: if `i ≤ j ≤ m` and `i`, `m` have the same class, so does `j`).
  This is what allows the two block estimates to be applied at all.
* On a *good* fibre, `g` lies in `[k + λ, k + 1 − λ]` throughout the block, so Kusmin–Landau
  (`RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_sub_int`, the module
  `M1-KUSMIN-LANDAU` supplies) bounds the fibre sum by `1 + 2/λ`, uniformly in its length.
* On a *bad* fibre, the values of `g` at the endpoints differ by less than `2λ`, while they
  separate at speed at least `r` (`sample_gap`), so the block has fewer than `2λ/r + 1` indices,
  and the triangle inequality with `|e(·)| = 1` bounds its sum by that.
* Only classes with first coordinate between `⌊g a + λ⌋` and `⌊g(a+L) + λ⌋` occur, so there are at
  most `2 (V + 2)` classes, the factor `2` being the Boolean.

Multiplying the number of classes by the per-class bound gives the first statement.  The balanced
choice is the identity `(1 + 2/λ) + (2λ/r + 1) = 2 + 5/√r` at `λ = √r/2`.  For the
second-derivative form the mean value theorem turns `r ≤ g' ≤ R` into two-sided control of the
increments of `g`: the lower bound is the growth hypothesis, the upper bound gives `V ≤ R L`.
The worked instance computes the second derivative of `−(t/2π) log x` as `(t/2π)/x²`, which on
`[N, 2N]` lies between `t/(8πN²)` and `t/(2πN²)`; the hypothesis `t ≤ 8πN²` is exactly `r ≤ 1`.

## Why this row exists

The open boundaries of `M1-KUSMIN-LANDAU` and `M1-VAN-DER-CORPUT` both named the same gap: the
first-derivative test for sums assumes that `f'` is trapped between two consecutive integers on
the whole range, which fails as soon as `f'` varies by more than `1` — and for the phase of `ζ`
it varies a great deal.  Splitting a general range into admissible subranges is exactly what this
module does, and the result is the first bound in the repository for an exponential sum with a
genuinely varying derivative.

## Scope, and what is *not* claimed

* Nothing is claimed about `ζ` itself: no subconvexity bound, no approximate functional equation,
  no density estimate.  `norm_sum_e2pi_logPhase_le` bounds one dyadic block of the phase and is
  not summed over blocks; no bound for `ζ(1/2 + it)` is derived.
* The constants are not optimized: `2 (V + 2)(2 + 5/√r)` against the classical `≪ V √r + 1/√r`.
  In particular the `+ 2` and the factor `2` from the Boolean are not removed.
* The `A` process (Weyl differencing, `M1-WEYL-DIFFERENCING`) and the `B` process (Poisson
  summation) are not combined with this test, and the third-derivative test is not proved, so the
  exponent pair `(1/6, 2/3)` and the Weyl bound `ζ(1/2 + it) ≪ t^{1/6+ε}` remain out of reach.

## Adversarial revalidation: M1-VDC-SECOND-DERIVATIVE

* The module is imported by `RiemannHypothesis.lean`, `lake build
  RiemannHypothesis.VanDerCorputSums` succeeds, and the file contains no `sorry`.
* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `norm_fiber_sum_le`, `norm_sum_e2pi_le_of_grow`, `norm_sum_e2pi_le_of_grow_sqrt`,
  `norm_sum_e2pi_le_of_deriv_two`, `norm_sum_e2pi_le_of_deriv_two_neg` and
  `norm_sum_e2pi_logPhase_le`.
* The five public statements are pinned in `scripts/revalidation.lean`: the statement is written
  out there in full and the repository declaration supplies the proof term, so a weakening or a
  restatement with extra hypotheses stops that file from elaborating.
* The statements are not vacuous.  The hypotheses of `norm_sum_e2pi_le_of_deriv_two` are satisfied
  by `f(x) = r x²/2` on any interval, with `g' ≡ r = R`; the log phase instance exhibits a phase
  whose derivative varies without bound, precisely the case Kusmin–Landau alone cannot treat.
* The bound is not uniformly better than the trivial one, and is not claimed to be.  The trivial
  bound is `L`; the right-hand side of `norm_sum_e2pi_le_of_deriv_two` is of size `R L/√r + 1/√r`,
  which beats `L` only when `R/√r` is small — the classical regime of the second-derivative test,
  where `R` is comparable to `r` and `r` is small.  Outside it the statement is true but weaker
  than the triangle inequality.  No numerical claim of a saving for `ζ` is made in the module.
* An earlier draft of `norm_fiber_sum_le` and `norm_sum_e2pi_le_of_grow` carried the hypothesis
  `λ ≤ 1/2`; the finished proofs do not use it, so it was removed rather than left in place.
* The statements are unconditional: no unproved `Prop` of this repository occurs as a hypothesis,
  so `docs/goal/conditional-theorems.txt` gains no new entry from this module.
