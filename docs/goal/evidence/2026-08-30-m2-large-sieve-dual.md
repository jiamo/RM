# M2-LARGE-SIEVE-DUAL — the dual large sieve

Date: 2026-08-30
File: `RiemannHypothesis/LargeSieveDual.lean`

## Claim

* `sum_normSq_adjoint_le` — **the duality principle for a finite matrix**.  Let `φ : ι → κ → ℂ`
  with `ι`, `κ` indexed by finite sets `s`, `u`, and let `0 ≤ C`.  If

      ∑_{i ∈ s} ‖∑_{n ∈ u} a n · φ i n‖² ≤ C ∑_{n ∈ u} ‖a n‖²

  for every coefficient vector `a`, then

      ∑_{n ∈ u} ‖∑_{i ∈ s} x i · conj (φ i n)‖² ≤ C ∑_{i ∈ s} ‖x i‖²

  for every `x`.

* `large_sieve_dual` — **the dual large sieve**: for points `t i` pairwise `δ`-separated modulo
  one, with `0 < δ ≤ 1/2`,

      ∑_{n < N} ‖∑_{i ∈ s} x i e(n t i)‖² ≤ (δ⁻¹ + π N) ∑_{i ∈ s} ‖x i‖².

* `large_sieve_dual_farey` — the same for the rationals in `[0, 1)` of denominator at most `Q`,
  with the constant `Q² + π N`.

## Proof

The duality principle is the statement that a matrix and its adjoint have the same norm, proved
here by an explicit computation rather than by invoking operator theory.  Put

    b n = ∑_i x i conj (φ i n),   S = ∑_n ‖b n‖²,   A i = ∑_n b n φ i n.

Exchanging the order of summation in `S = ∑_n conj (b n) · b n` gives the identity

    S = ∑_i x i · conj (A i),

so by the triangle inequality and the discrete Cauchy–Schwarz inequality

    S ≤ ∑_i ‖x i‖ ‖A i‖ ≤ √(∑_i ‖x i‖²) · √(∑_i ‖A i‖²).

The hypothesis, applied to the coefficient vector `b`, says `∑_i ‖A i‖² ≤ C S`, whence
`S ≤ √X · √(C S)` with `X = ∑_i ‖x i‖²`, and therefore `S² ≤ C S X`.  If `S = 0` the conclusion is
trivial, and otherwise dividing by `S` gives `S ≤ C X`.

The dual large sieve is this principle applied to `φ i n = e(n t i)`, whose adjoint entries are
the conjugates `conj (e(n t i))`; replacing `x` by its conjugate turns the conjugated sum back
into `∑_i x i e(n t i)` without changing either side, since conjugation preserves norms.  The
hypothesis of the duality principle is exactly
`RiemannHypothesis.LargeSieveGallagher.large_sieve_gallagher`, and the Farey version uses the
`Q⁻²`-separation of `M2-LARGE-SIEVE-FAREY`.

## Gates

* `lake build RiemannHypothesis.LargeSieveDual` — succeeds, with no warnings.
* `#print axioms` on every statement above: exactly `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry` in the file; the statements are pinned in `scripts/revalidation.lean` and their
  axioms checked in `scripts/audit.sh`.

## Open boundary

The constants come from `M2-LARGE-SIEVE-GALLAGHER` and carry the same factor `π` on the `N` term,
so they are not the sharp `N + δ⁻¹`.  The duality principle is proved for finite index sets only,
which is all that the large sieve needs.  As in the rows it depends on, everything here is about
exponential sums: no mean value theorem for `ζ` is improved, no zero-density estimate follows and
no zero is located.
