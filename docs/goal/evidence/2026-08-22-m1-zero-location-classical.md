# M1-ZERO-LOCATION-CLASSICAL — the zero strip at exponent one

Date: 2026-08-22
Module: `RiemannHypothesis/ZeroLocationClassical.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `exists_zero_re_le_one_sub_classical` — there is `c > 0` with `Re s ≤ 1 - c/log|Im s|` for every
  zero of `ζ` with `|Im s| ≥ 3`.  This is the contrapositive of `RiemannHypothesis.zeroFreeRegion`
  (M1-ZERO-FREE-REGION).
* `exists_zero_mem_shrinking_strip_classical` — the two-sided bound
  `c/log|Im s| ≤ Re s ≤ 1 - c/log|Im s|`.  The lower bound is the reflection of the upper one in
  the critical line, via `riemannZeta_one_sub_eq_zero_of_mem_strip` (M0-SYMMETRY) after checking
  that a zero with `|Im s| ≥ 3` is not one of the trivial (real) zeros.
* `exists_zero_abs_re_sub_half_le_classical` — equivalently
  `|Re s - 1/2| ≤ 1/2 - c/log|Im s|`.

## Relation to M1-ZERO-LOCATION

`RiemannHypothesis/ZeroLocation.lean` proves the same three statements with the explicit but far
weaker margin `2^{-45}/(log|Im s|)^9`.  The present file keeps the shape and replaces the exponent
nine by the classical exponent one, so the excluded margin is larger at every height `|Im s| ≥ 3`
above the point where the two constants cross.  The earlier statements are retained unchanged;
they are explicit, whereas the constant here is not.

## Scope

* `c` is the ineffective constant of `RiemannHypothesis.zeroFreeRegion`; see the evidence file
  for M1-ZERO-FREE-REGION.
* The strip still has width tending to `1`, so this is not the Riemann Hypothesis and nothing of
  the kind is claimed.

## Gates

* `lake build RiemannHypothesis.ZeroLocationClassical` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`; the claims are pinned in `scripts/revalidation.lean`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-ZERO-LOCATION-CLASSICAL

A second pass, made against the compiled module rather than against this note.

* **Is it vacuous?**  No: the hypotheses are `riemannZeta s = 0` and `3 ≤ |Im s|`, both satisfied
  by the first nontrivial zero at height `14.13…`, and the conclusion is a strict narrowing of the
  critical strip.
* **Is the reflection step legitimate?**  It uses the repository's
  `riemannZeta_one_sub_eq_zero_of_mem_strip`, which needs `0 < Re s < 1`; that is supplied by
  `zero_of_nontrivial_mem_strip` once the zero is known not to be a trivial one, and a zero with
  `|Im s| ≥ 3` cannot be a trivial zero because the trivial zeros are real.
* **Does it depend on anything unproved?**  Only on `RiemannHypothesis.zeroFreeRegion` and on the
  symmetry row M0-SYMMETRY, both `DONE_STRONG` and both `sorry`-free.
* **Proof hygiene.**  No `sorry`, `axiom`, `native_decide` or `implemented_by`; `#print axioms` on
  each theorem returns exactly `propext`, `Classical.choice`, `Quot.sound` (checked by
  `scripts/audit.sh`).
* **What is *not* claimed.**  No effectivity, no improvement of the exponent beyond one, and
  nothing about the Riemann Hypothesis.
