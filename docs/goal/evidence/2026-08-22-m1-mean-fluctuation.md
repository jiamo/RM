# M1-MEAN-FLUCTUATION — from the mean value to the fluctuation of `|ζ|` on a line

Date: 2026-08-22
Module: `RiemannHypothesis/MeanFluctuation.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

A general real-analysis principle, and its specialization to the second moment of `ζ`:

* `frequently_gt_sub_of_avg_tendsto` — if `f` is interval integrable on every `[0, T]` and
  `(1/T) ∫₀ᵀ f → L`, then for every `ε > 0` one has `L - ε < f t` for arbitrarily large `t`
  (`∃ᶠ t in atTop`). Proof: otherwise `f ≤ L - ε` from some `t₀` on, so
  `∫₀ᵀ f ≤ ∫₀^{t₀} f + (T - t₀)(L - ε)`, whose average tends to `L - ε`, contradicting the
  hypothesis by comparison of limits.
* `frequently_lt_add_of_avg_tendsto` — the mirror statement `f t < L + ε`, obtained by
  applying the first one to `-f`.
* `continuous_normSq_riemannZeta_line` — for `σ > 1` the map `t ↦ |ζ(σ + i t)|²` is
  continuous (the line misses the pole `s = 1`), hence interval integrable.
* `frequently_normSq_riemannZeta_gt`, `frequently_normSq_riemannZeta_lt` — for `σ > 1` and
  every `ε > 0`, both `|ζ(σ + i t)|² > ζ(2σ) - ε` and `|ζ(σ + i t)|² < ζ(2σ) + ε` hold for
  arbitrarily large `t`.  In particular `|ζ(σ + i t)|²` cannot stay away from its mean value
  `ζ(2σ)` on either side.

## What is *not* proved

* No `limsup`/`liminf` value is computed: the true `limsup` of `|ζ(σ + i t)|` on the line
  (`∏_p (1 - p^{-σ})^{-1}` by Kronecker's theorem) is *not* claimed; only that the mean value
  is approached from above and from below.
* Nothing about the critical strip, where the second moment itself is not available here.
* No consequence for the zeroes of `ζ`: on the half-plane `σ > 1` there are none.

## Gates

* `lake build RiemannHypothesis.MeanFluctuation` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-MEAN-FLUCTUATION

Re-checked by pinning, not by reading: `scripts/revalidation.lean` writes out the general
principle with its exact hypotheses (interval integrability on every `[0, T]` and the
convergence of the averages) and both specializations to `ζ`, with the line written out
explicitly as `(σ : ℂ) + (t : ℂ) * I`, each discharged by the repository's declaration.

Hidden-assumption check: the general lemma needs `0 < ε` and the integrability hypothesis, and
both are used; nothing about the sign of `f` is assumed. Vacuity check: `∃ᶠ t in atTop` is a
genuine statement (it fails, for instance, for a function tending to `-∞`), the hypotheses are
satisfiable, and the specializations are applied at `σ > 1` where the mean value theorem of
`RiemannHypothesis/MeanSquare.lean` supplies the limit. Non-circularity: the only inputs are
that mean value theorem and Mathlib's differentiability of `ζ` away from `s = 1`.

Scope check: only the half-plane of absolute convergence, and only the fluctuation around the
mean — no `limsup` value and nothing about zeroes is claimed.
