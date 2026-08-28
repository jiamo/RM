# Evidence: the prime number theorem reduced to `ψ(x) ~ x` (2026-08-20)

Rows: `M1-PNT-REDUCTION` (new, `DONE_STRONG`), `M1-PNT` (still `TODO_READY`, narrowed).

## What is proved (without `sorry`)

`RiemannHypothesis/PrimeCounting.lean`:

* `tendsto_log_div_sqrt_atTop` : `log x / √x → 0`.
* `tendsto_psi_sub_theta_div_atTop` : `(ψ(x) - θ(x))/x → 0`.
* `chebyshev_theta_tendsto_of_psi` : `ψ(x)/x → 1` implies `θ(x)/x → 1`.
* `primeCounting_tendsto_of_chebyshev_theta` : `θ(x)/x → 1` implies
  `π⌊x⌋ / (x / log x) → 1`.
* `primeCounting_tendsto_of_chebyshev_psi` : `ψ(x)/x → 1` implies
  `π⌊x⌋ / (x / log x) → 1`, which is the exit criterion of `M1-PNT`.

## The argument

Both steps rest on facts that Mathlib already supplies.

* `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` : `|ψ(x) - θ(x)| ≤ 2 √x log x` for `x ≥ 1`.
  Dividing by `x` gives `|(ψ-θ)/x| ≤ 2 log x / √x`, which tends to `0` because
  `log =o[atTop] x^(1/2)`. Hence `θ/x = ψ/x - (ψ-θ)/x → 1 - 0 = 1`.
* `Chebyshev.primeCounting_sub_theta_div_log_isBigO` : Abel summation gives
  `π⌊x⌋ - θ(x)/log x = O(x/(log x)²)`. Multiplying by `log x / x` — which is what dividing
  by `x/log x` amounts to — turns the error into `O(1/log x) → 0`, and leaves
  `π⌊x⌋/(x/log x) = (π⌊x⌋ - θ(x)/log x)(log x/x) + θ(x)/x → 0 + 1 = 1`.

## Commands run

```
lake build RiemannHypothesis.PrimeCounting
bash scripts/audit.sh                       # OK
```

`#print axioms` for the three implications reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **The prime number theorem itself is not proved.** What is proved is an implication whose
  hypothesis, `ψ(x) ~ x`, is exactly as hard as the theorem. This row is bookkeeping of a
  genuine kind: it isolates the one analytic input still missing, and the elementary
  partial-summation steps around it are now machine-checked rather than asserted.
* Neither route to `ψ(x) ~ x` is available here: the explicit formula (`M1-EXPLICIT`) needs
  contour integration over vertical lines, and Newman's Tauberian argument needs a contour
  argument that is in neither Mathlib nor this repository. Mathlib does not contain the
  prime number theorem.
