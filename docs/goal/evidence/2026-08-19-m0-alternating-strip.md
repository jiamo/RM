# M0-ALTERNATING-STRIP evidence

Task: identify `η` with the limit of the partial sums of the classical alternating
series on the whole right half-plane, and derive a form of the Riemann hypothesis
that mentions neither analytic continuation nor an unconditional sum.

Source identity: `RiemannHypothesis/Alternating.lean` (new file, imported by
`RiemannHypothesis.lean`).

Why this is not already in `RiemannHypothesis/Eta.lean`: there the alternating
series is identified with `η` only for `1 < re s`, where it converges absolutely
and Mathlib's `tsum` (an unconditional sum) is meaningful.  Inside the critical
strip the alternating series converges only conditionally, so its `tsum` is `0`
by convention and carries no information; the correct statement there is about
partial sums.

What is proved (all without `sorry`):

- `sum_alternating_eq_pairedSum_add_rem` : for every `N`,
  `∑_{n < N} (-1)^n/(n+1)^s = ∑_{j < N/2} pairedTerm j s + (N odd ? N^(-s) : 0)`,
  by induction on `N` with the two parities.
- `tendsto_rem_zero` : the leftover term has norm at most `N ^ (-re s)`, which
  tends to `0` for `0 < re s`.
- `tendsto_alternating_partialSum_dirichletEta` : for `0 < re s` the partial sums
  of the alternating series converge to `η(s)`; the paired partial sums converge
  because the paired series is absolutely convergent (`summable_pairedTerm`).
- `EtaLimitForm`, `eta_iff_eta_limit`, `zeta_iff_eta_limit` : the Riemann
  hypothesis is equivalent to: whenever the partial sums of
  `∑ (-1)^n/(n+1)^s` tend to `0` at a point of the critical strip, that point has
  real part `1/2`.

Commands run:

```bash
lake build
bash scripts/audit.sh
python3 scripts/goal_state.py validate
```

Observed results:

- `lake build`: zero errors; the only `sorry` in the repository is in
  `Challenge.lean`.
- `audit.sh`: OK; the new theorems (now listed in the script) depend on exactly
  `propext, Classical.choice, Quot.sound`.  The script's axiom check was made
  robust to the line wrapping of long `#print axioms` output.
- `validate`: OK.

Supported claim: `η` is the limit of the alternating partial sums on `0 < re s`,
and the Riemann hypothesis is equivalent to the elementary statement
`EtaLimitForm`.

Not proven: the Riemann hypothesis itself, or any partial result of
`RiemannHypothesis/Partial.lean`.
